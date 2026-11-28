use std::collections::HashMap;

use apollo_kernel::nbe::quote;
use apollo_kernel::{EvalError, InductiveId, Neutral, TermArena, TermId, Value};

use crate::linear::{Shape, shape};
use crate::proof::{Equation, cong, refl, sym, trans};
use crate::{AutoError, add_term};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Op {
    Leaf(TermId),
    App,
    Succ,
    Add,
    Ctor {
        id: InductiveId,
        ctor: u32,
        params: Vec<TermId>,
    },
}

#[derive(Debug, Clone)]
struct Node {
    op: Op,
    children: Vec<usize>,
    value: Value,
    ty: Value,
    fixed: Vec<Value>,
}

#[derive(Debug, Clone)]
pub enum Reason {
    Given(Box<Equation>),
    Congruence(usize, usize),
}

#[derive(Debug, Clone)]
struct Edge {
    to: usize,
    reason: Reason,
    forward: bool,
}

pub type TypeOf<'a> = &'a mut dyn FnMut(&mut TermArena, &Value) -> Result<Value, AutoError>;

#[derive(Debug)]
pub struct EGraph {
    depth: u32,
    nodes: Vec<Node>,
    memo: HashMap<(Op, Vec<usize>), usize>,
    parent: Vec<usize>,
    edges: Vec<Option<Edge>>,
}

impl EGraph {
    #[must_use]
    pub fn new(depth: u32) -> Self {
        Self {
            depth,
            nodes: Vec::new(),
            memo: HashMap::new(),
            parent: Vec::new(),
            edges: Vec::new(),
        }
    }

    #[must_use]
    pub fn value(&self, node: usize) -> &Value {
        &self.nodes[node].value
    }

    #[must_use]
    pub fn arithmetic(&self) -> Vec<Value> {
        self.nodes
            .iter()
            .filter(|n| matches!(n.op, Op::Succ | Op::Add))
            .map(|n| n.value.clone())
            .collect()
    }

    pub fn add(
        &mut self,
        arena: &mut TermArena,
        value: &Value,
        type_of: TypeOf<'_>,
    ) -> Result<usize, AutoError> {
        let (op, parts, fixed) = self.decompose(arena, value)?;
        let mut children = Vec::with_capacity(parts.len());
        for part in &parts {
            children.push(self.add(arena, part, &mut *type_of)?);
        }
        let key = (op.clone(), children.clone());
        if let Some(&existing) = self.memo.get(&key) {
            return Ok(existing);
        }
        let ty = type_of(arena, value)?;
        let id = self.nodes.len();
        self.nodes.push(Node {
            op,
            children,
            value: value.clone(),
            ty,
            fixed,
        });
        self.memo.insert(key, id);
        self.parent.push(id);
        self.edges.push(None);
        Ok(id)
    }

    fn decompose(
        &self,
        arena: &mut TermArena,
        value: &Value,
    ) -> Result<(Op, Vec<Value>, Vec<Value>), EvalError> {
        match shape(arena, self.depth, value) {
            Shape::Succ(pred) => return Ok((Op::Succ, vec![pred], Vec::new())),
            Shape::Add(lhs, rhs) => return Ok((Op::Add, vec![lhs, rhs], Vec::new())),
            Shape::Zero | Shape::Atom => {}
        }
        match value {
            Value::Neutral(neutral) => {
                if let Neutral::App { func, arg } = &**neutral {
                    return Ok((
                        Op::App,
                        vec![Value::Neutral(func.clone()), arg.clone()],
                        Vec::new(),
                    ));
                }
            }
            Value::Ctor {
                id,
                ctor,
                params,
                args,
            } => {
                let mut param_ids = Vec::with_capacity(params.len());
                for param in params {
                    param_ids.push(quote(arena, self.depth, param)?);
                }
                let op = Op::Ctor {
                    id: *id,
                    ctor: *ctor,
                    params: param_ids,
                };
                return Ok((op, args.clone(), params.clone()));
            }
            _ => {}
        }
        Ok((
            Op::Leaf(quote(arena, self.depth, value)?),
            Vec::new(),
            Vec::new(),
        ))
    }

    #[must_use]
    pub fn find(&self, node: usize) -> usize {
        let parent = self.parent[node];
        if parent == node {
            node
        } else {
            self.find(parent)
        }
    }

    pub fn merge(&mut self, a: usize, b: usize, reason: Reason) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return;
        }
        self.parent[ra] = rb;
        self.reroot(a);
        self.edges[a] = Some(Edge {
            to: b,
            reason,
            forward: true,
        });
    }

    fn reroot(&mut self, node: usize) {
        let mut cur = node;
        let mut incoming: Option<Edge> = None;
        loop {
            let next = self.edges[cur].take();
            self.edges[cur] = incoming;
            let Some(edge) = next else {
                break;
            };
            incoming = Some(Edge {
                to: cur,
                reason: edge.reason,
                forward: !edge.forward,
            });
            cur = edge.to;
        }
    }

    fn congruent(&self, a: usize, b: usize) -> bool {
        let (na, nb) = (&self.nodes[a], &self.nodes[b]);
        na.op == nb.op
            && na.children.len() == nb.children.len()
            && na
                .children
                .iter()
                .zip(&nb.children)
                .all(|(&x, &y)| self.find(x) == self.find(y))
    }

    pub fn close(&mut self) {
        for _ in 0..self.nodes.len() {
            let Some((a, b)) = self.pending() else {
                return;
            };
            self.merge(a, b, Reason::Congruence(a, b));
        }
    }

    fn pending(&self) -> Option<(usize, usize)> {
        (0..self.nodes.len())
            .flat_map(|a| (0..a).map(move |b| (a, b)))
            .find(|&(a, b)| self.find(a) != self.find(b) && self.congruent(a, b))
    }

    #[must_use]
    pub fn members(&self, node: usize) -> Vec<usize> {
        let root = self.find(node);
        (0..self.nodes.len())
            .filter(|&n| self.find(n) == root)
            .collect()
    }

    fn path_to_root(&self, node: usize) -> Vec<usize> {
        let mut path = vec![node];
        let mut cur = node;
        while let Some(edge) = &self.edges[cur] {
            cur = edge.to;
            path.push(cur);
        }
        path
    }

    pub fn explain(
        &self,
        arena: &mut TermArena,
        a: usize,
        b: usize,
    ) -> Result<Equation, EvalError> {
        let from_a = self.path_to_root(a);
        let from_b = self.path_to_root(b);
        let b_len = from_b.iter().take_while(|n| !from_a.contains(n)).count();
        let a_len = from_b
            .get(b_len)
            .and_then(|meet| from_a.iter().position(|n| n == meet))
            .unwrap_or(from_a.len());
        let mut steps = Vec::new();
        for edge in from_a[..a_len]
            .iter()
            .filter_map(|&n| self.edges[n].as_ref())
        {
            steps.push(self.edge_eq(arena, edge)?);
        }
        let mut back = Vec::new();
        for edge in from_b[..b_len]
            .iter()
            .filter_map(|&n| self.edges[n].as_ref())
        {
            let eq = self.edge_eq(arena, edge)?;
            back.push(sym(arena, &eq)?);
        }
        steps.extend(back.into_iter().rev());
        let node = &self.nodes[a];
        let start = refl(arena, node.ty.clone(), node.value.clone())?;
        steps
            .into_iter()
            .try_fold(start, |acc, next| trans(arena, &acc, &next))
    }

    fn edge_eq(&self, arena: &mut TermArena, edge: &Edge) -> Result<Equation, EvalError> {
        let eq = match &edge.reason {
            Reason::Given(eq) => (**eq).clone(),
            Reason::Congruence(x, y) => self.cong_eq(arena, *x, *y)?,
        };
        if edge.forward {
            Ok(eq)
        } else {
            sym(arena, &eq)
        }
    }

    fn cong_eq(&self, arena: &mut TermArena, a: usize, b: usize) -> Result<Equation, EvalError> {
        let (na, nb) = (&self.nodes[a], &self.nodes[b]);
        let mut args = Vec::with_capacity(na.children.len());
        for (&x, &y) in na.children.iter().zip(&nb.children) {
            args.push(self.explain(arena, x, y)?);
        }
        let ty = na.ty.clone();
        match &na.op {
            Op::App => cong(arena, ty, &[], &args, |t, _, xs| t.app(xs[0], xs[1])),
            Op::Succ => cong(arena, ty, &[], &args, |t, _, xs| t.succ(xs[0])),
            Op::Add => cong(arena, ty, &[], &args, |t, _, xs| add_term(t, xs[0], xs[1])),
            Op::Ctor { id, ctor, .. } => {
                let (id, ctor) = (*id, *ctor);
                cong(arena, ty, &na.fixed, &args, move |t, fixed, xs| {
                    t.ctor(id, ctor, fixed.to_vec(), xs.to_vec())
                })
            }
            Op::Leaf(_) => refl(arena, ty, na.value.clone()),
        }
    }
}
