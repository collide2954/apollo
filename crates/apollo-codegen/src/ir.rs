use std::collections::{BTreeSet, HashMap};
use std::fmt::Write;

use crate::escape::mark_unused;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FnKind {
    FnOnce,
    Fn,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RustType {
    Named(String),
    Tuple(Box<Self>, Box<Self>),
    Callable {
        kind: FnKind,
        params: Vec<Self>,
        ret: Box<Self>,
    },
}

impl RustType {
    pub fn collect_type_params(&self, out: &mut BTreeSet<String>) {
        match self {
            Self::Named(name) => {
                let _ = out.insert(name.clone());
            }
            Self::Tuple(fst, snd) => {
                fst.collect_type_params(out);
                snd.collect_type_params(out);
            }
            Self::Callable { params, ret, .. } => {
                for param in params {
                    param.collect_type_params(out);
                }
                ret.collect_type_params(out);
            }
        }
    }

    #[must_use]
    pub const fn is_callable(&self) -> bool {
        matches!(self, Self::Callable { .. })
    }

    pub fn write_to(&self, out: &mut String) {
        match self {
            Self::Named(name) => out.push_str(name),
            Self::Tuple(fst, snd) => {
                out.push('(');
                fst.write_to(out);
                out.push_str(", ");
                snd.write_to(out);
                out.push(')');
            }
            Self::Callable { kind, params, ret } => {
                let trait_name = match kind {
                    FnKind::FnOnce => "impl FnOnce(",
                    FnKind::Fn => "impl Fn(",
                };
                out.push_str(trait_name);
                for (idx, param) in params.iter().enumerate() {
                    if idx > 0 {
                        out.push_str(", ");
                    }
                    param.write_to(out);
                }
                out.push_str(") -> ");
                ret.write_to(out);
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RustParam {
    pub id: usize,
    pub name: String,
    pub ty: RustType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RustExpr {
    Local {
        id: usize,
        name: String,
    },
    Global(String),
    Clone(Box<Self>),
    Call {
        callee: Box<Self>,
        args: Vec<Self>,
    },
    Closure {
        params: Vec<(usize, String)>,
        body: Box<Self>,
    },
    Tuple(Box<Self>, Box<Self>),
    Field0(Box<Self>),
    Field1(Box<Self>),
    Let {
        id: usize,
        name: String,
        ty: RustType,
        value: Box<Self>,
        body: Box<Self>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RustFn {
    pub name: String,
    pub type_params: Vec<String>,
    pub clone_bounds: BTreeSet<String>,
    pub params: Vec<RustParam>,
    pub ret_ty: RustType,
    pub body: RustExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RustModule {
    pub functions: Vec<RustFn>,
}

impl RustFn {
    pub fn finalize_ownership(&mut self) {
        let mut counts = HashMap::new();
        count_uses(&self.body, &mut counts);

        let mut clone_ids = BTreeSet::new();
        for param in &mut self.params {
            let uses = counts.get(&param.id).copied().unwrap_or(0);
            if uses == 0 {
                param.name = mark_unused(&param.name);
            } else if uses > 1 && !param.ty.is_callable() {
                param.ty.collect_type_params(&mut self.clone_bounds);
                let _ = clone_ids.insert(param.id);
            }
        }
        collect_let_ownership(
            &mut self.body,
            &counts,
            &mut self.clone_bounds,
            &mut clone_ids,
        );

        let mut seen = HashMap::new();
        insert_clones(&mut self.body, &counts, &clone_ids, &mut seen);

        let mut used_type_params = BTreeSet::new();
        for param in &self.params {
            param.ty.collect_type_params(&mut used_type_params);
        }
        self.ret_ty.collect_type_params(&mut used_type_params);
        self.type_params.retain(|tp| used_type_params.contains(tp));
    }

    pub fn write_to(&self, out: &mut String) {
        let _ = write!(out, "pub fn {}", self.name);
        if !self.type_params.is_empty() {
            out.push('<');
            for (idx, tp) in self.type_params.iter().enumerate() {
                if idx > 0 {
                    out.push_str(", ");
                }
                out.push_str(tp);
                if self.clone_bounds.contains(tp) {
                    out.push_str(": Clone");
                }
            }
            out.push('>');
        }
        out.push('(');
        for (idx, param) in self.params.iter().enumerate() {
            if idx > 0 {
                out.push_str(", ");
            }
            out.push_str(&param.name);
            out.push_str(": ");
            param.ty.write_to(out);
        }
        out.push_str(") -> ");
        self.ret_ty.write_to(out);
        out.push_str(" {\n");
        write_block_expr(&self.body, 1, out);
        out.push_str("}\n");
    }
}

impl RustModule {
    #[must_use]
    pub fn render(&self) -> String {
        let mut out = String::from("#![no_std]\n#![forbid(unsafe_code)]\n");
        for func in &self.functions {
            out.push('\n');
            func.write_to(&mut out);
        }
        out
    }
}

fn count_uses(expr: &RustExpr, counts: &mut HashMap<usize, usize>) {
    match expr {
        RustExpr::Local { id, .. } => {
            *counts.entry(*id).or_insert(0) += 1;
        }
        RustExpr::Global(_) => {}
        RustExpr::Clone(inner) | RustExpr::Field0(inner) | RustExpr::Field1(inner) => {
            count_uses(inner, counts);
        }
        RustExpr::Call { callee, args } => {
            count_uses(callee, counts);
            for arg in args {
                count_uses(arg, counts);
            }
        }
        RustExpr::Closure { body, .. } => count_uses(body, counts),
        RustExpr::Tuple(fst, snd) => {
            count_uses(fst, counts);
            count_uses(snd, counts);
        }
        RustExpr::Let { value, body, .. } => {
            count_uses(value, counts);
            count_uses(body, counts);
        }
    }
}

fn collect_let_ownership(
    expr: &mut RustExpr,
    counts: &HashMap<usize, usize>,
    clone_bounds: &mut BTreeSet<String>,
    clone_ids: &mut BTreeSet<usize>,
) {
    match expr {
        RustExpr::Local { .. } | RustExpr::Global(_) => {}
        RustExpr::Clone(inner) | RustExpr::Field0(inner) | RustExpr::Field1(inner) => {
            collect_let_ownership(inner, counts, clone_bounds, clone_ids);
        }
        RustExpr::Call { callee, args } => {
            collect_let_ownership(callee, counts, clone_bounds, clone_ids);
            for arg in args {
                collect_let_ownership(arg, counts, clone_bounds, clone_ids);
            }
        }
        RustExpr::Closure { params, body } => {
            for (id, name) in params {
                if counts.get(id).copied().unwrap_or(0) == 0 {
                    *name = mark_unused(name);
                }
            }
            collect_let_ownership(body, counts, clone_bounds, clone_ids);
        }
        RustExpr::Tuple(fst, snd) => {
            collect_let_ownership(fst, counts, clone_bounds, clone_ids);
            collect_let_ownership(snd, counts, clone_bounds, clone_ids);
        }
        RustExpr::Let {
            id,
            name,
            ty,
            value,
            body,
        } => {
            let uses = counts.get(id).copied().unwrap_or(0);
            if uses == 0 {
                *name = mark_unused(name);
            } else if uses > 1 && !ty.is_callable() {
                ty.collect_type_params(clone_bounds);
                let _ = clone_ids.insert(*id);
            }
            collect_let_ownership(value, counts, clone_bounds, clone_ids);
            collect_let_ownership(body, counts, clone_bounds, clone_ids);
        }
    }
}

fn insert_clones(
    expr: &mut RustExpr,
    counts: &HashMap<usize, usize>,
    clone_ids: &BTreeSet<usize>,
    seen: &mut HashMap<usize, usize>,
) {
    match expr {
        RustExpr::Local { id, name } => {
            let id_val = *id;
            if clone_ids.contains(&id_val) {
                let entry = seen.entry(id_val).or_insert(0);
                *entry += 1;
                let total = counts.get(&id_val).copied().unwrap_or(1);
                if *entry < total {
                    let inner = RustExpr::Local {
                        id: id_val,
                        name: name.clone(),
                    };
                    *expr = RustExpr::Clone(Box::new(inner));
                }
            }
        }
        RustExpr::Global(_) => {}
        RustExpr::Clone(inner) | RustExpr::Field0(inner) | RustExpr::Field1(inner) => {
            insert_clones(inner, counts, clone_ids, seen);
        }
        RustExpr::Call { callee, args } => {
            insert_clones(callee, counts, clone_ids, seen);
            for arg in args {
                insert_clones(arg, counts, clone_ids, seen);
            }
        }
        RustExpr::Closure { body, .. } => insert_clones(body, counts, clone_ids, seen),
        RustExpr::Tuple(fst, snd) => {
            insert_clones(fst, counts, clone_ids, seen);
            insert_clones(snd, counts, clone_ids, seen);
        }
        RustExpr::Let { value, body, .. } => {
            insert_clones(value, counts, clone_ids, seen);
            insert_clones(body, counts, clone_ids, seen);
        }
    }
}

fn write_indent(depth: usize, out: &mut String) {
    for _ in 0..depth {
        out.push_str("    ");
    }
}

fn write_block_expr(expr: &RustExpr, depth: usize, out: &mut String) {
    write_indent(depth, out);
    if let RustExpr::Let {
        name,
        ty,
        value,
        body,
        ..
    } = expr
    {
        out.push_str("let ");
        out.push_str(name);
        if !ty.is_callable() {
            out.push_str(": ");
            ty.write_to(out);
        }
        out.push_str(" = ");
        write_inline_expr(value, out);
        out.push_str(";\n");
        write_block_expr(body, depth, out);
    } else {
        write_inline_expr(expr, out);
        out.push('\n');
    }
}

fn write_inline_expr(expr: &RustExpr, out: &mut String) {
    match expr {
        RustExpr::Local { name, .. } | RustExpr::Global(name) => out.push_str(name),
        RustExpr::Clone(inner) => {
            write_atom_expr(inner, out);
            out.push_str(".clone()");
        }
        RustExpr::Call { callee, args } => {
            write_atom_expr(callee, out);
            out.push('(');
            for (idx, arg) in args.iter().enumerate() {
                if idx > 0 {
                    out.push_str(", ");
                }
                write_inline_expr(arg, out);
            }
            out.push(')');
        }
        RustExpr::Closure { params, body } => {
            out.push_str("move |");
            for (idx, (_, name)) in params.iter().enumerate() {
                if idx > 0 {
                    out.push_str(", ");
                }
                out.push_str(name);
            }
            out.push_str("| ");
            write_inline_expr(body, out);
        }
        RustExpr::Tuple(fst, snd) => {
            out.push('(');
            write_inline_expr(fst, out);
            out.push_str(", ");
            write_inline_expr(snd, out);
            out.push(')');
        }
        RustExpr::Field0(inner) => {
            write_atom_expr(inner, out);
            out.push_str(".0");
        }
        RustExpr::Field1(inner) => {
            write_atom_expr(inner, out);
            out.push_str(".1");
        }
        RustExpr::Let { .. } => {
            out.push_str("{\n");
            write_block_expr(expr, 2, out);
            out.push_str("    }");
        }
    }
}

fn write_atom_expr(expr: &RustExpr, out: &mut String) {
    match expr {
        RustExpr::Closure { .. } => {
            out.push('(');
            write_inline_expr(expr, out);
            out.push(')');
        }
        other => write_inline_expr(other, out),
    }
}
