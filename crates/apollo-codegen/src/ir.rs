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
    Unit,
    Void,
    Bool,
    Nat,
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
            Self::Unit | Self::Void | Self::Bool | Self::Nat => {}
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

    #[must_use]
    pub fn is_copy(&self) -> bool {
        match self {
            Self::Unit | Self::Void | Self::Bool | Self::Nat => true,
            Self::Tuple(fst, snd) => fst.is_copy() && snd.is_copy(),
            Self::Named(_) | Self::Callable { .. } => false,
        }
    }

    pub fn write_to(&self, out: &mut String) {
        match self {
            Self::Named(name) => out.push_str(name),
            Self::Unit => out.push_str("()"),
            Self::Void => out.push_str("core::convert::Infallible"),
            Self::Bool => out.push_str("bool"),
            Self::Nat => out.push_str("u128"),
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
    Tt,
    BoolLit(bool),
    NatLit(u128),
    Succ(Box<Self>),
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
    VoidMatch(Box<Self>),
    UnitMatch {
        scrut: Box<Self>,
        body: Box<Self>,
    },
    BoolMatch {
        scrut: Box<Self>,
        on_true: Box<Self>,
        on_false: Box<Self>,
    },
    NatLoop {
        scrut: Box<Self>,
        acc_id: usize,
        acc_name: String,
        acc_ty: RustType,
        pred_id: usize,
        pred_name: String,
        base: Box<Self>,
        step: Box<Self>,
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
        let mut loop_captured = BTreeSet::new();
        let counts = count_uses(&self.body, &mut loop_captured);

        let mut clone_ids = BTreeSet::new();
        for param in &mut self.params {
            let uses = counts.get(&param.id).copied().unwrap_or(0);
            if uses == 0 {
                param.name = mark_unused(&param.name);
            } else if (uses > 1 || loop_captured.contains(&param.id))
                && !param.ty.is_callable()
                && !param.ty.is_copy()
            {
                param.ty.collect_type_params(&mut self.clone_bounds);
                let _ = clone_ids.insert(param.id);
            }
        }
        collect_inner_ownership(
            &mut self.body,
            &counts,
            &loop_captured,
            &mut self.clone_bounds,
            &mut clone_ids,
        );

        let mut seen = HashMap::new();
        insert_clones(
            &mut self.body,
            &counts,
            &clone_ids,
            &loop_captured,
            &mut seen,
        );

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

fn add_counts(dst: &mut HashMap<usize, usize>, src: &HashMap<usize, usize>) {
    for (&id, &count) in src {
        *dst.entry(id).or_insert(0) += count;
    }
}

fn max_counts(dst: &mut HashMap<usize, usize>, src: &HashMap<usize, usize>) {
    for (&id, &count) in src {
        let entry = dst.entry(id).or_insert(0);
        if count > *entry {
            *entry = count;
        }
    }
}

fn count_uses(expr: &RustExpr, loop_captured: &mut BTreeSet<usize>) -> HashMap<usize, usize> {
    let mut counts = HashMap::new();
    match expr {
        RustExpr::Local { id, .. } => {
            counts.insert(*id, 1);
        }
        RustExpr::Global(_) | RustExpr::Tt | RustExpr::BoolLit(_) | RustExpr::NatLit(_) => {}
        RustExpr::Succ(inner)
        | RustExpr::Clone(inner)
        | RustExpr::Field0(inner)
        | RustExpr::Field1(inner)
        | RustExpr::VoidMatch(inner)
        | RustExpr::Closure { body: inner, .. } => {
            return count_uses(inner, loop_captured);
        }
        RustExpr::Call { callee, args } => {
            add_counts(&mut counts, &count_uses(callee, loop_captured));
            for arg in args {
                add_counts(&mut counts, &count_uses(arg, loop_captured));
            }
        }
        RustExpr::Tuple(fst, snd)
        | RustExpr::UnitMatch {
            scrut: fst,
            body: snd,
        }
        | RustExpr::Let {
            value: fst,
            body: snd,
            ..
        } => {
            add_counts(&mut counts, &count_uses(fst, loop_captured));
            add_counts(&mut counts, &count_uses(snd, loop_captured));
        }
        RustExpr::BoolMatch {
            scrut,
            on_true,
            on_false,
        } => {
            add_counts(&mut counts, &count_uses(scrut, loop_captured));
            let mut branch_counts = count_uses(on_true, loop_captured);
            max_counts(&mut branch_counts, &count_uses(on_false, loop_captured));
            add_counts(&mut counts, &branch_counts);
        }
        RustExpr::NatLoop {
            scrut,
            acc_id,
            pred_id,
            base,
            step,
            ..
        } => {
            add_counts(&mut counts, &count_uses(scrut, loop_captured));
            add_counts(&mut counts, &count_uses(base, loop_captured));
            let step_counts = count_uses(step, loop_captured);
            for (&id, &cnt) in &step_counts {
                if id != *acc_id && id != *pred_id {
                    let _ = loop_captured.insert(id);
                }
                *counts.entry(id).or_insert(0) += cnt;
            }
        }
    }
    counts
}

fn collect_inner_ownership(
    expr: &mut RustExpr,
    counts: &HashMap<usize, usize>,
    loop_captured: &BTreeSet<usize>,
    clone_bounds: &mut BTreeSet<String>,
    clone_ids: &mut BTreeSet<usize>,
) {
    match expr {
        RustExpr::Local { .. }
        | RustExpr::Global(_)
        | RustExpr::Tt
        | RustExpr::BoolLit(_)
        | RustExpr::NatLit(_) => {}
        RustExpr::Succ(inner)
        | RustExpr::Clone(inner)
        | RustExpr::Field0(inner)
        | RustExpr::Field1(inner)
        | RustExpr::VoidMatch(inner) => {
            collect_inner_ownership(inner, counts, loop_captured, clone_bounds, clone_ids);
        }
        RustExpr::Call { callee, args } => {
            collect_inner_ownership(callee, counts, loop_captured, clone_bounds, clone_ids);
            for arg in args {
                collect_inner_ownership(arg, counts, loop_captured, clone_bounds, clone_ids);
            }
        }
        RustExpr::Closure { params, body } => {
            for (id, name) in params {
                if counts.get(id).copied().unwrap_or(0) == 0 {
                    *name = mark_unused(name);
                }
            }
            collect_inner_ownership(body, counts, loop_captured, clone_bounds, clone_ids);
        }
        RustExpr::Tuple(fst, snd)
        | RustExpr::UnitMatch {
            scrut: fst,
            body: snd,
        } => {
            collect_inner_ownership(fst, counts, loop_captured, clone_bounds, clone_ids);
            collect_inner_ownership(snd, counts, loop_captured, clone_bounds, clone_ids);
        }
        RustExpr::BoolMatch {
            scrut,
            on_true,
            on_false,
        } => {
            collect_inner_ownership(scrut, counts, loop_captured, clone_bounds, clone_ids);
            collect_inner_ownership(on_true, counts, loop_captured, clone_bounds, clone_ids);
            collect_inner_ownership(on_false, counts, loop_captured, clone_bounds, clone_ids);
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
            } else if (uses > 1 || loop_captured.contains(id)) && !ty.is_callable() && !ty.is_copy()
            {
                ty.collect_type_params(clone_bounds);
                let _ = clone_ids.insert(*id);
            }
            collect_inner_ownership(value, counts, loop_captured, clone_bounds, clone_ids);
            collect_inner_ownership(body, counts, loop_captured, clone_bounds, clone_ids);
        }
        RustExpr::NatLoop {
            scrut,
            acc_id,
            acc_ty,
            pred_id,
            pred_name,
            base,
            step,
            ..
        } => {
            if counts.get(pred_id).copied().unwrap_or(0) == 0 {
                *pred_name = mark_unused(pred_name);
            }
            let acc_uses = counts.get(acc_id).copied().unwrap_or(0);
            if (acc_uses > 1 || loop_captured.contains(acc_id))
                && !acc_ty.is_callable()
                && !acc_ty.is_copy()
            {
                acc_ty.collect_type_params(clone_bounds);
                let _ = clone_ids.insert(*acc_id);
            }
            collect_inner_ownership(scrut, counts, loop_captured, clone_bounds, clone_ids);
            collect_inner_ownership(base, counts, loop_captured, clone_bounds, clone_ids);
            collect_inner_ownership(step, counts, loop_captured, clone_bounds, clone_ids);
        }
    }
}

fn insert_clones(
    expr: &mut RustExpr,
    counts: &HashMap<usize, usize>,
    clone_ids: &BTreeSet<usize>,
    loop_captured: &BTreeSet<usize>,
    seen: &mut HashMap<usize, usize>,
) {
    match expr {
        RustExpr::Local { id, name } => {
            let id_val = *id;
            if clone_ids.contains(&id_val) {
                let entry = seen.entry(id_val).or_insert(0);
                *entry += 1;
                let total = counts.get(&id_val).copied().unwrap_or(1);
                if loop_captured.contains(&id_val) || *entry < total {
                    let inner = RustExpr::Local {
                        id: id_val,
                        name: name.clone(),
                    };
                    *expr = RustExpr::Clone(Box::new(inner));
                }
            }
        }
        RustExpr::Global(_) | RustExpr::Tt | RustExpr::BoolLit(_) | RustExpr::NatLit(_) => {}
        RustExpr::Succ(inner)
        | RustExpr::Clone(inner)
        | RustExpr::Field0(inner)
        | RustExpr::Field1(inner)
        | RustExpr::VoidMatch(inner)
        | RustExpr::Closure { body: inner, .. } => {
            insert_clones(inner, counts, clone_ids, loop_captured, seen);
        }
        RustExpr::Call { callee, args } => {
            insert_clones(callee, counts, clone_ids, loop_captured, seen);
            for arg in args {
                insert_clones(arg, counts, clone_ids, loop_captured, seen);
            }
        }
        RustExpr::Tuple(fst, snd)
        | RustExpr::UnitMatch {
            scrut: fst,
            body: snd,
        }
        | RustExpr::Let {
            value: fst,
            body: snd,
            ..
        } => {
            insert_clones(fst, counts, clone_ids, loop_captured, seen);
            insert_clones(snd, counts, clone_ids, loop_captured, seen);
        }
        RustExpr::BoolMatch {
            scrut,
            on_true,
            on_false,
        } => {
            insert_clones(scrut, counts, clone_ids, loop_captured, seen);
            let mut seen_true = seen.clone();
            let mut seen_false = seen.clone();
            insert_clones(on_true, counts, clone_ids, loop_captured, &mut seen_true);
            insert_clones(on_false, counts, clone_ids, loop_captured, &mut seen_false);
            max_counts(seen, &seen_true);
            max_counts(seen, &seen_false);
        }
        RustExpr::NatLoop {
            scrut, base, step, ..
        } => {
            insert_clones(scrut, counts, clone_ids, loop_captured, seen);
            insert_clones(base, counts, clone_ids, loop_captured, seen);
            insert_clones(step, counts, clone_ids, loop_captured, seen);
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
    match expr {
        RustExpr::Let {
            name,
            ty,
            value,
            body,
            ..
        } => {
            out.push_str("let ");
            out.push_str(name);
            if !ty.is_callable() {
                out.push_str(": ");
                ty.write_to(out);
            }
            out.push_str(" = ");
            write_inline_expr(value, depth, out);
            out.push_str(";\n");
            write_block_expr(body, depth, out);
        }
        RustExpr::NatLoop {
            scrut,
            acc_name,
            acc_ty,
            pred_name,
            base,
            step,
            ..
        } => {
            out.push_str("let mut ");
            out.push_str(acc_name);
            if !acc_ty.is_callable() {
                out.push_str(": ");
                acc_ty.write_to(out);
            }
            out.push_str(" = ");
            write_inline_expr(base, depth, out);
            out.push_str(";\n");
            write_indent(depth, out);
            out.push_str("for ");
            out.push_str(pred_name);
            out.push_str(" in 0..");
            write_atom_expr(scrut, depth, out);
            out.push_str(" {\n");
            write_indent(depth + 1, out);
            out.push_str(acc_name);
            out.push_str(" = ");
            write_inline_expr(step, depth + 1, out);
            out.push_str(";\n");
            write_indent(depth, out);
            out.push_str("}\n");
            write_indent(depth, out);
            out.push_str(acc_name);
            out.push('\n');
        }
        other => {
            write_inline_expr(other, depth, out);
            out.push('\n');
        }
    }
}

fn write_inline_expr(expr: &RustExpr, depth: usize, out: &mut String) {
    match expr {
        RustExpr::Local { name, .. } | RustExpr::Global(name) => out.push_str(name),
        RustExpr::Tt => out.push_str("()"),
        RustExpr::BoolLit(val) => out.push_str(if *val { "true" } else { "false" }),
        RustExpr::NatLit(val) => {
            let _ = write!(out, "{val}_u128");
        }
        RustExpr::Succ(inner) => {
            write_atom_expr(inner, depth, out);
            out.push_str(" + 1");
        }
        RustExpr::Clone(inner) => {
            write_atom_expr(inner, depth, out);
            out.push_str(".clone()");
        }
        RustExpr::Call { callee, args } => {
            write_atom_expr(callee, depth, out);
            out.push('(');
            for (idx, arg) in args.iter().enumerate() {
                if idx > 0 {
                    out.push_str(", ");
                }
                write_inline_expr(arg, depth, out);
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
            write_inline_expr(body, depth, out);
        }
        RustExpr::Tuple(fst, snd) => {
            out.push('(');
            write_inline_expr(fst, depth, out);
            out.push_str(", ");
            write_inline_expr(snd, depth, out);
            out.push(')');
        }
        RustExpr::Field0(inner) => {
            write_atom_expr(inner, depth, out);
            out.push_str(".0");
        }
        RustExpr::Field1(inner) => {
            write_atom_expr(inner, depth, out);
            out.push_str(".1");
        }
        RustExpr::VoidMatch(scrut) => {
            out.push_str("match ");
            write_inline_expr(scrut, depth, out);
            out.push_str(" {}");
        }
        RustExpr::UnitMatch { scrut, body } => {
            out.push_str("match ");
            write_inline_expr(scrut, depth, out);
            out.push_str(" { () => ");
            write_inline_expr(body, depth, out);
            out.push_str(" }");
        }
        RustExpr::BoolMatch {
            scrut,
            on_true,
            on_false,
        } => {
            out.push_str("if ");
            write_inline_expr(scrut, depth, out);
            out.push_str(" { ");
            write_inline_expr(on_true, depth, out);
            out.push_str(" } else { ");
            write_inline_expr(on_false, depth, out);
            out.push_str(" }");
        }
        RustExpr::Let { .. } | RustExpr::NatLoop { .. } => {
            out.push_str("{\n");
            write_block_expr(expr, depth + 1, out);
            write_indent(depth, out);
            out.push('}');
        }
    }
}

fn write_atom_expr(expr: &RustExpr, depth: usize, out: &mut String) {
    match expr {
        RustExpr::Closure { .. }
        | RustExpr::Succ(_)
        | RustExpr::VoidMatch(_)
        | RustExpr::UnitMatch { .. }
        | RustExpr::BoolMatch { .. } => {
            out.push('(');
            write_inline_expr(expr, depth, out);
            out.push(')');
        }
        other => write_inline_expr(other, depth, out),
    }
}
