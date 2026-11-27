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
    Data {
        name: String,
        args: Vec<Self>,
    },
    Boxed(Box<Self>),
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
            Self::Data { args, .. } => {
                for arg in args {
                    arg.collect_type_params(out);
                }
            }
            Self::Boxed(inner) => inner.collect_type_params(out),
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
            Self::Named(_) | Self::Data { .. } | Self::Boxed(_) | Self::Callable { .. } => false,
        }
    }

    pub fn write_to(&self, out: &mut String) {
        match self {
            Self::Named(name) => out.push_str(name),
            Self::Unit => out.push_str("()"),
            Self::Void => out.push_str("core::convert::Infallible"),
            Self::Bool => out.push_str("bool"),
            Self::Nat => out.push_str("u128"),
            Self::Data { name, args } => {
                out.push_str(name);
                if !args.is_empty() {
                    out.push('<');
                    for (idx, arg) in args.iter().enumerate() {
                        if idx > 0 {
                            out.push_str(", ");
                        }
                        arg.write_to(out);
                    }
                    out.push('>');
                }
            }
            Self::Boxed(inner) => {
                out.push_str("Box<");
                inner.write_to(out);
                out.push('>');
            }
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
pub struct RustStructField {
    pub name: String,
    pub ty: RustType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RustEnumVariant {
    pub name: String,
    pub fields: Vec<RustType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RustDataKind {
    Enum(Vec<RustEnumVariant>),
    Struct(Vec<RustStructField>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RustDataDef {
    pub name: String,
    pub type_params: Vec<String>,
    pub kind: RustDataKind,
}

impl RustDataDef {
    pub fn write_to(&self, out: &mut String) {
        out.push_str("#[derive(Clone)]\npub ");
        match &self.kind {
            RustDataKind::Enum(_) => out.push_str("enum "),
            RustDataKind::Struct(_) => out.push_str("struct "),
        }
        out.push_str(&self.name);
        if !self.type_params.is_empty() {
            out.push('<');
            for (idx, tp) in self.type_params.iter().enumerate() {
                if idx > 0 {
                    out.push_str(", ");
                }
                out.push_str(tp);
            }
            out.push('>');
        }
        out.push_str(" {\n");
        match &self.kind {
            RustDataKind::Enum(variants) => {
                for variant in variants {
                    out.push_str("    ");
                    out.push_str(&variant.name);
                    if !variant.fields.is_empty() {
                        out.push('(');
                        for (idx, fty) in variant.fields.iter().enumerate() {
                            if idx > 0 {
                                out.push_str(", ");
                            }
                            fty.write_to(out);
                        }
                        out.push(')');
                    }
                    out.push_str(",\n");
                }
            }
            RustDataKind::Struct(fields) => {
                for field in fields {
                    out.push_str("    pub ");
                    out.push_str(&field.name);
                    out.push_str(": ");
                    field.ty.write_to(out);
                    out.push_str(",\n");
                }
            }
        }
        out.push_str("}\n");
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RustPatBinder {
    pub id: usize,
    pub name: String,
    pub ty: RustType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RustMatchPat {
    Enum {
        enum_name: String,
        variant_name: String,
        binders: Vec<RustPatBinder>,
    },
    Struct {
        struct_name: String,
        fields: Vec<(String, RustPatBinder)>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RustMatchArm {
    pub pat: RustMatchPat,
    pub body: RustExpr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CaptureMode {
    ByValue,
    ByRefCallable,
    ByRefClone,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecCapture {
    pub id: usize,
    pub name: String,
    pub ty: RustType,
    pub mode: CaptureMode,
    pub arg_expr: RustExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RustRecArm {
    pub pat: RustMatchPat,
    pub rec_bindings: Vec<(usize, String, usize, String)>, // (ih_id, ih_name, field_id, field_name)
    pub body: RustExpr,
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
    BoxNew(Box<Self>),
    Deref(Box<Self>),
    EnumCtor {
        enum_name: String,
        variant_name: String,
        args: Vec<Self>,
    },
    StructInit {
        struct_name: String,
        fields: Vec<(String, Self)>,
    },
    DataMatch {
        scrut: Box<Self>,
        arms: Vec<RustMatchArm>,
    },
    RecDataMatch {
        helper_name: String,
        type_params: Vec<String>,
        clone_bounds: BTreeSet<String>,
        scrut_ty: RustType,
        ret_ty: RustType,
        captures: Vec<RecCapture>,
        scrut: Box<Self>,
        arms: Vec<RustRecArm>,
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
    pub uses_alloc: bool,
    pub data_defs: Vec<RustDataDef>,
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
        if self.uses_alloc {
            out.push_str("\nextern crate alloc;\nuse alloc::boxed::Box;\n");
        }
        for data_def in &self.data_defs {
            out.push('\n');
            data_def.write_to(&mut out);
        }
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
        *entry = (*entry).max(count);
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
        | RustExpr::BoxNew(inner)
        | RustExpr::Deref(inner)
        | RustExpr::Closure { body: inner, .. } => {
            return count_uses(inner, loop_captured);
        }
        RustExpr::Call { callee, args } => {
            add_counts(&mut counts, &count_uses(callee, loop_captured));
            for arg in args {
                add_counts(&mut counts, &count_uses(arg, loop_captured));
            }
        }
        RustExpr::EnumCtor { args, .. } => {
            for arg in args {
                add_counts(&mut counts, &count_uses(arg, loop_captured));
            }
        }
        RustExpr::StructInit { fields, .. } => {
            for (_, val) in fields {
                add_counts(&mut counts, &count_uses(val, loop_captured));
            }
        }
        RustExpr::DataMatch { scrut, arms } => {
            add_counts(&mut counts, &count_uses(scrut, loop_captured));
            let mut branch_counts = HashMap::new();
            for arm in arms {
                max_counts(&mut branch_counts, &count_uses(&arm.body, loop_captured));
            }
            add_counts(&mut counts, &branch_counts);
        }
        RustExpr::RecDataMatch {
            scrut,
            captures,
            arms,
            ..
        } => {
            count_rec_data_uses(scrut, captures, arms, loop_captured, &mut counts);
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
        | RustExpr::VoidMatch(inner)
        | RustExpr::BoxNew(inner)
        | RustExpr::Deref(inner) => {
            collect_inner_ownership(inner, counts, loop_captured, clone_bounds, clone_ids);
        }
        RustExpr::EnumCtor { .. }
        | RustExpr::StructInit { .. }
        | RustExpr::DataMatch { .. }
        | RustExpr::RecDataMatch { .. } => {
            collect_data_ownership(expr, counts, loop_captured, clone_bounds, clone_ids);
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
        | RustExpr::BoxNew(inner)
        | RustExpr::Deref(inner)
        | RustExpr::Closure { body: inner, .. } => {
            insert_clones(inner, counts, clone_ids, loop_captured, seen);
        }
        RustExpr::EnumCtor { .. }
        | RustExpr::StructInit { .. }
        | RustExpr::DataMatch { .. }
        | RustExpr::RecDataMatch { .. } => {
            insert_data_clones(expr, counts, clone_ids, loop_captured, seen);
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

fn count_rec_data_uses(
    scrut: &RustExpr,
    captures: &[RecCapture],
    arms: &[RustRecArm],
    loop_captured: &mut BTreeSet<usize>,
    counts: &mut HashMap<usize, usize>,
) {
    add_counts(counts, &count_uses(scrut, loop_captured));
    for cap in captures {
        *counts.entry(cap.id).or_insert(0) += 1;
    }
    let mut branch_counts = HashMap::new();
    for arm in arms {
        let mut arm_counts = count_uses(&arm.body, loop_captured);
        for (_, _, field_id, _) in &arm.rec_bindings {
            *arm_counts.entry(*field_id).or_insert(0) += 1;
        }
        max_counts(&mut branch_counts, &arm_counts);
    }
    for (id, cnt) in branch_counts {
        if !captures.iter().any(|c| c.id == id) {
            *counts.entry(id).or_insert(0) += cnt;
        }
    }
}

fn collect_data_ownership(
    expr: &mut RustExpr,
    counts: &HashMap<usize, usize>,
    loop_captured: &BTreeSet<usize>,
    clone_bounds: &mut BTreeSet<String>,
    clone_ids: &mut BTreeSet<usize>,
) {
    match expr {
        RustExpr::EnumCtor { args, .. } => {
            for arg in args {
                collect_inner_ownership(arg, counts, loop_captured, clone_bounds, clone_ids);
            }
        }
        RustExpr::StructInit { fields, .. } => {
            for (_, val) in fields {
                collect_inner_ownership(val, counts, loop_captured, clone_bounds, clone_ids);
            }
        }
        RustExpr::DataMatch { scrut, arms } => {
            collect_inner_ownership(scrut, counts, loop_captured, clone_bounds, clone_ids);
            for arm in arms {
                collect_pat_ownership(&mut arm.pat, counts, loop_captured, clone_bounds, clone_ids);
                collect_inner_ownership(
                    &mut arm.body,
                    counts,
                    loop_captured,
                    clone_bounds,
                    clone_ids,
                );
            }
        }
        RustExpr::RecDataMatch { .. } => {
            collect_rec_data_ownership(expr, counts, loop_captured, clone_bounds, clone_ids);
        }
        _ => {}
    }
}

fn insert_data_clones(
    expr: &mut RustExpr,
    counts: &HashMap<usize, usize>,
    clone_ids: &BTreeSet<usize>,
    loop_captured: &BTreeSet<usize>,
    seen: &mut HashMap<usize, usize>,
) {
    match expr {
        RustExpr::EnumCtor { args, .. } => {
            for arg in args {
                insert_clones(arg, counts, clone_ids, loop_captured, seen);
            }
        }
        RustExpr::StructInit { fields, .. } => {
            for (_, val) in fields {
                insert_clones(val, counts, clone_ids, loop_captured, seen);
            }
        }
        RustExpr::DataMatch { scrut, arms } => {
            insert_clones(scrut, counts, clone_ids, loop_captured, seen);
            let base_seen = seen.clone();
            for arm in arms {
                let mut seen_arm = base_seen.clone();
                insert_clones(
                    &mut arm.body,
                    counts,
                    clone_ids,
                    loop_captured,
                    &mut seen_arm,
                );
                max_counts(seen, &seen_arm);
            }
        }
        RustExpr::RecDataMatch {
            scrut,
            captures,
            arms,
            ..
        } => {
            insert_rec_data_clones(
                scrut,
                captures,
                arms,
                counts,
                clone_ids,
                loop_captured,
                seen,
            );
        }
        _ => {}
    }
}

fn collect_rec_data_ownership(
    expr: &mut RustExpr,
    counts: &HashMap<usize, usize>,
    loop_captured: &BTreeSet<usize>,
    clone_bounds: &mut BTreeSet<String>,
    clone_ids: &mut BTreeSet<usize>,
) {
    let RustExpr::RecDataMatch {
        scrut,
        captures,
        clone_bounds: rec_bounds,
        ret_ty,
        arms,
        ..
    } = expr
    else {
        return;
    };
    collect_inner_ownership(scrut, counts, loop_captured, clone_bounds, clone_ids);
    for cap in captures {
        if cap.mode == CaptureMode::ByRefClone {
            cap.ty.collect_type_params(clone_bounds);
            cap.ty.collect_type_params(rec_bounds);
        }
    }
    for arm in arms {
        collect_pat_ownership(&mut arm.pat, counts, loop_captured, rec_bounds, clone_ids);
        for (ih_id, ih_name, _, _) in &mut arm.rec_bindings {
            let uses = counts.get(ih_id).copied().unwrap_or(0);
            if uses == 0 {
                *ih_name = mark_unused(ih_name);
            } else if uses > 1 && !ret_ty.is_callable() && !ret_ty.is_copy() {
                ret_ty.collect_type_params(rec_bounds);
                let _ = clone_ids.insert(*ih_id);
            }
        }
        collect_inner_ownership(&mut arm.body, counts, loop_captured, rec_bounds, clone_ids);
    }
    for tp in rec_bounds.iter() {
        let _ = clone_bounds.insert(tp.clone());
    }
}

fn insert_rec_data_clones(
    scrut: &mut RustExpr,
    captures: &mut [RecCapture],
    arms: &mut [RustRecArm],
    counts: &HashMap<usize, usize>,
    clone_ids: &BTreeSet<usize>,
    loop_captured: &BTreeSet<usize>,
    seen: &mut HashMap<usize, usize>,
) {
    insert_clones(scrut, counts, clone_ids, loop_captured, seen);
    for cap in captures.iter_mut() {
        if cap.mode == CaptureMode::ByValue {
            insert_clones(&mut cap.arg_expr, counts, clone_ids, loop_captured, seen);
        }
    }
    let mut inner_clone_ids = clone_ids.clone();
    let mut inner_loop = loop_captured.clone();
    for cap in captures.iter() {
        if cap.mode == CaptureMode::ByRefClone {
            let _ = inner_clone_ids.insert(cap.id);
            let _ = inner_loop.insert(cap.id);
        }
    }
    for arm in arms {
        let mut seen_arm = HashMap::new();
        insert_clones(
            &mut arm.body,
            counts,
            &inner_clone_ids,
            &inner_loop,
            &mut seen_arm,
        );
    }
}

fn collect_pat_ownership(
    pat: &mut RustMatchPat,
    counts: &HashMap<usize, usize>,
    loop_captured: &BTreeSet<usize>,
    clone_bounds: &mut BTreeSet<String>,
    clone_ids: &mut BTreeSet<usize>,
) {
    let apply_binder =
        |b: &mut RustPatBinder, bounds: &mut BTreeSet<String>, cids: &mut BTreeSet<usize>| {
            let uses = counts.get(&b.id).copied().unwrap_or(0);
            if uses == 0 {
                b.name = mark_unused(&b.name);
            } else if (uses > 1 || loop_captured.contains(&b.id))
                && !b.ty.is_callable()
                && !b.ty.is_copy()
            {
                b.ty.collect_type_params(bounds);
                let _ = cids.insert(b.id);
            }
        };
    match pat {
        RustMatchPat::Enum { binders, .. } => {
            for b in binders {
                apply_binder(b, clone_bounds, clone_ids);
            }
        }
        RustMatchPat::Struct { fields, .. } => {
            for (_, b) in fields {
                apply_binder(b, clone_bounds, clone_ids);
            }
        }
    }
}

pub fn collect_local_ids(expr: &RustExpr, out: &mut BTreeSet<usize>) {
    let mut dummy = BTreeSet::new();
    let counts = count_uses(expr, &mut dummy);
    out.extend(counts.keys().copied());
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
        RustExpr::RecDataMatch { .. } => {
            write_rec_data_match(expr, depth, out);
        }
        other => {
            write_inline_expr(other, depth, out);
            out.push('\n');
        }
    }
}

fn write_match_pat(pat: &RustMatchPat, out: &mut String) {
    match pat {
        RustMatchPat::Enum {
            enum_name,
            variant_name,
            binders,
        } => {
            out.push_str(enum_name);
            out.push_str("::");
            out.push_str(variant_name);
            if !binders.is_empty() {
                out.push('(');
                for (idx, b) in binders.iter().enumerate() {
                    if idx > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&b.name);
                }
                out.push(')');
            }
        }
        RustMatchPat::Struct {
            struct_name,
            fields,
        } => {
            out.push_str(struct_name);
            out.push_str(" { ");
            for (idx, (fname, b)) in fields.iter().enumerate() {
                if idx > 0 {
                    out.push_str(", ");
                }
                out.push_str(fname);
                out.push_str(": ");
                out.push_str(&b.name);
            }
            out.push_str(" }");
        }
    }
}

fn write_rec_data_match(expr: &RustExpr, depth: usize, out: &mut String) {
    let RustExpr::RecDataMatch {
        helper_name,
        type_params,
        clone_bounds,
        scrut_ty,
        ret_ty,
        captures,
        scrut,
        arms,
    } = expr
    else {
        return;
    };
    out.push_str("fn ");
    out.push_str(helper_name);
    if !type_params.is_empty() {
        out.push('<');
        for (idx, tp) in type_params.iter().enumerate() {
            if idx > 0 {
                out.push_str(", ");
            }
            out.push_str(tp);
            if clone_bounds.contains(tp) {
                out.push_str(": Clone");
            }
        }
        out.push('>');
    }
    out.push_str("(scrut: ");
    scrut_ty.write_to(out);
    for cap in captures {
        out.push_str(", ");
        out.push_str(&cap.name);
        out.push_str(": ");
        if cap.mode != CaptureMode::ByValue {
            out.push('&');
        }
        cap.ty.write_to(out);
    }
    out.push_str(") -> ");
    ret_ty.write_to(out);
    out.push_str(" {\n");
    write_indent(depth + 1, out);
    out.push_str("match scrut {\n");
    for arm in arms {
        write_indent(depth + 2, out);
        write_match_pat(&arm.pat, out);
        out.push_str(" => ");
        if arm.rec_bindings.is_empty() {
            write_inline_expr(&arm.body, depth + 2, out);
            out.push_str(",\n");
        } else {
            out.push_str("{\n");
            for (_, ih_name, _, field_name) in &arm.rec_bindings {
                write_indent(depth + 3, out);
                out.push_str("let ");
                out.push_str(ih_name);
                if !ret_ty.is_callable() {
                    out.push_str(": ");
                    ret_ty.write_to(out);
                }
                out.push_str(" = ");
                out.push_str(helper_name);
                out.push_str("(*");
                out.push_str(field_name);
                for cap in captures {
                    out.push_str(", ");
                    out.push_str(&cap.name);
                }
                out.push_str(");\n");
            }
            write_block_expr(&arm.body, depth + 3, out);
            write_indent(depth + 2, out);
            out.push_str("},\n");
        }
    }
    write_indent(depth + 1, out);
    out.push_str("}\n");
    write_indent(depth, out);
    out.push_str("}\n");
    write_indent(depth, out);
    out.push_str(helper_name);
    out.push('(');
    write_inline_expr(scrut, depth, out);
    for cap in captures {
        out.push_str(", ");
        if cap.mode == CaptureMode::ByValue {
            write_inline_expr(&cap.arg_expr, depth, out);
        } else {
            out.push('&');
            out.push_str(&cap.name);
        }
    }
    out.push_str(")\n");
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
        RustExpr::Let { .. } | RustExpr::NatLoop { .. } | RustExpr::RecDataMatch { .. } => {
            out.push_str("{\n");
            write_block_expr(expr, depth + 1, out);
            write_indent(depth, out);
            out.push('}');
        }
        RustExpr::BoxNew(_)
        | RustExpr::Deref(_)
        | RustExpr::EnumCtor { .. }
        | RustExpr::StructInit { .. }
        | RustExpr::DataMatch { .. } => write_data_inline_expr(expr, depth, out),
    }
}

fn write_data_inline_expr(expr: &RustExpr, depth: usize, out: &mut String) {
    match expr {
        RustExpr::BoxNew(inner) => {
            out.push_str("Box::new(");
            write_inline_expr(inner, depth, out);
            out.push(')');
        }
        RustExpr::Deref(inner) => {
            out.push_str("(*");
            write_atom_expr(inner, depth, out);
            out.push(')');
        }
        RustExpr::EnumCtor {
            enum_name,
            variant_name,
            args,
        } => {
            out.push_str(enum_name);
            out.push_str("::");
            out.push_str(variant_name);
            if !args.is_empty() {
                out.push('(');
                for (idx, arg) in args.iter().enumerate() {
                    if idx > 0 {
                        out.push_str(", ");
                    }
                    write_inline_expr(arg, depth, out);
                }
                out.push(')');
            }
        }
        RustExpr::StructInit {
            struct_name,
            fields,
        } => {
            out.push_str(struct_name);
            out.push_str(" { ");
            for (idx, (fname, val)) in fields.iter().enumerate() {
                if idx > 0 {
                    out.push_str(", ");
                }
                out.push_str(fname);
                out.push_str(": ");
                write_inline_expr(val, depth, out);
            }
            out.push_str(" }");
        }
        RustExpr::DataMatch { scrut, arms } => {
            out.push_str("match ");
            write_inline_expr(scrut, depth, out);
            if arms.is_empty() {
                out.push_str(" {}");
            } else {
                out.push_str(" {\n");
                for arm in arms {
                    write_indent(depth + 1, out);
                    write_match_pat(&arm.pat, out);
                    out.push_str(" => ");
                    write_inline_expr(&arm.body, depth + 1, out);
                    out.push_str(",\n");
                }
                write_indent(depth, out);
                out.push('}');
            }
        }
        _ => {}
    }
}

fn write_atom_expr(expr: &RustExpr, depth: usize, out: &mut String) {
    match expr {
        RustExpr::Closure { .. }
        | RustExpr::Succ(_)
        | RustExpr::VoidMatch(_)
        | RustExpr::UnitMatch { .. }
        | RustExpr::BoolMatch { .. }
        | RustExpr::DataMatch { .. } => {
            out.push('(');
            write_inline_expr(expr, depth, out);
            out.push(')');
        }
        other => write_inline_expr(other, depth, out),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{FnKind, RustExpr, RustFn, RustParam, RustType};

    #[test]
    fn nat_loop_does_not_clone_callable_accumulator() {
        let callable_ty = RustType::Callable {
            kind: FnKind::Fn,
            params: vec![RustType::Nat],
            ret: Box::new(RustType::Nat),
        };
        let mut func = RustFn {
            name: "repeat_fn".to_owned(),
            type_params: Vec::new(),
            clone_bounds: BTreeSet::new(),
            params: vec![
                RustParam {
                    id: 0,
                    name: "n".to_owned(),
                    ty: RustType::Nat,
                },
                RustParam {
                    id: 1,
                    name: "f".to_owned(),
                    ty: callable_ty.clone(),
                },
            ],
            ret_ty: callable_ty.clone(),
            body: RustExpr::NatLoop {
                scrut: Box::new(RustExpr::Local {
                    id: 0,
                    name: "n".to_owned(),
                }),
                acc_id: 3,
                acc_name: "acc".to_owned(),
                acc_ty: callable_ty,
                pred_id: 2,
                pred_name: "k".to_owned(),
                base: Box::new(RustExpr::Local {
                    id: 1,
                    name: "f".to_owned(),
                }),
                step: Box::new(RustExpr::Closure {
                    params: vec![(4, "x".to_owned())],
                    body: Box::new(RustExpr::Call {
                        callee: Box::new(RustExpr::Local {
                            id: 3,
                            name: "acc".to_owned(),
                        }),
                        args: vec![RustExpr::Call {
                            callee: Box::new(RustExpr::Local {
                                id: 3,
                                name: "acc".to_owned(),
                            }),
                            args: vec![RustExpr::Local {
                                id: 4,
                                name: "x".to_owned(),
                            }],
                        }],
                    }),
                }),
            },
        };
        func.finalize_ownership();
        let mut out = String::new();
        func.write_to(&mut out);
        assert!(!out.contains(".clone()"));
    }
}
