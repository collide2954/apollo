use crate::span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MultAst {
    Zero,
    One,
    Many,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    pub decls: Vec<Decl>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DeclKind {
    Fn,
    Theorem,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decl {
    pub kind: DeclKind,
    pub name: String,
    pub params: Vec<Param>,
    pub ret_ty: Expr,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub mult: MultAst,
    pub name: String,
    pub ty: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HComBranch {
    pub cof: CofExpr,
    pub dim_name: String,
    pub tube: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CofExpr {
    Top(Span),
    Bot(Span),
    Eq {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        span: Span,
    },
    And {
        lhs: Box<Self>,
        rhs: Box<Self>,
        span: Span,
    },
    Or {
        lhs: Box<Self>,
        rhs: Box<Self>,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    Universe(u32),
    Interval,
    DimZero,
    DimOne,
    Var(String),
    Pi {
        params: Vec<Param>,
        codomain: Box<Expr>,
    },
    Lam {
        params: Vec<(MultAst, String)>,
        body: Box<Expr>,
    },
    App {
        func: Box<Expr>,
        arg: Box<Expr>,
    },
    Sigma {
        mult: MultAst,
        name: String,
        first: Box<Expr>,
        second: Box<Expr>,
    },
    Pair {
        first: Box<Expr>,
        second: Box<Expr>,
    },
    Fst(Box<Expr>),
    Snd(Box<Expr>),
    Ann {
        term: Box<Expr>,
        ty: Box<Expr>,
    },
    Path {
        dim_name: String,
        family: Box<Expr>,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    PLam {
        dim_name: String,
        body: Box<Expr>,
    },
    PApp {
        path: Box<Expr>,
        dim: Box<Expr>,
    },
    Coe {
        dim_name: String,
        line: Box<Expr>,
        src: Box<Expr>,
        dst: Box<Expr>,
        term: Box<Expr>,
    },
    HCom {
        ty: Box<Expr>,
        src: Box<Expr>,
        dst: Box<Expr>,
        branches: Vec<HComBranch>,
        cap: Box<Expr>,
    },
    Let {
        mult: MultAst,
        name: String,
        ty: Box<Expr>,
        value: Box<Expr>,
        body: Box<Expr>,
    },
}
