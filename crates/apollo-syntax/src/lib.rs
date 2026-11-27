pub mod ast;
pub mod lexer;
pub mod parser;
pub mod span;

pub use ast::{
    CofExpr, Decl, DeclKind, Expr, ExprKind, HComBranch, MatchArm, Module, MultAst, Param, Pattern,
};
pub use lexer::{LexError, Token, TokenKind, lex};
pub use parser::{ParseError, parse_expr, parse_module};
pub use span::{LineCol, Span, line_col};

#[must_use]
pub const fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

#[cfg(test)]
mod tests {
    use super::version;

    #[test]
    fn reports_package_version() {
        assert_eq!(version(), env!("CARGO_PKG_VERSION"));
    }
}
