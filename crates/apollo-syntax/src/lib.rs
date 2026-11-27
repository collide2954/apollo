pub mod lexer;
pub mod span;

pub use lexer::{LexError, Token, TokenKind, lex};
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
