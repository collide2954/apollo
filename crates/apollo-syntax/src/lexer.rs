use std::fmt;

use crate::span::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    Fn,
    Theorem,
    Enum,
    Struct,
    Let,
    TypeKw,
    Sigma,
    Path,
    Interval,
    Coe,
    HCom,
    VType,
    VIn,
    VProj,
    Unit,
    Void,
    Bool,
    Nat,
    True,
    False,
    Zero,
    Succ,
    Match,
    As,
    Many,
    Top,
    Bot,
    Ident(String),
    Int(u32),
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    LAngle,
    RAngle,
    Comma,
    Colon,
    ColonColon,
    Semicolon,
    Dot,
    DotDot,
    At,
    Pipe,
    Eq,
    Arrow,
    FatArrow,
    And,
    Or,
    Eof,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LexError {
    UnexpectedChar { ch: char, span: Span },
    InvalidInteger { text: String, span: Span },
    UnterminatedBlockComment { span: Span },
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedChar { ch, .. } => write!(f, "unexpected character '{ch}'"),
            Self::InvalidInteger { text, .. } => write!(f, "invalid integer literal '{text}'"),
            Self::UnterminatedBlockComment { .. } => f.write_str("unterminated block comment"),
        }
    }
}

impl std::error::Error for LexError {}

pub fn lex(source: &str) -> Result<Vec<Token>, LexError> {
    let mut lexer = Lexer::new(source);
    let mut tokens = Vec::new();
    loop {
        let token = lexer.next_token()?;
        let is_eof = token.kind == TokenKind::Eof;
        tokens.push(token);
        if is_eof {
            break;
        }
    }
    Ok(tokens)
}

struct Lexer<'a> {
    source: &'a str,
    rest: &'a str,
}

impl<'a> Lexer<'a> {
    const fn new(source: &'a str) -> Self {
        Self {
            source,
            rest: source,
        }
    }

    const fn pos(&self) -> usize {
        self.source.len() - self.rest.len()
    }

    fn peek(&self) -> Option<char> {
        self.rest.chars().next()
    }

    fn advance(&mut self) -> Option<char> {
        let mut chars = self.rest.chars();
        let ch = chars.next()?;
        self.rest = chars.as_str();
        Some(ch)
    }

    fn skip_trivia(&mut self) -> Result<(), LexError> {
        loop {
            self.rest = self.rest.trim_start();
            if let Some(after) = self.rest.strip_prefix("//") {
                self.rest = after.split_once('\n').map_or("", |(_, tail)| tail);
                continue;
            }
            if let Some(after) = self.rest.strip_prefix("/*") {
                let start = self.pos();
                if let Some((_, tail)) = after.split_once("*/") {
                    self.rest = tail;
                    continue;
                }
                self.rest = "";
                return Err(LexError::UnterminatedBlockComment {
                    span: Span::new(start, self.pos()),
                });
            }
            break;
        }
        Ok(())
    }

    fn next_token(&mut self) -> Result<Token, LexError> {
        self.skip_trivia()?;
        let start = self.pos();
        let Some(ch) = self.advance() else {
            return Ok(Token {
                kind: TokenKind::Eof,
                span: Span::new(start, start),
            });
        };

        let kind = match ch {
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            '<' => TokenKind::LAngle,
            '>' => TokenKind::RAngle,
            ',' => TokenKind::Comma,
            ':' if self.peek() == Some(':') => {
                let _ = self.advance();
                TokenKind::ColonColon
            }
            ':' => TokenKind::Colon,
            ';' => TokenKind::Semicolon,
            '.' if self.peek() == Some('.') => {
                let _ = self.advance();
                TokenKind::DotDot
            }
            '.' => TokenKind::Dot,
            '@' => TokenKind::At,
            '→' => TokenKind::Arrow,
            '⇒' => TokenKind::FatArrow,
            'ω' | '*' => TokenKind::Many,
            '∧' => TokenKind::And,
            '∨' => TokenKind::Or,
            '⊤' => TokenKind::Top,
            '⊥' => TokenKind::Bot,
            '-' if self.peek() == Some('>') => {
                let _ = self.advance();
                TokenKind::Arrow
            }
            '=' if self.peek() == Some('>') => {
                let _ = self.advance();
                TokenKind::FatArrow
            }
            '=' => TokenKind::Eq,
            '&' if self.peek() == Some('&') => {
                let _ = self.advance();
                TokenKind::And
            }
            '|' if self.peek() == Some('|') => {
                let _ = self.advance();
                TokenKind::Or
            }
            '|' => TokenKind::Pipe,
            c if c.is_ascii_digit() => self.lex_int(start)?,
            c if is_ident_start(c) => self.lex_ident(start),
            other => {
                return Err(LexError::UnexpectedChar {
                    ch: other,
                    span: Span::new(start, self.pos()),
                });
            }
        };

        Ok(Token {
            kind,
            span: Span::new(start, self.pos()),
        })
    }

    fn lex_int(&mut self, start: usize) -> Result<TokenKind, LexError> {
        let rest = self.rest.trim_start_matches(|ch: char| ch.is_ascii_digit());
        self.rest = rest;
        let end = self.pos();
        let text = &self.source[start..end];
        let value = text.parse::<u32>().map_err(|_| LexError::InvalidInteger {
            text: text.to_owned(),
            span: Span::new(start, end),
        })?;
        Ok(TokenKind::Int(value))
    }

    fn lex_ident(&mut self, start: usize) -> TokenKind {
        self.rest = self.rest.trim_start_matches(is_ident_continue);
        let end = self.pos();
        match &self.source[start..end] {
            "fn" => TokenKind::Fn,
            "theorem" => TokenKind::Theorem,
            "enum" => TokenKind::Enum,
            "struct" => TokenKind::Struct,
            "let" => TokenKind::Let,
            "Type" => TokenKind::TypeKw,
            "Sigma" => TokenKind::Sigma,
            "Path" => TokenKind::Path,
            "I" => TokenKind::Interval,
            "coe" => TokenKind::Coe,
            "hcom" => TokenKind::HCom,
            "V" => TokenKind::VType,
            "vin" => TokenKind::VIn,
            "vproj" => TokenKind::VProj,
            "Unit" => TokenKind::Unit,
            "Void" => TokenKind::Void,
            "Bool" => TokenKind::Bool,
            "Nat" => TokenKind::Nat,
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            "zero" => TokenKind::Zero,
            "succ" => TokenKind::Succ,
            "match" => TokenKind::Match,
            "as" => TokenKind::As,
            "many" => TokenKind::Many,
            "top" => TokenKind::Top,
            "bot" => TokenKind::Bot,
            ident => TokenKind::Ident(ident.to_owned()),
        }
    }
}

const fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

const fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

#[cfg(test)]
mod tests {
    use super::{LexError, TokenKind, lex};

    #[test]
    fn lexes_apollo_keywords_ascii_and_unicode_tokens() {
        let src = "// comment\nfn id(0 A: Type 0, 1 x: A) → A { /* block */ x }\n\
                   theorem t(ω y: I) -> Path(i => A, y, y) { <i> hcom(A, 0, 1, [i = 0 && top || bot => <j> coe(k => A, 0, 1, y @ j)], y.0); let z = * y; many ∧ ∨ ⊤ ⊥ ⇒ }";
        let tokens = lex(src);
        assert!(tokens.is_ok());
        if let Ok(list) = tokens {
            let kinds: Vec<TokenKind> = list.into_iter().map(|t| t.kind).collect();
            assert_eq!(kinds[0], TokenKind::Fn);
            assert!(kinds.contains(&TokenKind::Theorem));
            assert!(kinds.contains(&TokenKind::Let));
            assert!(kinds.contains(&TokenKind::TypeKw));
            assert!(kinds.contains(&TokenKind::Path));
            assert!(kinds.contains(&TokenKind::Interval));
            assert!(kinds.contains(&TokenKind::Coe));
            assert!(kinds.contains(&TokenKind::HCom));
            assert!(kinds.contains(&TokenKind::Arrow));
            assert!(kinds.contains(&TokenKind::FatArrow));
            assert!(kinds.contains(&TokenKind::Many));
            assert!(kinds.contains(&TokenKind::And));
            assert!(kinds.contains(&TokenKind::Or));
            assert!(kinds.contains(&TokenKind::Top));
            assert!(kinds.contains(&TokenKind::Bot));
            assert!(kinds.contains(&TokenKind::At));
            assert!(kinds.contains(&TokenKind::Dot));
            assert!(kinds.contains(&TokenKind::Semicolon));
            assert_eq!(kinds.last(), Some(&TokenKind::Eof));
        }

        let pipe_and_sigma = lex("Sigma(1 x: A, B) |1 x| x");
        assert!(pipe_and_sigma.is_ok());
        if let Ok(list) = pipe_and_sigma {
            let kinds: Vec<TokenKind> = list.into_iter().map(|t| t.kind).collect();
            assert_eq!(kinds[0], TokenKind::Sigma);
            assert!(kinds.contains(&TokenKind::Pipe));
        }

        let ind = lex("Unit Void Bool Nat true false zero succ match as");
        assert!(ind.is_ok());
        if let Ok(list) = ind {
            let kinds: Vec<TokenKind> = list.into_iter().map(|t| t.kind).collect();
            assert_eq!(
                kinds,
                vec![
                    TokenKind::Unit,
                    TokenKind::Void,
                    TokenKind::Bool,
                    TokenKind::Nat,
                    TokenKind::True,
                    TokenKind::False,
                    TokenKind::Zero,
                    TokenKind::Succ,
                    TokenKind::Match,
                    TokenKind::As,
                    TokenKind::Eof,
                ]
            );
        }
        let dots = lex("a.b .. c");
        assert!(dots.is_ok());
        if let Ok(list) = dots {
            let kinds: Vec<TokenKind> = list.into_iter().map(|t| t.kind).collect();
            assert_eq!(
                kinds,
                vec![
                    TokenKind::Ident("a".to_owned()),
                    TokenKind::Dot,
                    TokenKind::Ident("b".to_owned()),
                    TokenKind::DotDot,
                    TokenKind::Ident("c".to_owned()),
                    TokenKind::Eof,
                ]
            );
        }
    }

    #[test]
    fn reports_lexical_errors() {
        let bad_char = lex("fn $");
        assert!(matches!(
            bad_char,
            Err(LexError::UnexpectedChar { ch: '$', .. })
        ));
        if let Err(err) = bad_char {
            assert!(err.to_string().contains('$'));
        }

        let bad_int = lex("99999999999999999999");
        assert!(matches!(bad_int, Err(LexError::InvalidInteger { .. })));
        if let Err(err) = bad_int {
            assert!(err.to_string().contains("invalid integer"));
        }

        let unclosed = lex("/* never closed");
        assert!(matches!(
            unclosed,
            Err(LexError::UnterminatedBlockComment { .. })
        ));
        if let Err(err) = unclosed {
            assert!(err.to_string().contains("unterminated"));
        }

        assert!(matches!(
            lex("-x"),
            Err(LexError::UnexpectedChar { ch: '-', .. })
        ));
        assert!(matches!(
            lex("&x"),
            Err(LexError::UnexpectedChar { ch: '&', .. })
        ));
        assert!(matches!(
            lex("/x"),
            Err(LexError::UnexpectedChar { ch: '/', .. })
        ));
    }
}
