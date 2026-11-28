use std::fmt;

use crate::ast::{
    CofExpr, DataDecl, DataKind, Decl, DeclKind, Expr, ExprKind, HComBranch, MatchArm, Module,
    ModuleItem, MultAst, Param, Pattern, VariantDecl,
};
use crate::lexer::{LexError, Token, TokenKind, lex};
use crate::span::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseError {
    Lex(LexError),
    UnexpectedToken { expected: String, span: Span },
    InvalidDimension { value: u32, span: Span },
    InvalidProjection { value: u32, span: Span },
}

impl From<LexError> for ParseError {
    fn from(value: LexError) -> Self {
        Self::Lex(value)
    }
}

impl ParseError {
    #[must_use]
    pub const fn span(&self) -> Span {
        match self {
            Self::Lex(
                LexError::UnexpectedChar { span, .. }
                | LexError::InvalidInteger { span, .. }
                | LexError::UnterminatedBlockComment { span },
            )
            | Self::UnexpectedToken { span, .. }
            | Self::InvalidDimension { span, .. }
            | Self::InvalidProjection { span, .. } => *span,
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lex(err) => write!(f, "{err}"),
            Self::UnexpectedToken { expected, .. } => write!(f, "expected {expected}"),
            Self::InvalidDimension { value, .. } => {
                write!(f, "invalid interval endpoint {value}; expected 0 or 1")
            }
            Self::InvalidProjection { value, .. } => {
                write!(f, "invalid tuple projection .{value}; expected .0 or .1")
            }
        }
    }
}

impl std::error::Error for ParseError {}

pub fn parse_module(source: &str) -> Result<Module, ParseError> {
    let tokens = lex(source)?;
    let mut parser = Parser::new(&tokens);
    parser.parse_module()
}

pub fn parse_expr(source: &str) -> Result<Expr, ParseError> {
    let tokens = lex(source)?;
    let mut parser = Parser::new(&tokens);
    let expr = parser.parse_expr()?;
    parser.expect(&TokenKind::Eof, "end of input")?;
    Ok(expr)
}

struct Parser<'a> {
    tokens: &'a [Token],
    eof: Token,
    allow_struct_lit: bool,
}

impl<'a> Parser<'a> {
    fn new(tokens: &'a [Token]) -> Self {
        let eof = tokens.last().cloned().unwrap_or(Token {
            kind: TokenKind::Eof,
            span: Span::new(0, 0),
        });
        Self {
            tokens,
            eof,
            allow_struct_lit: true,
        }
    }

    fn parse_expr_no_struct(&mut self) -> Result<Expr, ParseError> {
        let prev = self.allow_struct_lit;
        self.allow_struct_lit = false;
        let res = self.parse_expr();
        self.allow_struct_lit = prev;
        res
    }

    fn peek(&self) -> &Token {
        self.tokens.first().unwrap_or(&self.eof)
    }

    const fn advance(&mut self) -> &Token {
        if let Some((first, rest)) = self.tokens.split_first() {
            self.tokens = rest;
            first
        } else {
            &self.eof
        }
    }

    fn check(&self, kind: &TokenKind) -> bool {
        &self.peek().kind == kind
    }

    fn expect(&mut self, expected: &TokenKind, label: &str) -> Result<Span, ParseError> {
        if self.check(expected) {
            Ok(self.advance().span)
        } else {
            Err(ParseError::UnexpectedToken {
                expected: label.to_owned(),
                span: self.peek().span,
            })
        }
    }

    fn expect_ident(&mut self, label: &str) -> Result<(String, Span), ParseError> {
        let token = self.peek().clone();
        if let TokenKind::Ident(name) = token.kind {
            let _ = self.advance();
            Ok((name, token.span))
        } else {
            Err(ParseError::UnexpectedToken {
                expected: label.to_owned(),
                span: token.span,
            })
        }
    }

    fn expect_int(&mut self, label: &str) -> Result<(u32, Span), ParseError> {
        let token = self.peek().clone();
        if let TokenKind::Int(val) = token.kind {
            let _ = self.advance();
            Ok((val, token.span))
        } else {
            Err(ParseError::UnexpectedToken {
                expected: label.to_owned(),
                span: token.span,
            })
        }
    }

    fn parse_module(&mut self) -> Result<Module, ParseError> {
        let mut items = Vec::new();
        while !self.check(&TokenKind::Eof) {
            items.push(self.parse_item()?);
        }
        Ok(Module { items })
    }

    fn parse_item(&mut self) -> Result<ModuleItem, ParseError> {
        match self.peek().kind {
            TokenKind::Fn | TokenKind::Theorem => Ok(ModuleItem::Decl(self.parse_decl()?)),
            TokenKind::Enum => Ok(ModuleItem::Data(self.parse_enum()?)),
            TokenKind::Struct => Ok(ModuleItem::Data(self.parse_struct()?)),
            _ => Err(ParseError::UnexpectedToken {
                expected: "'fn', 'theorem', 'enum', or 'struct'".to_owned(),
                span: self.peek().span,
            }),
        }
    }

    fn parse_opt_data_params(&mut self) -> Result<Vec<Param>, ParseError> {
        if self.check(&TokenKind::LParen) {
            let _ = self.advance();
            let params = self.parse_param_list()?;
            let _ = self.expect(&TokenKind::RParen, "')'")?;
            Ok(params)
        } else {
            Ok(Vec::new())
        }
    }

    fn parse_opt_universe_ann(&mut self) -> Result<Option<u32>, ParseError> {
        if self.check(&TokenKind::Colon) {
            let _ = self.advance();
            let _ = self.expect(&TokenKind::TypeKw, "'Type'")?;
            let (lvl, _) = self.expect_int("universe level")?;
            Ok(Some(lvl))
        } else {
            Ok(None)
        }
    }

    fn parse_enum(&mut self) -> Result<DataDecl, ParseError> {
        let start = self.expect(&TokenKind::Enum, "'enum'")?;
        let (name, _) = self.expect_ident("enum name")?;
        let params = self.parse_opt_data_params()?;
        let level = self.parse_opt_universe_ann()?;
        let _ = self.expect(&TokenKind::LBrace, "'{'")?;
        let mut variants = Vec::new();
        while !self.check(&TokenKind::RBrace) {
            let (vname, vstart) = self.expect_ident("variant name")?;
            let (fields, vend) = if self.check(&TokenKind::LParen) {
                let _ = self.advance();
                let fs = self.parse_param_list()?;
                let end = self.expect(&TokenKind::RParen, "')'")?;
                (fs, end)
            } else {
                (Vec::new(), vstart)
            };
            variants.push(VariantDecl {
                name: vname,
                fields,
                span: vstart.merge(vend),
            });
            if self.check(&TokenKind::Comma) {
                let _ = self.advance();
            } else {
                break;
            }
        }
        let end = self.expect(&TokenKind::RBrace, "'}'")?;
        Ok(DataDecl {
            kind: DataKind::Enum,
            name,
            params,
            level,
            variants,
            span: start.merge(end),
        })
    }

    fn parse_struct(&mut self) -> Result<DataDecl, ParseError> {
        let start = self.expect(&TokenKind::Struct, "'struct'")?;
        let (name, _) = self.expect_ident("struct name")?;
        let params = self.parse_opt_data_params()?;
        let level = self.parse_opt_universe_ann()?;
        let _ = self.expect(&TokenKind::LBrace, "'{'")?;
        let mut fields = Vec::new();
        while !self.check(&TokenKind::RBrace) {
            fields.push(self.parse_param()?);
            if self.check(&TokenKind::Comma) {
                let _ = self.advance();
            } else {
                break;
            }
        }
        let end = self.expect(&TokenKind::RBrace, "'}'")?;
        let span = start.merge(end);
        Ok(DataDecl {
            kind: DataKind::Struct,
            name: name.clone(),
            params,
            level,
            variants: vec![VariantDecl { name, fields, span }],
            span,
        })
    }

    fn parse_decl(&mut self) -> Result<Decl, ParseError> {
        let start = self.peek().span;
        let kind = match self.peek().kind {
            TokenKind::Fn => {
                let _ = self.advance();
                DeclKind::Fn
            }
            TokenKind::Theorem => {
                let _ = self.advance();
                DeclKind::Theorem
            }
            _ => {
                return Err(ParseError::UnexpectedToken {
                    expected: "'fn' or 'theorem'".to_owned(),
                    span: start,
                });
            }
        };
        let (name, _) = self.expect_ident("declaration name")?;
        let _ = self.expect(&TokenKind::LParen, "'('")?;
        let params = self.parse_param_list()?;
        let _ = self.expect(&TokenKind::RParen, "')'")?;
        let _ = self.expect(&TokenKind::Arrow, "'->'")?;
        let ret_ty = self.parse_expr_no_struct()?;
        let body = self.parse_block()?;
        let span = start.merge(body.span);
        Ok(Decl {
            kind,
            name,
            params,
            ret_ty,
            body,
            span,
        })
    }

    fn parse_param_list(&mut self) -> Result<Vec<Param>, ParseError> {
        let mut params = Vec::new();
        while !self.check(&TokenKind::RParen) {
            params.push(self.parse_param()?);
            if self.check(&TokenKind::Comma) {
                let _ = self.advance();
            } else {
                break;
            }
        }
        Ok(params)
    }

    fn parse_param(&mut self) -> Result<Param, ParseError> {
        let start = self.peek().span;
        let mult = self.parse_opt_mult();
        let (name, _) = self.expect_ident("parameter name")?;
        let _ = self.expect(&TokenKind::Colon, "':'")?;
        let ty = self.parse_expr()?;
        let span = start.merge(ty.span);
        Ok(Param {
            mult,
            name,
            ty,
            span,
        })
    }

    fn parse_opt_mult(&mut self) -> MultAst {
        match self.peek().kind {
            TokenKind::Int(0) => {
                let _ = self.advance();
                MultAst::Zero
            }
            TokenKind::Int(1) => {
                let _ = self.advance();
                MultAst::One
            }
            TokenKind::Many => {
                let _ = self.advance();
                MultAst::Many
            }
            _ => MultAst::Many,
        }
    }

    fn parse_block(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&TokenKind::LBrace, "'{'")?;
        let prev = self.allow_struct_lit;
        self.allow_struct_lit = true;
        let expr_res = self.parse_block_body();
        self.allow_struct_lit = prev;
        let expr = expr_res?;
        let end = self.expect(&TokenKind::RBrace, "'}'")?;
        Ok(Expr {
            kind: expr.kind,
            span: start.merge(end),
        })
    }

    fn parse_block_body(&mut self) -> Result<Expr, ParseError> {
        if self.check(&TokenKind::Let) {
            let start = self.advance().span;
            let mult = self.parse_opt_mult();
            let (name, _) = self.expect_ident("binding name")?;
            let _ = self.expect(&TokenKind::Colon, "':'")?;
            let ty = self.parse_expr()?;
            let _ = self.expect(&TokenKind::Eq, "'='")?;
            let value = self.parse_expr()?;
            let _ = self.expect(&TokenKind::Semicolon, "';'")?;
            let body = self.parse_block_body()?;
            let span = start.merge(body.span);
            return Ok(Expr {
                kind: ExprKind::Let {
                    mult,
                    name,
                    ty: Box::new(ty),
                    value: Box::new(value),
                    body: Box::new(body),
                },
                span,
            });
        }
        self.parse_expr()
    }

    fn is_pi_ahead(&self) -> bool {
        if !self.check(&TokenKind::LParen) {
            return false;
        }
        let mut depth = 0_usize;
        for (offset, token) in self.tokens.iter().enumerate() {
            match token.kind {
                TokenKind::LParen => depth += 1,
                TokenKind::RParen => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        return self
                            .tokens
                            .get(offset + 1)
                            .is_some_and(|next| next.kind == TokenKind::Arrow);
                    }
                }
                _ => {}
            }
        }
        false
    }

    fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        if self.is_pi_ahead() {
            let start = self.advance().span;
            let params = self.parse_param_list()?;
            let _ = self.expect(&TokenKind::RParen, "')'")?;
            let _ = self.expect(&TokenKind::Arrow, "'->'")?;
            let codomain = self.parse_expr()?;
            let span = start.merge(codomain.span);
            return Ok(Expr {
                kind: ExprKind::Pi {
                    params,
                    codomain: Box::new(codomain),
                },
                span,
            });
        }
        if self.check(&TokenKind::Pipe) {
            return self.parse_lambda();
        }
        if self.check(&TokenKind::LAngle) {
            return self.parse_plam();
        }
        self.parse_postfix()
    }

    fn parse_lambda(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&TokenKind::Pipe, "'|'")?;
        let mut params = Vec::new();
        while !self.check(&TokenKind::Pipe) {
            let mult = self.parse_opt_mult();
            let (name, _) = self.expect_ident("lambda parameter")?;
            params.push((mult, name));
            if self.check(&TokenKind::Comma) {
                let _ = self.advance();
            } else {
                break;
            }
        }
        let _ = self.expect(&TokenKind::Pipe, "'|'")?;
        let body = self.parse_expr()?;
        let span = start.merge(body.span);
        Ok(Expr {
            kind: ExprKind::Lam {
                params,
                body: Box::new(body),
            },
            span,
        })
    }

    fn parse_plam(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&TokenKind::LAngle, "'<'")?;
        let (dim_name, _) = self.expect_ident("dimension variable")?;
        let _ = self.expect(&TokenKind::RAngle, "'>'")?;
        let body = self.parse_expr()?;
        let span = start.merge(body.span);
        Ok(Expr {
            kind: ExprKind::PLam {
                dim_name,
                body: Box::new(body),
            },
            span,
        })
    }

    fn parse_postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_atom()?;
        loop {
            if self.check(&TokenKind::LParen) {
                let _ = self.advance();
                while !self.check(&TokenKind::RParen) {
                    let prev = self.allow_struct_lit;
                    self.allow_struct_lit = true;
                    let arg_res = self.parse_expr();
                    self.allow_struct_lit = prev;
                    let arg = arg_res?;
                    let span = expr.span.merge(arg.span);
                    expr = Expr {
                        kind: ExprKind::App {
                            func: Box::new(expr),
                            arg: Box::new(arg),
                        },
                        span,
                    };
                    if self.check(&TokenKind::Comma) {
                        let _ = self.advance();
                    } else {
                        break;
                    }
                }
                let end = self.expect(&TokenKind::RParen, "')'")?;
                expr.span = expr.span.merge(end);
                if self.allow_struct_lit
                    && self.check(&TokenKind::LBrace)
                    && let Some((type_name, type_args)) = split_var_app(&expr)
                {
                    let (fields, end_brace) = self.parse_struct_lit_fields()?;
                    expr = Expr {
                        kind: ExprKind::StructLit {
                            type_name,
                            type_args,
                            fields,
                        },
                        span: expr.span.merge(end_brace),
                    };
                }
            } else if self.check(&TokenKind::At) {
                let _ = self.advance();
                let dim = self.parse_atom()?;
                let span = expr.span.merge(dim.span);
                expr = Expr {
                    kind: ExprKind::PApp {
                        path: Box::new(expr),
                        dim: Box::new(dim),
                    },
                    span,
                };
            } else if self.check(&TokenKind::Dot) {
                let _ = self.advance();
                expr = self.parse_dot_projection(expr)?;
            } else {
                break;
            }
        }
        Ok(expr)
    }

    fn parse_dot_projection(&mut self, expr: Expr) -> Result<Expr, ParseError> {
        let token = self.peek().clone();
        match token.kind {
            TokenKind::Int(0) => {
                let _ = self.advance();
                Ok(Expr {
                    span: expr.span.merge(token.span),
                    kind: ExprKind::Fst(Box::new(expr)),
                })
            }
            TokenKind::Int(1) => {
                let _ = self.advance();
                Ok(Expr {
                    span: expr.span.merge(token.span),
                    kind: ExprKind::Snd(Box::new(expr)),
                })
            }
            TokenKind::Int(other) => Err(ParseError::InvalidProjection {
                value: other,
                span: token.span,
            }),
            TokenKind::Ident(name) => {
                let _ = self.advance();
                Ok(Expr {
                    span: expr.span.merge(token.span),
                    kind: ExprKind::Field {
                        target: Box::new(expr),
                        name,
                    },
                })
            }
            _ => Err(ParseError::UnexpectedToken {
                expected: "0, 1, or field name".to_owned(),
                span: token.span,
            }),
        }
    }

    fn parse_struct_lit_fields(&mut self) -> Result<(Vec<(String, Expr)>, Span), ParseError> {
        let _ = self.expect(&TokenKind::LBrace, "'{'")?;
        let mut fields = Vec::new();
        while !self.check(&TokenKind::RBrace) {
            let (fname, _) = self.expect_ident("field name")?;
            let _ = self.expect(&TokenKind::Colon, "':'")?;
            let prev = self.allow_struct_lit;
            self.allow_struct_lit = true;
            let val_res = self.parse_expr();
            self.allow_struct_lit = prev;
            fields.push((fname, val_res?));
            if self.check(&TokenKind::Comma) {
                let _ = self.advance();
            } else {
                break;
            }
        }
        let end = self.expect(&TokenKind::RBrace, "'}'")?;
        Ok((fields, end))
    }

    fn parse_ident_atom(&mut self, name: String, start: Span) -> Result<Expr, ParseError> {
        let _ = self.advance();
        if self.check(&TokenKind::ColonColon) {
            let _ = self.advance();
            let (ctor_name, ctor_span) = self.expect_ident("constructor name")?;
            let mut args = Vec::new();
            let end = if self.check(&TokenKind::LParen) {
                let _ = self.advance();
                while !self.check(&TokenKind::RParen) {
                    let prev = self.allow_struct_lit;
                    self.allow_struct_lit = true;
                    let arg_res = self.parse_expr();
                    self.allow_struct_lit = prev;
                    args.push(arg_res?);
                    if self.check(&TokenKind::Comma) {
                        let _ = self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RParen, "')'")?
            } else {
                ctor_span
            };
            Ok(Expr {
                kind: ExprKind::Ctor {
                    type_name: name,
                    ctor_name,
                    args,
                },
                span: start.merge(end),
            })
        } else if self.allow_struct_lit && self.check(&TokenKind::LBrace) {
            let (fields, end) = self.parse_struct_lit_fields()?;
            Ok(Expr {
                kind: ExprKind::StructLit {
                    type_name: name,
                    type_args: Vec::new(),
                    fields,
                },
                span: start.merge(end),
            })
        } else {
            Ok(Expr {
                kind: ExprKind::Var(name),
                span: start,
            })
        }
    }

    const fn single_token_expr(&mut self, kind: ExprKind, span: Span) -> Expr {
        let _ = self.advance();
        Expr { kind, span }
    }

    fn parse_atom(&mut self) -> Result<Expr, ParseError> {
        let token = self.peek().clone();
        match token.kind {
            TokenKind::TypeKw => {
                let _ = self.advance();
                let (level, end) = self.expect_int("universe level")?;
                Ok(Expr {
                    kind: ExprKind::Universe(level),
                    span: token.span.merge(end),
                })
            }
            TokenKind::Interval => Ok(self.single_token_expr(ExprKind::Interval, token.span)),
            TokenKind::Int(0) => Ok(self.single_token_expr(ExprKind::DimZero, token.span)),
            TokenKind::Int(1) => Ok(self.single_token_expr(ExprKind::DimOne, token.span)),
            TokenKind::Int(value) => Err(ParseError::InvalidDimension {
                value,
                span: token.span,
            }),
            TokenKind::Ident(name) => self.parse_ident_atom(name, token.span),
            TokenKind::Sigma => self.parse_sigma(),
            TokenKind::Path => self.parse_path(),
            TokenKind::Coe => self.parse_coe(),
            TokenKind::HCom => self.parse_hcom(),
            TokenKind::Unit => Ok(self.single_token_expr(ExprKind::Unit, token.span)),
            TokenKind::Void => Ok(self.single_token_expr(ExprKind::Void, token.span)),
            TokenKind::Bool => Ok(self.single_token_expr(ExprKind::Bool, token.span)),
            TokenKind::True => Ok(self.single_token_expr(ExprKind::True, token.span)),
            TokenKind::False => Ok(self.single_token_expr(ExprKind::False, token.span)),
            TokenKind::Nat => Ok(self.single_token_expr(ExprKind::Nat, token.span)),
            TokenKind::Zero => Ok(self.single_token_expr(ExprKind::Zero, token.span)),
            TokenKind::Succ => self.parse_succ(),
            TokenKind::Match => self.parse_match(),
            TokenKind::LBrace => self.parse_block(),
            TokenKind::LParen => self.parse_paren_expr(),
            _ => Err(ParseError::UnexpectedToken {
                expected: "expression".to_owned(),
                span: token.span,
            }),
        }
    }

    fn parse_sigma(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&TokenKind::Sigma, "'Sigma'")?;
        let _ = self.expect(&TokenKind::LParen, "'('")?;
        let mult = self.parse_opt_mult();
        let (name, _) = self.expect_ident("binder name")?;
        let _ = self.expect(&TokenKind::Colon, "':'")?;
        let first = self.parse_expr()?;
        let _ = self.expect(&TokenKind::Comma, "','")?;
        let second = self.parse_expr()?;
        let end = self.expect(&TokenKind::RParen, "')'")?;
        Ok(Expr {
            kind: ExprKind::Sigma {
                mult,
                name,
                first: Box::new(first),
                second: Box::new(second),
            },
            span: start.merge(end),
        })
    }

    fn parse_path(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&TokenKind::Path, "'Path'")?;
        let _ = self.expect(&TokenKind::LParen, "'('")?;
        let (dim_name, _) = self.expect_ident("dimension variable")?;
        let _ = self.expect(&TokenKind::FatArrow, "'=>'")?;
        let family = self.parse_expr()?;
        let _ = self.expect(&TokenKind::Comma, "','")?;
        let left = self.parse_expr()?;
        let _ = self.expect(&TokenKind::Comma, "','")?;
        let right = self.parse_expr()?;
        let end = self.expect(&TokenKind::RParen, "')'")?;
        Ok(Expr {
            kind: ExprKind::Path {
                dim_name,
                family: Box::new(family),
                left: Box::new(left),
                right: Box::new(right),
            },
            span: start.merge(end),
        })
    }

    fn parse_coe(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&TokenKind::Coe, "'coe'")?;
        let _ = self.expect(&TokenKind::LParen, "'('")?;
        let (dim_name, _) = self.expect_ident("dimension variable")?;
        let _ = self.expect(&TokenKind::FatArrow, "'=>'")?;
        let line = self.parse_expr()?;
        let _ = self.expect(&TokenKind::Comma, "','")?;
        let src = self.parse_expr()?;
        let _ = self.expect(&TokenKind::Comma, "','")?;
        let dst = self.parse_expr()?;
        let _ = self.expect(&TokenKind::Comma, "','")?;
        let term = self.parse_expr()?;
        let end = self.expect(&TokenKind::RParen, "')'")?;
        Ok(Expr {
            kind: ExprKind::Coe {
                dim_name,
                line: Box::new(line),
                src: Box::new(src),
                dst: Box::new(dst),
                term: Box::new(term),
            },
            span: start.merge(end),
        })
    }

    fn parse_hcom(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&TokenKind::HCom, "'hcom'")?;
        let _ = self.expect(&TokenKind::LParen, "'('")?;
        let ty = self.parse_expr()?;
        let _ = self.expect(&TokenKind::Comma, "','")?;
        let src = self.parse_expr()?;
        let _ = self.expect(&TokenKind::Comma, "','")?;
        let dst = self.parse_expr()?;
        let _ = self.expect(&TokenKind::Comma, "','")?;
        let _ = self.expect(&TokenKind::LBracket, "'['")?;
        let mut branches = Vec::new();
        while !self.check(&TokenKind::RBracket) {
            branches.push(self.parse_hcom_branch()?);
            if self.check(&TokenKind::Comma) {
                let _ = self.advance();
            } else {
                break;
            }
        }
        let _ = self.expect(&TokenKind::RBracket, "']'")?;
        let _ = self.expect(&TokenKind::Comma, "','")?;
        let cap = self.parse_expr()?;
        let end = self.expect(&TokenKind::RParen, "')'")?;
        Ok(Expr {
            kind: ExprKind::HCom {
                ty: Box::new(ty),
                src: Box::new(src),
                dst: Box::new(dst),
                branches,
                cap: Box::new(cap),
            },
            span: start.merge(end),
        })
    }

    fn parse_hcom_branch(&mut self) -> Result<HComBranch, ParseError> {
        let start = self.peek().span;
        let cof = self.parse_cof_or()?;
        let _ = self.expect(&TokenKind::FatArrow, "'=>'")?;
        let _ = self.expect(&TokenKind::LAngle, "'<'")?;
        let (dim_name, _) = self.expect_ident("tube dimension variable")?;
        let _ = self.expect(&TokenKind::RAngle, "'>'")?;
        let tube = self.parse_expr()?;
        let span = start.merge(tube.span);
        Ok(HComBranch {
            cof,
            dim_name,
            tube,
            span,
        })
    }

    fn parse_cof_or(&mut self) -> Result<CofExpr, ParseError> {
        let mut lhs = self.parse_cof_and()?;
        while self.check(&TokenKind::Or) {
            let _ = self.advance();
            let rhs = self.parse_cof_and()?;
            let span = cof_span(&lhs).merge(cof_span(&rhs));
            lhs = CofExpr::Or {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                span,
            };
        }
        Ok(lhs)
    }

    fn parse_cof_and(&mut self) -> Result<CofExpr, ParseError> {
        let mut lhs = self.parse_cof_atom()?;
        while self.check(&TokenKind::And) {
            let _ = self.advance();
            let rhs = self.parse_cof_atom()?;
            let span = cof_span(&lhs).merge(cof_span(&rhs));
            lhs = CofExpr::And {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                span,
            };
        }
        Ok(lhs)
    }

    fn parse_cof_atom(&mut self) -> Result<CofExpr, ParseError> {
        let token = self.peek().clone();
        match token.kind {
            TokenKind::Top => {
                let _ = self.advance();
                Ok(CofExpr::Top(token.span))
            }
            TokenKind::Bot => {
                let _ = self.advance();
                Ok(CofExpr::Bot(token.span))
            }
            TokenKind::LParen => {
                let _ = self.advance();
                let inner = self.parse_cof_or()?;
                let _ = self.expect(&TokenKind::RParen, "')'")?;
                Ok(inner)
            }
            _ => {
                let lhs = self.parse_atom()?;
                let _ = self.expect(&TokenKind::Eq, "'='")?;
                let rhs = self.parse_atom()?;
                let span = lhs.span.merge(rhs.span);
                Ok(CofExpr::Eq {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span,
                })
            }
        }
    }

    fn parse_succ(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&TokenKind::Succ, "'succ'")?;
        let _ = self.expect(&TokenKind::LParen, "'('")?;
        let pred = self.parse_expr()?;
        let end = self.expect(&TokenKind::RParen, "')'")?;
        Ok(Expr {
            kind: ExprKind::Succ(Box::new(pred)),
            span: start.merge(end),
        })
    }

    fn parse_match(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&TokenKind::Match, "'match'")?;
        let scrut = self.parse_expr_no_struct()?;
        let motive = if self.check(&TokenKind::As) {
            let _ = self.advance();
            let _ = self.expect(&TokenKind::Pipe, "'|'")?;
            let (name, _) = self.expect_ident("motive binder")?;
            let _ = self.expect(&TokenKind::Pipe, "'|'")?;
            let motive_ty = self.parse_expr_no_struct()?;
            Some((name, Box::new(motive_ty)))
        } else {
            None
        };
        let _ = self.expect(&TokenKind::LBrace, "'{'")?;
        let mut arms = Vec::new();
        while !self.check(&TokenKind::RBrace) {
            arms.push(self.parse_match_arm()?);
            if self.check(&TokenKind::Comma) {
                let _ = self.advance();
            } else {
                break;
            }
        }
        let end = self.expect(&TokenKind::RBrace, "'}'")?;
        Ok(Expr {
            kind: ExprKind::Match {
                scrut: Box::new(scrut),
                motive,
                arms,
            },
            span: start.merge(end),
        })
    }

    fn parse_match_arm(&mut self) -> Result<MatchArm, ParseError> {
        let pat = self.parse_pattern()?;
        let start = pattern_span(&pat);
        let _ = self.expect(&TokenKind::FatArrow, "'=>'")?;
        let body = self.parse_expr()?;
        let span = start.merge(body.span);
        Ok(MatchArm { pat, body, span })
    }

    fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        let token = self.peek().clone();
        match token.kind {
            TokenKind::LParen => {
                let start = self.advance().span;
                let end = self.expect(&TokenKind::RParen, "')'")?;
                Ok(Pattern::Unit(start.merge(end)))
            }
            TokenKind::True => {
                let _ = self.advance();
                Ok(Pattern::True(token.span))
            }
            TokenKind::False => {
                let _ = self.advance();
                Ok(Pattern::False(token.span))
            }
            TokenKind::Zero => {
                let _ = self.advance();
                Ok(Pattern::Zero(token.span))
            }
            TokenKind::Succ => {
                let start = self.advance().span;
                let _ = self.expect(&TokenKind::LParen, "'('")?;
                let (pred, _) = self.expect_ident("predecessor binder")?;
                let ih = if self.check(&TokenKind::Comma) {
                    let _ = self.advance();
                    let (ih_name, _) = self.expect_ident("induction hypothesis binder")?;
                    Some(ih_name)
                } else {
                    None
                };
                let end = self.expect(&TokenKind::RParen, "')'")?;
                Ok(Pattern::Succ {
                    pred,
                    ih,
                    span: start.merge(end),
                })
            }
            TokenKind::Ident(type_name) => self.parse_data_pattern(type_name, token.span),
            _ => Err(ParseError::UnexpectedToken {
                expected: "pattern ('()', 'true', 'false', 'zero', 'succ', or data pattern)"
                    .to_owned(),
                span: token.span,
            }),
        }
    }

    fn parse_data_pattern(
        &mut self,
        type_name: String,
        start: Span,
    ) -> Result<Pattern, ParseError> {
        let _ = self.advance();
        if self.check(&TokenKind::ColonColon) {
            let _ = self.advance();
            let (ctor_name, ctor_span) = self.expect_ident("constructor name")?;
            let mut binders = Vec::new();
            let end = if self.check(&TokenKind::LParen) {
                let _ = self.advance();
                while !self.check(&TokenKind::RParen) {
                    let (b, _) = self.expect_ident("pattern binder")?;
                    binders.push(b);
                    if self.check(&TokenKind::Comma) {
                        let _ = self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RParen, "')'")?
            } else {
                ctor_span
            };
            Ok(Pattern::Ctor {
                type_name,
                ctor_name,
                binders,
                span: start.merge(end),
            })
        } else if self.check(&TokenKind::LBrace) {
            let _ = self.advance();
            let mut fields = Vec::new();
            while !self.check(&TokenKind::RBrace) {
                let (fname, _) = self.expect_ident("field name")?;
                let binder = if self.check(&TokenKind::Colon) {
                    let _ = self.advance();
                    let (b, _) = self.expect_ident("field binder")?;
                    b
                } else {
                    fname.clone()
                };
                fields.push((fname, binder));
                if self.check(&TokenKind::Comma) {
                    let _ = self.advance();
                } else {
                    break;
                }
            }
            let end = self.expect(&TokenKind::RBrace, "'}'")?;
            Ok(Pattern::Struct {
                type_name,
                fields,
                span: start.merge(end),
            })
        } else {
            Err(ParseError::UnexpectedToken {
                expected: "'::' or '{' in pattern".to_owned(),
                span: self.peek().span,
            })
        }
    }

    fn parse_paren_expr(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&TokenKind::LParen, "'('")?;
        if self.check(&TokenKind::RParen) {
            let end = self.advance().span;
            return Ok(Expr {
                kind: ExprKind::Tt,
                span: start.merge(end),
            });
        }
        let prev = self.allow_struct_lit;
        self.allow_struct_lit = true;
        let res = self.parse_paren_inner(start);
        self.allow_struct_lit = prev;
        res
    }

    fn parse_paren_inner(&mut self, start: Span) -> Result<Expr, ParseError> {
        let first = self.parse_expr()?;
        if self.check(&TokenKind::Comma) {
            let _ = self.advance();
            let second = self.parse_expr()?;
            let end = self.expect(&TokenKind::RParen, "')'")?;
            Ok(Expr {
                kind: ExprKind::Pair {
                    first: Box::new(first),
                    second: Box::new(second),
                },
                span: start.merge(end),
            })
        } else if self.check(&TokenKind::Colon) {
            let _ = self.advance();
            let ty = self.parse_expr()?;
            let end = self.expect(&TokenKind::RParen, "')'")?;
            Ok(Expr {
                kind: ExprKind::Ann {
                    term: Box::new(first),
                    ty: Box::new(ty),
                },
                span: start.merge(end),
            })
        } else {
            let end = self.expect(&TokenKind::RParen, "')'")?;
            Ok(Expr {
                kind: first.kind,
                span: start.merge(end),
            })
        }
    }
}

fn split_var_app(expr: &Expr) -> Option<(String, Vec<Expr>)> {
    let mut cur = expr;
    let mut rev_args = Vec::new();
    while let ExprKind::App { func, arg } = &cur.kind {
        rev_args.push((**arg).clone());
        cur = func;
    }
    if let ExprKind::Var(name) = &cur.kind {
        rev_args.reverse();
        Some((name.clone(), rev_args))
    } else {
        None
    }
}

const fn pattern_span(pat: &Pattern) -> Span {
    match pat {
        Pattern::Unit(span)
        | Pattern::True(span)
        | Pattern::False(span)
        | Pattern::Zero(span)
        | Pattern::Succ { span, .. }
        | Pattern::Ctor { span, .. }
        | Pattern::Struct { span, .. } => *span,
    }
}

const fn cof_span(cof: &CofExpr) -> Span {
    match cof {
        CofExpr::Top(span)
        | CofExpr::Bot(span)
        | CofExpr::Eq { span, .. }
        | CofExpr::And { span, .. }
        | CofExpr::Or { span, .. } => *span,
    }
}

#[cfg(test)]
mod tests {
    use super::{ParseError, parse_expr, parse_module};
    use crate::ast::{DataKind, DeclKind, ExprKind, ModuleItem, MultAst};

    #[test]
    fn parses_full_apollo_module_with_cubical_theorems() {
        let src = r"
            fn id(0 A: Type 0, 1 x: A) -> A {
                x
            }

            fn dup(0 A: Type 0, ω x: A) -> Sigma(1 _: A, A) {
                (x, x)
            }

            theorem refl(0 A: Type 0, 0 x: A) -> Path(_ => A, x, x) {
                <i> x
            }

            theorem funext(
                0 A: Type 0,
                0 B: Type 0,
                0 f: (1 _: A) -> B,
                0 g: (1 _: A) -> B,
                0 h: (0 x: A) -> Path(_ => B, f(x), g(x)),
            ) -> Path(_ => (1 _: A) -> B, f, g) {
                <i> |1 x| (h(x)) @ i
            }

            fn transport(
                0 A: Type 0,
                0 B: Type 0,
                0 p: Path(_ => Type 0, A, B),
                1 x: A,
            ) -> B {
                coe(i => p @ i, 0, 1, x)
            }

            theorem sym(
                0 A: Type 0,
                0 x: A,
                0 y: A,
                0 p: Path(_ => A, x, y),
            ) -> Path(_ => A, y, x) {
                <i> hcom(A, 0, 1, [i = 0 && top || (bot) => <j> p @ j, i = 1 => <j> x], x)
            }
        ";

        let module = parse_module(src);
        assert!(module.is_ok());
        if let Ok(m) = module {
            assert_eq!(m.items.len(), 6);
            if let ModuleItem::Decl(d) = &m.items[0] {
                assert_eq!(d.kind, DeclKind::Fn);
                assert_eq!(d.name, "id");
                assert_eq!(d.params[0].mult, MultAst::Zero);
                assert_eq!(d.params[1].mult, MultAst::One);
            }
            if let ModuleItem::Decl(d) = &m.items[1] {
                assert_eq!(d.params[1].mult, MultAst::Many);
            }
            if let ModuleItem::Decl(d) = &m.items[2] {
                assert_eq!(d.kind, DeclKind::Theorem);
            }
            if let ModuleItem::Decl(d) = &m.items[5] {
                assert_eq!(d.name, "sym");
            }
        }
    }

    #[test]
    fn parses_let_blocks_projections_annotations_and_multi_arg_calls() {
        let expr = parse_expr("{ let 1 y: A = (x : A); f(y.0, y.1) }");
        assert!(expr.is_ok());
        if let Ok(e) = expr {
            assert!(matches!(e.kind, ExprKind::Let { .. }));
        }

        let interval = parse_expr("I");
        assert!(matches!(interval.map(|e| e.kind), Ok(ExprKind::Interval)));

        let multi_lam = parse_expr("|0 A, 1 x| x");
        assert!(matches!(
            multi_lam.map(|e| e.kind),
            Ok(ExprKind::Lam { .. })
        ));

        let default_mult = parse_module("fn f(x: Type 0) -> Type 0 { x }");
        assert!(default_mult.is_ok());
        if let Ok(m) = default_mult
            && let ModuleItem::Decl(d) = &m.items[0]
        {
            assert_eq!(d.params[0].mult, MultAst::Many);
        }

        let nested_pi = parse_expr("(0 x: (A)) -> B");
        assert!(matches!(nested_pi.map(|e| e.kind), Ok(ExprKind::Pi { .. })));
        let grouped_call = parse_expr("((f))(x)");
        assert!(matches!(
            grouped_call.map(|e| e.kind),
            Ok(ExprKind::App { .. })
        ));

        let unit_tt = parse_expr("()");
        assert!(matches!(unit_tt.map(|e| e.kind), Ok(ExprKind::Tt)));

        let ind_mod = parse_module(
            r"
            fn absurd(0 A: Type 0, 1 v: Void) -> A { match v {} }
            fn unit_id(1 u: Unit) -> Unit { match u { () => () } }
            fn not(1 b: Bool) -> Bool { match b { true => false, false => true } }
            fn add(1 n: Nat, 1 m: Nat) -> Nat {
                match n { zero => m, succ(k, ih) => succ(ih) }
            }
            theorem not_not(0 b: Bool) -> Path(_ => Bool, not(not(b)), b) {
                match b as |x| Path(_ => Bool, not(not(x)), x) {
                    true => <i> true,
                    false => <i> false,
                }
            }
            fn pred(1 n: Nat) -> Nat { match n { zero => zero, succ(k) => k } }
        ",
        );
        assert!(ind_mod.is_ok(), "parse err: {:?}", ind_mod.err());
        if let Ok(m) = ind_mod {
            assert_eq!(m.items.len(), 6);
        }
        assert!(parse_expr("match x { bad => x }").is_err());
    }

    #[test]
    fn parses_enum_struct_constructors_literals_and_patterns() {
        let src = r"
            enum Color { Red, Green, Blue }
            enum Option(0 A: Type 0) : Type 0 {
                None,
                Some(1 val: A),
            }
            enum List(0 A: Type 0) {
                Nil,
                Cons(1 head: A, 1 tail: List(A)),
            }
            struct Point(0 A: Type 0) {
                1 x: A,
                1 y: A,
            }
            fn mk(0 A: Type 0, 1 a: A, 1 b: A) -> Point(A) {
                Point { x: a, y: b }
            }
            fn mk_nat() -> Point(Nat) {
                Point(Nat) { x: zero, y: succ(zero) }
            }
            fn get_x(0 A: Type 0, ω p: Point(A)) -> A {
                p.x
            }
            fn swap_pt(0 A: Type 0, 1 p: Point(A)) -> Point(A) {
                match p {
                    Point { x, y: second } => Point { x: second, y: x },
                }
            }
            fn unwrap_or(0 A: Type 0, 1 o: Option(A), ω d: A) -> A {
                match o {
                    Option::None => d,
                    Option::Some(v) => v,
                }
            }
        ";
        let parsed = parse_module(src);
        assert!(parsed.is_ok(), "parse err: {:?}", parsed.err());
        if let Ok(m) = parsed {
            assert_eq!(m.items.len(), 9);
            assert!(matches!(
                &m.items[0],
                ModuleItem::Data(d) if d.kind == DataKind::Enum && d.variants.len() == 3
            ));
            assert!(matches!(
                &m.items[1],
                ModuleItem::Data(d) if d.level == Some(0) && d.variants.len() == 2
            ));
            assert!(matches!(
                &m.items[3],
                ModuleItem::Data(d) if d.kind == DataKind::Struct && d.variants[0].fields.len() == 2
            ));
        }
        assert!(parse_expr("x.foo").is_ok());
        assert!(parse_expr("x.(").is_err());
        assert!(parse_expr("Option::Some(zero)").is_ok());
        assert!(parse_expr("Option::None").is_ok());
        assert!(parse_expr("match (Point { x: zero, y: zero }) { Point { x, y } => x }").is_ok());
        assert!(matches!(
            parse_expr("Point(Nat) { x: zero, y: succ(zero) }"),
            Ok(crate::Expr {
                kind: ExprKind::StructLit {
                    ref type_name,
                    ref type_args,
                    ref fields,
                },
                ..
            }) if type_name == "Point" && type_args.len() == 1 && fields.len() == 2
        ));
    }

    #[test]
    fn reports_parse_and_lex_errors_with_spans() {
        let cases = [
            parse_module("bad").err(),
            parse_expr("2").err(),
            parse_expr("x.2").err(),
            parse_expr("Type").err(),
            parse_expr("$").err(),
            parse_expr("(x").err(),
            parse_expr(")").err(),
        ];

        for maybe_err in cases {
            assert!(maybe_err.is_some());
            if let Some(err) = maybe_err {
                let _ = err.span();
                assert_ne!(err.to_string(), "");
            }
        }
        assert!(matches!(
            parse_expr("2"),
            Err(ParseError::InvalidDimension { value: 2, .. })
        ));
        assert!(matches!(
            parse_expr("x.2"),
            Err(ParseError::InvalidProjection { value: 2, .. })
        ));
    }
}
