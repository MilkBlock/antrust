use std::collections::HashSet;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Any,
    Int(i64),
    Bool(bool),
    Unit,
    Var(String),
    Tup(Vec<Pattern>),
    CtorApp { name: String, args: Option<Vec<Pattern>> },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Field {
    Name(String),
    Index(i64),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Binding {
    Seq(Box<Expr>),
    One(Pattern, Box<Expr>),
    Rec(Vec<(Pattern, Box<Expr>)>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Unit,
    Int(i64),
    Bool(bool),
    Str(String),
    Builtin(String),
    Var(String),
    GVar(String),
    Ctor(String),
    App(Box<Expr>, Vec<Expr>),
    Op(String, Box<Expr>, Box<Expr>),
    Tup(Vec<Expr>),
    Arr(Vec<Expr>),
    Lam(Vec<Pattern>, Box<Expr>),
    Let(Box<Binding>, Box<Expr>),
    Sel(Box<Expr>, Field),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    Unit,
    Int,
    Float,
    Bool,
    Apply(Box<Ty>, Vec<Ty>),
    Arrow(Box<Ty>, Box<Ty>),
    Tuple(Vec<Ty>),
    Named(String),
    NamedVar(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TyCtor {
    pub name: String,
    pub args: Vec<Ty>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TyKind {
    Enum { params: Vec<String>, ctors: Vec<TyCtor> },
}

#[derive(Debug, Clone, PartialEq)]
pub enum TyBinding {
    One { name: String, kind: TyKind },
    Rec(Vec<(String, TyKind)>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Type(TyBinding),
    Term(Binding),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Prog {
    stmts: Vec<Stmt>,
}

impl Prog {
    pub fn new(stmts: Vec<Stmt>) -> Self {
        Self { stmts }
    }

    pub fn stmts(&self) -> &[Stmt] {
        &self.stmts
    }

    pub fn into_stmts(self) -> Vec<Stmt> {
        self.stmts
    }
}

#[derive(Debug)]
pub enum FrontendError {
    Lexing { line: usize, column: usize, message: String },
    Syntax { line: usize, column: usize, token: String },
    UnsupportedInput(String),
    Io(std::io::Error),
}

impl FrontendError {
    pub fn to_stderr(&self) -> String {
        match self {
            FrontendError::Lexing { line, column, message } => {
                format!("Lexing error at line {line}, character {column}: {message}")
            }
            FrontendError::Syntax { line, column, token } => {
                format!("Syntax error at line {line}, character {column}, at token `{token}`")
            }
            FrontendError::UnsupportedInput(name) => {
                format!("Unsupported input: {name}")
            }
            FrontendError::Io(err) => format!("IO error: {err}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum TokenKind {
    EOF,
    Int(i64),
    Bool(bool),
    Str(String),
    Ident(String),
    Ctor(String),
    RawCtor(String),
    Builtin(String),
    Let,
    Rec,
    And,
    In,
    Match,
    With,
    If,
    Then,
    Else,
    Type,
    Fun,
    Of,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Semi,
    SemiSemi,
    Dot,
    Arrow,
    Less,
    LessEq,
    Greater,
    GreaterEq,
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Or,
    Quote,
}

#[derive(Debug, Clone)]
struct Token {
    kind: TokenKind,
    lexeme: String,
    line: usize,
    column: usize,
}

struct Lexer {
    input: Vec<char>,
    index: usize,
    line: usize,
    column: usize,
}

impl Lexer {
    fn new(source: &str) -> Self {
        Self {
            input: source.chars().collect(),
            index: 0,
            line: 1,
            column: 1,
        }
    }

    fn peek(&self) -> Option<char> {
        self.input.get(self.index).copied()
    }

    fn peek_next(&self) -> Option<char> {
        self.input.get(self.index + 1).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let ch = self.input.get(self.index).copied()?;
        self.index += 1;
        if ch == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        Some(ch)
    }

    fn make_token(&self, kind: TokenKind, lexeme: String, line: usize, column: usize) -> Token {
        Token {
            kind,
            lexeme,
            line,
            column,
        }
    }

    fn next_token(&mut self) -> Result<Token, FrontendError> {
        loop {
            let ch = match self.peek() {
                Some(ch) => ch,
                None => {
                    return Ok(self.make_token(TokenKind::EOF, String::new(), self.line, self.column))
                }
            };

            if ch.is_whitespace() {
                self.bump();
                continue;
            }

            if ch == '(' && self.peek_next() == Some('*') {
                self.bump();
                self.bump();
                self.consume_comment(1)?;
                continue;
            }

            let line = self.line;
            let column = self.column;

            return Ok(match ch {
                '(' => {
                    self.bump();
                    self.make_token(TokenKind::LParen, "(".to_string(), line, column)
                }
                ')' => {
                    self.bump();
                    self.make_token(TokenKind::RParen, ")".to_string(), line, column)
                }
                '[' => {
                    self.bump();
                    self.make_token(TokenKind::LBracket, "[".to_string(), line, column)
                }
                ']' => {
                    self.bump();
                    self.make_token(TokenKind::RBracket, "]".to_string(), line, column)
                }
                ',' => {
                    self.bump();
                    self.make_token(TokenKind::Comma, ",".to_string(), line, column)
                }
                ';' => {
                    self.bump();
                    if self.peek() == Some(';') {
                        self.bump();
                        self.make_token(TokenKind::SemiSemi, ";;".to_string(), line, column)
                    } else {
                        self.make_token(TokenKind::Semi, ";".to_string(), line, column)
                    }
                }
                '.' => {
                    self.bump();
                    self.make_token(TokenKind::Dot, ".".to_string(), line, column)
                }
                '-' => {
                    self.bump();
                    if self.peek() == Some('>') {
                        self.bump();
                        self.make_token(TokenKind::Arrow, "->".to_string(), line, column)
                    } else {
                        self.make_token(TokenKind::Sub, "-".to_string(), line, column)
                    }
                }
                '<' => {
                    self.bump();
                    if self.peek() == Some('=') {
                        self.bump();
                        self.make_token(TokenKind::LessEq, "<=".to_string(), line, column)
                    } else {
                        self.make_token(TokenKind::Less, "<".to_string(), line, column)
                    }
                }
                '>' => {
                    self.bump();
                    if self.peek() == Some('=') {
                        self.bump();
                        self.make_token(TokenKind::GreaterEq, ">=".to_string(), line, column)
                    } else {
                        self.make_token(TokenKind::Greater, ">".to_string(), line, column)
                    }
                }
                '+' => {
                    self.bump();
                    self.make_token(TokenKind::Add, "+".to_string(), line, column)
                }
                '*' => {
                    self.bump();
                    self.make_token(TokenKind::Mul, "*".to_string(), line, column)
                }
                '/' => {
                    self.bump();
                    self.make_token(TokenKind::Div, "/".to_string(), line, column)
                }
                '=' => {
                    self.bump();
                    self.make_token(TokenKind::Eq, "=".to_string(), line, column)
                }
                '|' => {
                    self.bump();
                    self.make_token(TokenKind::Or, "|".to_string(), line, column)
                }
                '\'' => {
                    self.bump();
                    self.make_token(TokenKind::Quote, "'".to_string(), line, column)
                }
                '`' => {
                    self.bump();
                    let start = self.index;
                    let ctor = self.consume_identifier()?;
                    if ctor.is_empty() || !ctor.chars().next().unwrap().is_uppercase() {
                        return Err(FrontendError::Lexing {
                            line,
                            column,
                            message: format!("Unexpected token: `"),
                        });
                    }
                    let lexeme: String = self.input[start..self.index].iter().collect();
                    self.make_token(TokenKind::RawCtor(ctor), format!("`{lexeme}"), line, column)
                }
                '"' => self.lex_string(line, column)?,
                ch if ch.is_ascii_digit() => self.lex_number(line, column)?,
                ch if ch.is_ascii_alphabetic() || ch == '_' => self.lex_identifier(line, column)?,
                _ => {
                    self.bump();
                    return Err(FrontendError::Lexing {
                        line,
                        column,
                        message: format!("Unexpected token: {ch}"),
                    });
                }
            });
        }
    }

    fn consume_comment(&mut self, mut depth: usize) -> Result<(), FrontendError> {
        while let Some(ch) = self.peek() {
            if ch == '(' && self.peek_next() == Some('*') {
                self.bump();
                self.bump();
                depth += 1;
                continue;
            }
            if ch == '*' && self.peek_next() == Some(')') {
                self.bump();
                self.bump();
                depth -= 1;
                if depth == 0 {
                    return Ok(());
                }
                continue;
            }
            self.bump();
        }
        Err(FrontendError::Lexing {
            line: self.line,
            column: self.column,
            message: "Unexpected end of file: comment doesn't terminate".to_string(),
        })
    }

    fn lex_number(&mut self, line: usize, column: usize) -> Result<Token, FrontendError> {
        let start = self.index;
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                self.bump();
            } else {
                break;
            }
        }
        let lexeme: String = self.input[start..self.index].iter().collect();
        let value = lexeme.parse::<i64>().unwrap_or(0);
        Ok(self.make_token(TokenKind::Int(value), lexeme, line, column))
    }

    fn lex_identifier(&mut self, line: usize, column: usize) -> Result<Token, FrontendError> {
        let start = self.index;
        self.bump();
        while let Some(ch) = self.peek() {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                self.bump();
            } else {
                break;
            }
        }
        let lexeme: String = self.input[start..self.index].iter().collect();
        let token = match lexeme.as_str() {
            "if" => TokenKind::If,
            "then" => TokenKind::Then,
            "else" => TokenKind::Else,
            "match" => TokenKind::Match,
            "of" => TokenKind::Of,
            "with" => TokenKind::With,
            "let" => TokenKind::Let,
            "in" => TokenKind::In,
            "type" => TokenKind::Type,
            "fun" => TokenKind::Fun,
            "rec" => TokenKind::Rec,
            "and" => TokenKind::And,
            "true" => TokenKind::Bool(true),
            "false" => TokenKind::Bool(false),
            "print_endline" | "print_string" => TokenKind::Builtin(lexeme.clone()),
            _ => {
                if lexeme.chars().next().unwrap().is_uppercase() {
                    TokenKind::Ctor(lexeme.clone())
                } else {
                    TokenKind::Ident(lexeme.clone())
                }
            }
        };
        Ok(self.make_token(token, lexeme, line, column))
    }

    fn lex_string(&mut self, line: usize, column: usize) -> Result<Token, FrontendError> {
        self.bump();
        let mut buffer = String::new();
        while let Some(ch) = self.peek() {
            if ch == '"' {
                self.bump();
                return Ok(self.make_token(TokenKind::Str(buffer.clone()), buffer, line, column));
            }
            if ch == '\\' {
                self.bump();
                let esc = match self.peek() {
                    Some(c) => c,
                    None => {
                        return Err(FrontendError::Lexing {
                            line,
                            column,
                            message: "Invalid string literal".to_string(),
                        })
                    }
                };
                self.bump();
                let escaped = match esc {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    'b' => '\x08',
                    'f' => '\x0c',
                    '\\' => '\\',
                    '\'' => '\'',
                    '"' => '"',
                    _ => {
                        return Err(FrontendError::Lexing {
                            line,
                            column,
                            message: "Invalid string literal".to_string(),
                        })
                    }
                };
                buffer.push(escaped);
                continue;
            }
            if ch == '\n' {
                return Err(FrontendError::Lexing {
                    line,
                    column,
                    message: "Invalid string literal".to_string(),
                });
            }
            buffer.push(ch);
            self.bump();
        }
        Err(FrontendError::Lexing {
            line,
            column,
            message: "Unexpected end of file: string literal doesn't terminate".to_string(),
        })
    }

    fn consume_identifier(&mut self) -> Result<String, FrontendError> {
        let start = self.index;
        while let Some(ch) = self.peek() {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                self.bump();
            } else {
                break;
            }
        }
        Ok(self.input[start..self.index].iter().collect())
    }
}

struct Parser {
    tokens: Vec<Token>,
    index: usize,
}

impl Parser {
    fn new(source: &str) -> Result<Self, FrontendError> {
        let mut lexer = Lexer::new(source);
        let mut tokens = Vec::new();
        loop {
            let token = lexer.next_token()?;
            let is_eof = matches!(token.kind, TokenKind::EOF);
            tokens.push(token);
            if is_eof {
                break;
            }
        }
        Ok(Self { tokens, index: 0 })
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.index]
    }

    fn is_eof(&self) -> bool {
        matches!(self.peek().kind, TokenKind::EOF)
    }

    fn next(&mut self) -> &Token {
        let token = &self.tokens[self.index];
        if !matches!(token.kind, TokenKind::EOF) {
            self.index += 1;
        }
        token
    }

    fn consume(&mut self, kind: &TokenKind) -> bool {
        if std::mem::discriminant(&self.peek().kind) == std::mem::discriminant(kind) {
            self.next();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: TokenKind) -> Result<Token, FrontendError> {
        let token = self.peek().clone();
        if std::mem::discriminant(&token.kind) == std::mem::discriminant(&kind) {
            self.next();
            Ok(token)
        } else {
            Err(self.syntax_error())
        }
    }

    fn syntax_error(&self) -> FrontendError {
        let token = self.peek();
        let column_end = token.column + token.lexeme.chars().count();
        FrontendError::Syntax {
            line: token.line,
            column: column_end,
            token: token.lexeme.clone(),
        }
    }

    fn parse_prog(&mut self) -> Result<Prog, FrontendError> {
        let mut stmts = Vec::new();
        while !self.is_eof() {
            let stmt = self.parse_item()?;
            stmts.push(stmt);
            if self.consume(&TokenKind::SemiSemi) {
                continue;
            }
            if self.is_eof() {
                break;
            }
            return Err(self.syntax_error());
        }
        Ok(Prog { stmts })
    }

    fn parse_item(&mut self) -> Result<Stmt, FrontendError> {
        match self.peek().kind {
            TokenKind::Let => self.parse_let_decl(),
            TokenKind::Type => self.parse_type_decl(),
            _ => {
                let expr = self.parse_seq_expr()?;
                Ok(Stmt::Term(Binding::Seq(Box::new(expr))))
            }
        }
    }

    fn parse_let_decl(&mut self) -> Result<Stmt, FrontendError> {
        self.expect(TokenKind::Let)?;
        if self.consume(&TokenKind::Rec) {
            let first = self.parse_binding()?;
            let mut bindings = vec![first];
            while self.consume(&TokenKind::And) {
                bindings.push(self.parse_binding()?);
            }
            Ok(Stmt::Term(Binding::Rec(bindings)))
        } else {
            let binding = self.parse_binding()?;
            Ok(Stmt::Term(Binding::One(binding.0, binding.1)))
        }
    }

    fn parse_binding(&mut self) -> Result<(Pattern, Box<Expr>), FrontendError> {
        let pattern = self.parse_simple_pattern()?;
        self.expect(TokenKind::Eq)?;
        let expr = self.parse_seq_expr()?;
        Ok((pattern, Box::new(expr)))
    }

    fn parse_type_decl(&mut self) -> Result<Stmt, FrontendError> {
        self.expect(TokenKind::Type)?;
        let name = self.expect_ident()?;
        let params = self.parse_type_parameters()?;
        self.expect(TokenKind::Eq)?;
        let kind = self.parse_type_kind(params.clone())?;
        let mut rec_groups = vec![(name, kind)];
        while self.consume(&TokenKind::And) {
            let name = self.expect_ident()?;
            let params = self.parse_type_parameters()?;
            self.expect(TokenKind::Eq)?;
            let kind = self.parse_type_kind(params.clone())?;
            rec_groups.push((name, kind));
        }
        if rec_groups.len() == 1 {
            let (name, kind) = rec_groups.pop().unwrap();
            Ok(Stmt::Type(TyBinding::One { name, kind }))
        } else {
            Ok(Stmt::Type(TyBinding::Rec(rec_groups)))
        }
    }

    fn parse_type_parameters(&mut self) -> Result<Vec<String>, FrontendError> {
        let mut params = Vec::new();
        while self.consume(&TokenKind::Quote) {
            let name = self.expect_ident()?;
            params.push(name);
        }
        Ok(params)
    }

    fn parse_type_kind(&mut self, params: Vec<String>) -> Result<TyKind, FrontendError> {
        let ctors = self.parse_ctor_decls()?;
        Ok(TyKind::Enum { params, ctors })
    }

    fn parse_ctor_decls(&mut self) -> Result<Vec<TyCtor>, FrontendError> {
        let mut ctors = Vec::new();
        if self.consume(&TokenKind::Or) {
            // optional leading |
        }
        loop {
            let ctor = match &self.peek().kind {
                TokenKind::Ctor(name) => {
                    let name = name.clone();
                    self.next();
                    name
                }
                _ => return Err(self.syntax_error()),
            };
            let mut args = Vec::new();
            if self.consume(&TokenKind::Of) {
                args.push(self.parse_applied_type()?);
                while self.consume(&TokenKind::Mul) {
                    args.push(self.parse_applied_type()?);
                }
            }
            ctors.push(TyCtor { name: ctor, args });
            if self.consume(&TokenKind::Or) {
                if matches!(self.peek().kind, TokenKind::SemiSemi | TokenKind::And) {
                    break;
                }
                continue;
            }
            break;
        }
        Ok(ctors)
    }

    fn parse_type(&mut self) -> Result<Ty, FrontendError> {
        self.parse_function_type()
    }

    fn parse_function_type(&mut self) -> Result<Ty, FrontendError> {
        let left = self.parse_tuple_type()?;
        if self.consume(&TokenKind::Arrow) {
            let right = self.parse_function_type()?;
            Ok(Ty::Arrow(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    fn parse_tuple_type(&mut self) -> Result<Ty, FrontendError> {
        let mut types = vec![self.parse_applied_type()?];
        while self.consume(&TokenKind::Mul) {
            types.push(self.parse_applied_type()?);
        }
        if types.len() == 1 {
            Ok(types.remove(0))
        } else {
            Ok(Ty::Tuple(types))
        }
    }

    fn parse_applied_type(&mut self) -> Result<Ty, FrontendError> {
        let base = self.parse_atomic_type()?;
        let mut args = Vec::new();
        loop {
            match self.peek().kind {
                TokenKind::Ident(_) | TokenKind::LParen | TokenKind::Quote => {
                    let arg = self.parse_atomic_type()?;
                    args.push(arg);
                }
                _ => break,
            }
        }
        if args.is_empty() {
            Ok(base)
        } else {
            Ok(Ty::Apply(Box::new(base), args))
        }
    }

    fn parse_atomic_type(&mut self) -> Result<Ty, FrontendError> {
        match self.peek().kind.clone() {
            TokenKind::LParen => {
                self.next();
                let ty = self.parse_type()?;
                self.expect(TokenKind::RParen)?;
                Ok(ty)
            }
            TokenKind::Quote => {
                self.next();
                let name = self.expect_ident()?;
                Ok(Ty::NamedVar(name))
            }
            TokenKind::Ident(name) => {
                self.next();
                let ty = match name.as_str() {
                    "int" => Ty::Int,
                    "bool" => Ty::Bool,
                    "float" => Ty::Float,
                    "unit" => Ty::Unit,
                    _ => Ty::Named(name),
                };
                Ok(ty)
            }
            _ => Err(self.syntax_error()),
        }
    }

    fn parse_seq_expr(&mut self) -> Result<Expr, FrontendError> {
        let expr = self.parse_expr()?;
        if self.consume(&TokenKind::Semi) {
            let rest = self.parse_seq_expr()?;
            Ok(Expr::Let(Box::new(Binding::Seq(Box::new(expr))), Box::new(rest)))
        } else {
            Ok(expr)
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, FrontendError> {
        self.parse_comma_expr()
    }

    fn parse_let_expr(&mut self) -> Result<Expr, FrontendError> {
        self.expect(TokenKind::Let)?;
        if self.consume(&TokenKind::Rec) {
            let mut bindings = vec![self.parse_binding()?];
            while self.consume(&TokenKind::And) {
                bindings.push(self.parse_binding()?);
            }
            self.expect(TokenKind::In)?;
            let body = self.parse_expr()?;
            Ok(Expr::Let(Box::new(Binding::Rec(bindings)), Box::new(body)))
        } else {
            let binding = self.parse_binding()?;
            self.expect(TokenKind::In)?;
            let body = self.parse_expr()?;
            Ok(Expr::Let(Box::new(Binding::One(binding.0, binding.1)), Box::new(body)))
        }
    }

    fn parse_match_expr(&mut self) -> Result<Expr, FrontendError> {
        self.expect(TokenKind::Match)?;
        let target = self.parse_expr()?;
        self.expect(TokenKind::With)?;
        let cases = self.parse_cases()?;
        Ok(Expr::Match(Box::new(target), cases))
    }

    fn parse_cases(&mut self) -> Result<Vec<(Pattern, Expr)>, FrontendError> {
        let mut cases = Vec::new();
        if self.consume(&TokenKind::Or) {
            // optional leading |
        }
        loop {
            let pat = self.parse_pattern()?;
            self.expect(TokenKind::Arrow)?;
            let expr = self.parse_expr()?;
            cases.push((pat, expr));
            if self.consume(&TokenKind::Or) {
                continue;
            }
            break;
        }
        Ok(cases)
    }

    fn parse_fun_expr(&mut self) -> Result<Expr, FrontendError> {
        self.expect(TokenKind::Fun)?;
        let mut patterns = Vec::new();
        loop {
            patterns.push(self.parse_simple_pattern()?);
            match self.peek().kind {
                TokenKind::Arrow => break,
                _ => {
                    if !matches!(self.peek().kind, TokenKind::Ident(_) | TokenKind::LParen | TokenKind::Ctor(_)) {
                        return Err(self.syntax_error());
                    }
                }
            }
        }
        self.expect(TokenKind::Arrow)?;
        let body = self.parse_non_comma_expr()?;
        Ok(Expr::Lam(patterns, Box::new(body)))
    }

    fn parse_if_expr(&mut self) -> Result<Expr, FrontendError> {
        self.expect(TokenKind::If)?;
        let cond = self.parse_expr()?;
        self.expect(TokenKind::Then)?;
        let then_branch = self.parse_expr()?;
        if self.consume(&TokenKind::Else) {
            let else_branch = self.parse_expr()?;
            Ok(Expr::If(Box::new(cond), Box::new(then_branch), Box::new(else_branch)))
        } else {
            Ok(Expr::If(Box::new(cond), Box::new(then_branch), Box::new(Expr::Unit)))
        }
    }

    fn parse_comma_expr(&mut self) -> Result<Expr, FrontendError> {
        let first = self.parse_non_comma_expr()?;
        if self.consume(&TokenKind::Comma) {
            let mut exprs = vec![first];
            loop {
                exprs.push(self.parse_non_comma_expr()?);
                if !self.consume(&TokenKind::Comma) {
                    break;
                }
            }
            Ok(Expr::Tup(exprs))
        } else {
            Ok(first)
        }
    }

    fn parse_non_comma_expr(&mut self) -> Result<Expr, FrontendError> {
        match self.peek().kind {
            TokenKind::Let => self.parse_let_expr(),
            TokenKind::Match => self.parse_match_expr(),
            TokenKind::Fun => self.parse_fun_expr(),
            TokenKind::If => self.parse_if_expr(),
            _ => self.parse_infix_expr(0),
        }
    }

    fn parse_infix_expr(&mut self, min_prec: u8) -> Result<Expr, FrontendError> {
        let mut lhs = self.parse_application_expr()?;
        loop {
            let (op, prec) = match self.peek().kind {
                TokenKind::Eq => ("=", 1),
                TokenKind::Less => ("<", 2),
                TokenKind::LessEq => ("<=", 2),
                TokenKind::Greater => (">", 2),
                TokenKind::GreaterEq => (">=", 2),
                TokenKind::Add => ("+", 3),
                TokenKind::Sub => ("-", 3),
                TokenKind::Mul => ("*", 4),
                TokenKind::Div => ("/", 4),
                _ => break,
            };
            if prec < min_prec {
                break;
            }
            self.next();
            let rhs = self.parse_infix_expr(prec + 1)?;
            lhs = Expr::Op(op.to_string(), Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_application_expr(&mut self) -> Result<Expr, FrontendError> {
        let mut expr = self.parse_simple_expr()?;
        let mut args = Vec::new();
        loop {
            if !self.simple_expr_starts() {
                break;
            }
            let arg = self.parse_simple_expr()?;
            args.push(arg);
        }
        if args.is_empty() {
            Ok(expr)
        } else {
            expr = Expr::App(Box::new(expr), args);
            Ok(expr)
        }
    }

    fn simple_expr_starts(&self) -> bool {
        matches!(
            self.peek().kind,
            TokenKind::LParen
                | TokenKind::Ident(_)
                | TokenKind::Ctor(_)
                | TokenKind::RawCtor(_)
                | TokenKind::Int(_)
                | TokenKind::Bool(_)
                | TokenKind::Str(_)
                | TokenKind::Builtin(_)
                | TokenKind::LBracket
        )
    }

    fn parse_simple_expr(&mut self) -> Result<Expr, FrontendError> {
        let mut expr = match self.peek().kind.clone() {
            TokenKind::LParen => {
                self.next();
                if self.consume(&TokenKind::RParen) {
                    Expr::Unit
                } else {
                    let expr = self.parse_seq_expr()?;
                    self.expect(TokenKind::RParen)?;
                    expr
                }
            }
            TokenKind::Ident(name) => {
                self.next();
                Expr::Var(name)
            }
            TokenKind::RawCtor(name) => {
                self.next();
                Expr::App(Box::new(Expr::Ctor(name)), Vec::new())
            }
            TokenKind::Ctor(name) => {
                self.next();
                Expr::Ctor(name)
            }
            TokenKind::Int(value) => {
                self.next();
                Expr::Int(value)
            }
            TokenKind::Bool(value) => {
                self.next();
                Expr::Bool(value)
            }
            TokenKind::Str(value) => {
                self.next();
                Expr::Str(value)
            }
            TokenKind::Builtin(name) => {
                self.next();
                Expr::Builtin(name)
            }
            TokenKind::LBracket => {
                self.next();
                let mut elements = Vec::new();
                if !self.consume(&TokenKind::RBracket) {
                    elements.push(self.parse_expr()?);
                    while self.consume(&TokenKind::Semi) {
                        if self.consume(&TokenKind::RBracket) {
                            return Ok(Expr::Arr(elements));
                        }
                        elements.push(self.parse_expr()?);
                    }
                    self.expect(TokenKind::RBracket)?;
                }
                Expr::Arr(elements)
            }
            _ => return Err(self.syntax_error()),
        };

        loop {
            if self.consume(&TokenKind::Dot) {
                match self.peek().kind.clone() {
                    TokenKind::Ident(name) => {
                        self.next();
                        expr = Expr::Sel(Box::new(expr), Field::Name(name));
                    }
                    TokenKind::Int(value) => {
                        self.next();
                        expr = Expr::Sel(Box::new(expr), Field::Index(value));
                    }
                    _ => return Err(self.syntax_error()),
                }
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn parse_pattern(&mut self) -> Result<Pattern, FrontendError> {
        let mut pat = match self.peek().kind.clone() {
            TokenKind::Ctor(name) => {
                self.next();
                let mut args = Vec::new();
                while self.delimited_pattern_starts() {
                    args.push(self.parse_delimited_pattern()?);
                }
                if args.is_empty() {
                    Pattern::CtorApp { name, args: None }
                } else {
                    Pattern::CtorApp {
                        name,
                        args: Some(args),
                    }
                }
            }
            _ => self.parse_delimited_pattern()?,
        };

        if self.consume(&TokenKind::Comma) {
            let mut pats = vec![pat];
            loop {
                pats.push(self.parse_pattern()?);
                if !self.consume(&TokenKind::Comma) {
                    break;
                }
            }
            pat = Pattern::Tup(pats);
        }

        Ok(pat)
    }

    fn parse_simple_pattern(&mut self) -> Result<Pattern, FrontendError> {
        let mut pat = match self.peek().kind.clone() {
            TokenKind::Ident(name) => {
                self.next();
                Pattern::Var(name)
            }
            TokenKind::LParen => {
                self.next();
                if self.consume(&TokenKind::RParen) {
                    Pattern::Unit
                } else {
                    let pat = self.parse_simple_pattern()?;
                    self.expect(TokenKind::RParen)?;
                    pat
                }
            }
            _ => return Err(self.syntax_error()),
        };

        if self.consume(&TokenKind::Comma) {
            let mut pats = vec![pat];
            loop {
                pats.push(self.parse_simple_pattern()?);
                if !self.consume(&TokenKind::Comma) {
                    break;
                }
            }
            pat = Pattern::Tup(pats);
        }

        Ok(pat)
    }

    fn parse_delimited_pattern(&mut self) -> Result<Pattern, FrontendError> {
        match self.peek().kind.clone() {
            TokenKind::Int(value) => {
                self.next();
                Ok(Pattern::Int(value))
            }
            TokenKind::Bool(value) => {
                self.next();
                Ok(Pattern::Bool(value))
            }
            TokenKind::Ident(name) => {
                self.next();
                if name == "_" {
                    Ok(Pattern::Any)
                } else {
                    Ok(Pattern::Var(name))
                }
            }
            TokenKind::LParen => {
                self.next();
                if self.consume(&TokenKind::RParen) {
                    Ok(Pattern::Unit)
                } else {
                    let pat = self.parse_pattern()?;
                    self.expect(TokenKind::RParen)?;
                    Ok(pat)
                }
            }
            _ => Err(self.syntax_error()),
        }
    }

    fn delimited_pattern_starts(&self) -> bool {
        matches!(
            self.peek().kind,
            TokenKind::Int(_) | TokenKind::Bool(_) | TokenKind::Ident(_) | TokenKind::LParen
        )
    }

    fn expect_ident(&mut self) -> Result<String, FrontendError> {
        match self.peek().kind.clone() {
            TokenKind::Ident(name) => {
                self.next();
                Ok(name)
            }
            _ => Err(self.syntax_error()),
        }
    }
}

pub fn parse_prog(source: &str) -> Result<Prog, FrontendError> {
    let mut parser = Parser::new(source)?;
    parser.parse_prog()
}

pub fn print_ast(input_path: &Path, source: &str) -> Result<String, FrontendError> {
    let prog = parse_prog(source)?;
    let resolved = resolve_globals(prog);
    let _ = input_path;
    Ok(pp_prog(&resolved))
}

pub fn resolve_globals(prog: Prog) -> Prog {
    let mut globals: HashSet<String> = HashSet::new();
    let mut stmts = Vec::new();
    for stmt in prog.stmts {
        match stmt {
            Stmt::Term(Binding::One(pat, expr)) => {
                let env = Env {
                    globals: &globals,
                    locals: HashSet::new(),
                };
                let expr = Box::new(resolve_expr(*expr, &env));
                collect_pattern_vars(&pat, &mut globals);
                stmts.push(Stmt::Term(Binding::One(pat, expr)));
            }
            Stmt::Term(Binding::Rec(bindings)) => {
                for (pat, _) in &bindings {
                    collect_pattern_vars(pat, &mut globals);
                }
                let env = Env {
                    globals: &globals,
                    locals: HashSet::new(),
                };
                let resolved_bindings = bindings
                    .into_iter()
                    .map(|(pat, expr)| (pat, Box::new(resolve_expr(*expr, &env))))
                    .collect();
                stmts.push(Stmt::Term(Binding::Rec(resolved_bindings)));
            }
            Stmt::Term(Binding::Seq(expr)) => {
                let env = Env {
                    globals: &globals,
                    locals: HashSet::new(),
                };
                let expr = Box::new(resolve_expr(*expr, &env));
                stmts.push(Stmt::Term(Binding::Seq(expr)));
            }
            Stmt::Type(binding) => stmts.push(Stmt::Type(binding)),
        }
    }
    Prog { stmts }
}

struct Env<'a> {
    globals: &'a HashSet<String>,
    locals: HashSet<String>,
}

fn collect_pattern_vars(pattern: &Pattern, acc: &mut HashSet<String>) {
    match pattern {
        Pattern::Var(name) => {
            acc.insert(name.clone());
        }
        Pattern::Tup(items) => {
            for item in items {
                collect_pattern_vars(item, acc);
            }
        }
        Pattern::CtorApp { args: Some(args), .. } => {
            for item in args {
                collect_pattern_vars(item, acc);
            }
        }
        Pattern::Any | Pattern::Int(_) | Pattern::Bool(_) | Pattern::Unit | Pattern::CtorApp { args: None, .. } => {}
    }
}

fn resolve_expr(expr: Expr, env: &Env) -> Expr {
    match expr {
        Expr::Var(name) => {
            if env.locals.contains(&name) {
                Expr::Var(name)
            } else if env.globals.contains(&name) {
                Expr::GVar(name)
            } else {
                Expr::Var(name)
            }
        }
        Expr::GVar(_) | Expr::Ctor(_) | Expr::Int(_) | Expr::Bool(_) | Expr::Str(_) | Expr::Unit | Expr::Builtin(_) => expr,
        Expr::Lam(patterns, body) => {
            let mut locals = env.locals.clone();
            for pat in &patterns {
                collect_pattern_vars(pat, &mut locals);
            }
            let env = Env {
                globals: env.globals,
                locals,
            };
            Expr::Lam(patterns, Box::new(resolve_expr(*body, &env)))
        }
        Expr::App(fun, args) => Expr::App(
            Box::new(resolve_expr(*fun, env)),
            args.into_iter().map(|e| resolve_expr(e, env)).collect(),
        ),
        Expr::Op(op, lhs, rhs) => Expr::Op(
            op,
            Box::new(resolve_expr(*lhs, env)),
            Box::new(resolve_expr(*rhs, env)),
        ),
        Expr::If(c, t, e) => Expr::If(
            Box::new(resolve_expr(*c, env)),
            Box::new(resolve_expr(*t, env)),
            Box::new(resolve_expr(*e, env)),
        ),
        Expr::Tup(items) => Expr::Tup(items.into_iter().map(|e| resolve_expr(e, env)).collect()),
        Expr::Arr(items) => Expr::Arr(items.into_iter().map(|e| resolve_expr(e, env)).collect()),
        Expr::Let(binding, body) => {
            let (binding, locals) = match *binding {
                Binding::Seq(expr) => (
                    Binding::Seq(Box::new(resolve_expr(*expr, env))),
                    env.locals.clone(),
                ),
                Binding::One(pat, expr) => {
                    let expr = Box::new(resolve_expr(*expr, env));
                    let mut locals = env.locals.clone();
                    collect_pattern_vars(&pat, &mut locals);
                    (Binding::One(pat, expr), locals)
                }
                Binding::Rec(bindings) => {
                    let mut locals = env.locals.clone();
                    for (pat, _) in &bindings {
                        collect_pattern_vars(pat, &mut locals);
                    }
                    let env_rec = Env {
                        globals: env.globals,
                        locals: locals.clone(),
                    };
                    let bindings = bindings
                        .into_iter()
                        .map(|(pat, expr)| (pat, Box::new(resolve_expr(*expr, &env_rec))))
                        .collect();
                    (Binding::Rec(bindings), locals)
                }
            };
            let env = Env {
                globals: env.globals,
                locals,
            };
            Expr::Let(Box::new(binding), Box::new(resolve_expr(*body, &env)))
        }
        Expr::Sel(expr, field) => Expr::Sel(Box::new(resolve_expr(*expr, env)), field),
        Expr::Match(expr, cases) => {
            let expr = resolve_expr(*expr, env);
            let cases = cases
                .into_iter()
                .map(|(pat, expr)| {
                    let mut locals = env.locals.clone();
                    collect_pattern_vars(&pat, &mut locals);
                    let env_case = Env {
                        globals: env.globals,
                        locals,
                    };
                    (pat, resolve_expr(expr, &env_case))
                })
                .collect();
            Expr::Match(Box::new(expr), cases)
        }
    }
}

pub fn pp_prog(prog: &Prog) -> String {
    syntax_pp::pp_prog(prog)
}

pub fn pp_stmt(stmt: &Stmt) -> String {
    syntax_pp::pp_stmt(stmt)
}

#[allow(dead_code)]
fn pp_type_binding(binding: &TyBinding) -> String {
    match binding {
        TyBinding::One { name, kind } => pp_enum(name, kind) + ";;",
        TyBinding::Rec(groups) => {
            let mut parts = Vec::new();
            for (idx, (name, kind)) in groups.iter().enumerate() {
                let rendered = pp_enum_with_prefix(name, kind, idx != 0);
                parts.push(rendered);
            }
            format!("{};;", parts.join("\n"))
        }
    }
}

#[allow(dead_code)]
fn pp_enum(name: &str, kind: &TyKind) -> String {
    pp_enum_with_prefix(name, kind, false)
}

#[allow(dead_code)]
fn pp_enum_with_prefix(name: &str, kind: &TyKind, is_and: bool) -> String {
    let (params, ctors) = match kind {
        TyKind::Enum { params, ctors } => (params, ctors),
    };
    let mut prefix = if is_and { "and".to_string() } else { "type".to_string() };
    prefix.push(' ');
    prefix.push_str(&pp_type_params(params));
    prefix.push_str(name);
    prefix.push_str(" = ");

    let ctor_strs: Vec<String> = ctors.iter().map(pp_ctor).collect();
    let single_line = format!("{}| {}", prefix, ctor_strs.join(" | "));
    if single_line.len() <= 80 {
        single_line
    } else {
        let mut out = String::new();
        out.push_str(&format!("{}\n", prefix.trim_end()));
        for (idx, ctor) in ctor_strs.iter().enumerate() {
            out.push_str("  | ");
            out.push_str(ctor);
            if idx + 1 < ctor_strs.len() {
                out.push('\n');
            }
        }
        out
    }
}

#[allow(dead_code)]
fn pp_type_params(params: &[String]) -> String {
    if params.is_empty() {
        String::new()
    } else if params.len() == 1 {
        format!("'{} ", params[0])
    } else {
        let joined = params
            .iter()
            .map(|p| format!("'{}", p))
            .collect::<Vec<_>>()
            .join(",");
        format!("({}) ", joined)
    }
}

#[allow(dead_code)]
fn pp_ctor(ctor: &TyCtor) -> String {
    if ctor.args.is_empty() {
        ctor.name.clone()
    } else {
        let args = ctor
            .args
            .iter()
            .map(|ty| pp_ty(ty, false))
            .collect::<Vec<_>>()
            .join(" * ");
        format!("{} of {}", ctor.name, args)
    }
}

#[allow(dead_code)]
fn pp_ty(ty: &Ty, c: bool) -> String {
    let wrap = |s: String| if c { format!("({})", s) } else { s };
    match ty {
        Ty::Unit => "unit".to_string(),
        Ty::Int => "int".to_string(),
        Ty::Float => "float".to_string(),
        Ty::Bool => "bool".to_string(),
        Ty::Named(name) => name.clone(),
        Ty::NamedVar(name) => format!("'{}", name),
        Ty::Apply(base, args) => {
            let args_strs = args.iter().map(|t| pp_ty(t, true)).collect::<Vec<_>>();
            let args_str = if args_strs.len() > 1 {
                format!("({})", args_strs.join(","))
            } else {
                args_strs.join("")
            };
            wrap(format!("{} {}", args_str, pp_ty(base, c)))
        }
        Ty::Arrow(lhs, rhs) => wrap(format!("{} -> {}", pp_ty(lhs, true), pp_ty(rhs, true))),
        Ty::Tuple(items) => format!("({})", items.iter().map(|t| pp_ty(t, true)).collect::<Vec<_>>().join("*")),
    }
}

pub fn pp_pattern(pattern: &Pattern, c: bool) -> String {
    syntax_pp::pp_pattern(pattern, c)
}

#[allow(dead_code)]
const RIBBON_WIDTH: usize = 64; // PPrint.ToBuffer.pretty 0.8 80

#[allow(dead_code)]
fn fits_in_ribbon(s: &str) -> bool {
    s.len() <= RIBBON_WIDTH
}

#[allow(dead_code)]
fn fits_in_ribbon_at(s: &str, indent: usize) -> bool {
    s.len().saturating_add(indent) <= RIBBON_WIDTH
}

#[allow(dead_code)]
fn wrap_parens(s: String) -> String {
    if !s.contains('\n') {
        return format!("({})", s);
    }
    let mut lines = s.lines();
    let first = lines.next().unwrap_or("");
    let rest: Vec<String> = lines.map(|line| format!(" {}", line)).collect();
    let mut out = String::new();
    out.push('(');
    out.push_str(first);
    if !rest.is_empty() {
        out.push('\n');
        out.push_str(&rest.join("\n"));
    }
    out.push(')');
    out
}

#[allow(dead_code)]
fn pp_expr_inline(expr: &Expr, c: bool, _indent: usize) -> String {
    let wrap = |s: String| if c { wrap_parens(s) } else { s };
    match expr {
        Expr::Unit => "()".to_string(),
        Expr::Int(value) => value.to_string(),
        Expr::Bool(value) => value.to_string(),
        Expr::Str(value) => format!("\"{}\"", value),
        Expr::Builtin(name) => name.clone(),
        Expr::Var(name) => name.clone(),
        Expr::GVar(name) => format!("global:{}", name),
        Expr::Ctor(name) => name.clone(),
        Expr::App(fun, args) => {
            if let Expr::Ctor(name) = &**fun {
                if args.len() > 1 {
                    let tup = Expr::Tup(args.clone());
                    return wrap(format!("{} {}", name, pp_expr_inline(&tup, true, _indent)));
                }
            }
            let mut parts = vec![pp_expr_inline_tight(fun, _indent)];
            for arg in args {
                parts.push(pp_expr_inline_tight(arg, _indent));
            }
            wrap(parts.join(" "))
        }
        Expr::Op(op, lhs, rhs) => wrap(format!(
            "{} {} {}",
            pp_expr_inline_tight(lhs, _indent),
            op,
            pp_expr_inline_tight(rhs, _indent)
        )),
        Expr::Tup(items) => format!(
            "({})",
            items
                .iter()
                .map(|e| pp_expr_inline_tight(e, _indent))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Expr::Arr(items) => format!(
            "[{}]",
            items
                .iter()
                .map(|e| pp_expr_inline_tight(e, _indent))
                .collect::<Vec<_>>()
                .join("; ")
        ),
        Expr::Lam(patterns, body) => {
            let pat_str = patterns
                .iter()
                .map(|p| pp_pattern(p, true))
                .collect::<Vec<_>>()
                .join(" ");
            let inline_body = pp_expr_inline(body, true, _indent);
            wrap(format!("fun {} -> {}", pat_str, inline_body))
        }
        Expr::Let(binding, body) => match binding.as_ref() {
            Binding::Seq(expr) => format!(
                "{}; {}",
                pp_expr_inline(expr, false, _indent),
                pp_expr_inline(body, false, _indent)
            ),
            Binding::One(pat, expr) => format!(
                "let {} = {} in {}",
                pp_pattern(pat, false),
                pp_expr_inline(expr, false, _indent),
                pp_expr_inline(body, false, _indent)
            ),
            Binding::Rec(bindings) => {
                let mut parts = Vec::new();
                for (idx, (pat, expr)) in bindings.iter().enumerate() {
                    let prefix = if idx == 0 { "let rec" } else { "and" };
                    parts.push(format!(
                        "{} {} = {}",
                        prefix,
                        pp_pattern(pat, false),
                        pp_expr_inline(expr, false, _indent)
                    ));
                }
                format!("{} in {}", parts.join(" "), pp_expr_inline(body, false, _indent))
            }
        },
        Expr::Sel(expr, field) => {
            let field_str = match field {
                Field::Name(name) => name.clone(),
                Field::Index(idx) => idx.to_string(),
            };
            format!("{}.{}", pp_expr_inline_tight(expr, _indent), field_str)
        }
        Expr::If(cond, then_branch, else_branch) => format!(
            "if {} then {} else {}",
            pp_expr_inline(cond, true, _indent),
            pp_expr_inline(then_branch, true, _indent),
            pp_expr_inline(else_branch, true, _indent)
        ),
        Expr::Match(target, cases) => {
            let mut parts = Vec::new();
            parts.push(format!(
                "match {} with",
                pp_expr_inline(target, false, _indent)
            ));
            for (pat, expr) in cases {
                parts.push(format!(
                    "| {} -> {}",
                    pp_pattern(pat, false),
                    pp_expr_inline(expr, true, _indent)
                ));
            }
            parts.join(" ")
        }
    }
}

#[allow(dead_code)]
fn needs_tight_parens(expr: &Expr) -> bool {
    matches!(expr, Expr::If(_, _, _) | Expr::Let(_, _) | Expr::Match(_, _))
}

#[allow(dead_code)]
fn pp_expr_inline_tight(expr: &Expr, indent: usize) -> String {
    if needs_tight_parens(expr) {
        wrap_parens(pp_expr_inline(expr, false, indent))
    } else {
        pp_expr_inline(expr, true, indent)
    }
}

#[allow(dead_code)]
fn pp_expr_tight(expr: &Expr, indent: usize, force_seq_break: bool) -> String {
    if needs_tight_parens(expr) {
        wrap_parens(pp_expr_inner(expr, false, indent, force_seq_break, true))
    } else {
        pp_expr_inner(expr, true, indent, force_seq_break, true)
    }
}

pub fn pp_expr(expr: &Expr, c: bool, indent: usize) -> String {
    let _ = indent;
    syntax_pp::pp_expr(expr, c)
}

#[allow(dead_code)]
fn pp_expr_inner(expr: &Expr, c: bool, indent: usize, force_seq_break: bool, inline_ctx: bool) -> String {
    let wrap = |s: String| if c { wrap_parens(s) } else { s };
    match expr {
        Expr::Unit => "()".to_string(),
        Expr::Int(value) => value.to_string(),
        Expr::Bool(value) => value.to_string(),
        Expr::Str(value) => format!("\"{}\"", value),
        Expr::Builtin(name) => name.clone(),
        Expr::Var(name) => name.clone(),
        Expr::GVar(name) => format!("global:{}", name),
        Expr::Ctor(name) => name.clone(),
        Expr::App(fun, args) => {
            let (fun_expr, args) = if let Expr::Ctor(name) = &**fun {
                if args.len() > 1 {
                    let tup = Expr::Tup(args.clone());
                    return wrap(format!(
                        "{} {}",
                        name,
                        pp_expr_inner(&tup, true, indent, force_seq_break, true)
                    ));
                }
                (Expr::Ctor(name.clone()), args.clone())
            } else {
                ((**fun).clone(), args.clone())
            };
            let fun_inline = pp_expr_inline_tight(&fun_expr, indent);
            let mut col = indent + fun_inline.len();
            let mut parts = vec![pp_expr_tight(&fun_expr, indent, force_seq_break)];
            for arg in args {
                col += 1;
                let arg_inline = pp_expr_inline_tight(&arg, col);
                parts.push(pp_expr_tight(&arg, col, force_seq_break));
                col += arg_inline.len();
            }
            wrap(parts.join(" "))
        }
        Expr::Op(op, lhs, rhs) => wrap(format!(
            "{} {} {}",
            pp_expr_tight(lhs, indent, force_seq_break),
            op,
            pp_expr_tight(rhs, indent, force_seq_break)
        )),
        Expr::Tup(items) => format!(
            "({})",
            items
                .iter()
                .map(|e| pp_expr_tight(e, indent, force_seq_break))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Expr::Arr(items) => format!(
            "[{}]",
            items
                .iter()
                .map(|e| pp_expr_tight(e, indent, force_seq_break))
                .collect::<Vec<_>>()
                .join("; ")
        ),
        Expr::Lam(patterns, body) => {
            let pat_str = patterns
                .iter()
                .map(|p| pp_pattern(p, true))
                .collect::<Vec<_>>()
                .join(" ");
            let inline_body = pp_expr_inline(body, true, indent);
            let inline = wrap(format!("fun {} -> {}", pat_str, inline_body));
            if fits_in_ribbon_at(&inline, indent) {
                return inline;
            }
            let body_str = pp_expr_inner(body, true, indent + 2, force_seq_break, false);
            let body_indent = 2;
            let rendered = format!(
                "fun {} ->\n{}",
                pat_str,
                indent_lines(&body_str, body_indent)
            );
            wrap(rendered)
        }
        Expr::Let(binding, body) => {
            let rendered = match binding.as_ref() {
                Binding::Seq(expr) => {
                    let expr_str = pp_expr_inner(expr, false, indent, force_seq_break, inline_ctx);
                    if force_seq_break {
                        let body_str = pp_expr_inner(body, false, indent, true, inline_ctx);
                        let body_str = if inline_ctx {
                            indent_lines(&body_str, indent)
                        } else {
                            body_str
                        };
                        format!("{};\n{}", expr_str, body_str)
                    } else {
                        let inline = format!(
                            "{}; {}",
                            pp_expr_inline(expr, false, indent),
                            pp_expr_inline(body, false, indent)
                        );
                        let body_str = pp_expr_inner(body, false, indent, force_seq_break, inline_ctx);
                        if fits_in_ribbon_at(&inline, indent)
                            && !expr_str.contains('\n')
                            && !body_str.contains('\n')
                        {
                            inline
                        } else {
                            let body_str = pp_expr_inner(body, false, indent, true, inline_ctx);
                            let body_str = if inline_ctx {
                                indent_lines(&body_str, indent)
                            } else {
                                body_str
                            };
                            format!("{};\n{}", expr_str, body_str)
                        }
                    }
                }
                Binding::One(pat, expr) => {
                    let expr_inline = pp_expr_inline(expr, false, indent);
                    let head_inline =
                        format!("let {} = {} in", pp_pattern(pat, false), expr_inline);
                    let expr_str = pp_expr_inner(expr, false, 0, force_seq_break, false);
                    let body_str = pp_expr_inner(body, false, 0, force_seq_break, false);
                    if fits_in_ribbon_at(&head_inline, indent) && !expr_str.contains('\n') {
                        if body_str.contains('\n') {
                            format!("{}\n{}", head_inline, body_str)
                        } else {
                            let inline = format!("{} {}", head_inline, body_str);
                            if fits_in_ribbon_at(&inline, indent) {
                                inline
                            } else {
                                format!("{}\n{}", head_inline, body_str)
                            }
                        }
                    } else {
                        let indented_expr = indent_lines(&expr_str, 2);
                        format!(
                            "let {} =\n{}\nin\n{}",
                            pp_pattern(pat, false),
                            indented_expr,
                            body_str
                        )
                    }
                }
                Binding::Rec(bindings) => {
                    let inline = {
                        let mut parts_inline = Vec::new();
                        for (idx, (pat, expr)) in bindings.iter().enumerate() {
                            let prefix = if idx == 0 { "let rec" } else { "and" };
                            parts_inline.push(format!(
                                "{} {} = {}",
                                prefix,
                                pp_pattern(pat, false),
                                pp_expr_inline(expr, false, indent)
                            ));
                        }
                        format!(
                            "{} in {}",
                            parts_inline.join(" "),
                            pp_expr_inline(body, false, indent)
                        )
                    };
                    let mut parts = Vec::new();
                    let mut has_multiline = false;
                    for (idx, (pat, expr)) in bindings.iter().enumerate() {
                        let prefix = if idx == 0 { "let rec" } else { "and" };
                        let expr_str = pp_expr_inner(expr, false, indent, force_seq_break, false);
                        if expr_str.contains('\n') {
                            has_multiline = true;
                        }
                        let rendered = if expr_str.contains('\n') {
                            format!(
                                "{} {} =\n{}",
                                prefix,
                                pp_pattern(pat, false),
                                indent_lines(&expr_str, indent + 2)
                            )
                        } else {
                            format!("{} {} = {}", prefix, pp_pattern(pat, false), expr_str)
                        };
                        parts.push(rendered);
                    }
                    let body_str = pp_expr_inner(body, false, indent, force_seq_break, false);
                    if fits_in_ribbon_at(&inline, indent) && !has_multiline && !body_str.contains('\n')
                    {
                        inline
                    } else {
                        format!("{}\nin\n{}", parts.join("\n"), body_str)
                    }
                }
            };
            rendered
        }
        Expr::Sel(expr, field) => {
            let field_str = match field {
                Field::Name(name) => name.clone(),
                Field::Index(idx) => idx.to_string(),
            };
            format!(
                "{}.{}",
                pp_expr_tight(expr, indent, force_seq_break),
                field_str
            )
        }
        Expr::If(cond, then_branch, else_branch) => {
            let inline = format!(
                "if {} then {} else {}",
                pp_expr_inline(cond, true, indent),
                pp_expr_inline(then_branch, true, indent),
                pp_expr_inline(else_branch, true, indent)
            );
            let cond_inline = pp_expr_inline(cond, true, indent);
            let cond_str = pp_expr_inner(cond, true, indent + 2, force_seq_break, false);
            let then_str = pp_expr_inner(then_branch, true, indent + 2, force_seq_break, false);
            let else_str = pp_expr_inner(else_branch, true, indent + 2, force_seq_break, false);
            if fits_in_ribbon_at(&inline, indent)
                && !cond_str.contains('\n')
                && !then_str.contains('\n')
                && !else_str.contains('\n')
            {
                inline
            } else {
                let head_inline = format!("if {}", cond_inline);
                let head = if !cond_str.contains('\n') && fits_in_ribbon_at(&head_inline, indent) {
                    head_inline
                } else {
                    format!("if\n{}", indent_lines(&cond_str, 2))
                };
                let then_indented = indent_lines(&then_str, 2);
                let else_indented = indent_lines(&else_str, 2);
                format!(
                    "{}\nthen\n{}\nelse\n{}",
                    head, then_indented, else_indented
                )
            }
        }
        Expr::Match(target, cases) => {
            let inline = pp_expr_inline(expr, c, indent);
            if fits_in_ribbon_at(&inline, indent) {
                return inline;
            }
            let head = format!("match {} with", pp_expr_inline(target, false, indent));
            let case_indent = if inline_ctx {
                indent.saturating_sub(2)
            } else {
                0
            };
            let case_prefix = " ".repeat(case_indent);
            let mut lines = vec![head];
            for (pat, expr) in cases {
                let expr_str = pp_expr_inner(expr, true, indent + 2, force_seq_break, false);
                let inline_case = format!(
                    "{}| {} -> {}",
                    case_prefix,
                    pp_pattern(pat, false),
                    pp_expr_inline(expr, true, indent)
                );
                if fits_in_ribbon_at(&inline_case, indent) && !expr_str.contains('\n') {
                    lines.push(inline_case);
                } else {
                    let indented = indent_lines(&expr_str, case_indent + 2);
                    lines.push(format!(
                        "{}| {} ->\n{}",
                        case_prefix,
                        pp_pattern(pat, false),
                        indented
                    ));
                }
            }
            lines.join("\n")
        }
    }
}

#[allow(dead_code)]
fn indent_lines(s: &str, indent: usize) -> String {
    let prefix = " ".repeat(indent);
    s.lines()
        .map(|line| format!("{}{}", prefix, line))
        .collect::<Vec<_>>()
        .join("\n")
}

pub fn repo_root() -> PathBuf {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest_dir
        .parent()
        .and_then(Path::parent)
        .expect("repo root")
        .to_path_buf()
}

mod syntax_pp {
    use super::{Binding, Expr, Field, Pattern, Prog, Stmt, Ty, TyBinding, TyCtor, TyKind};
    use std::rc::Rc;

    const WIDTH: usize = 80;
    const RIBBON_WIDTH: usize = 64; // PPrint.ToBuffer.pretty 0.8 80

    #[derive(Clone)]
    struct Doc {
        node: Rc<DocNode>,
        requirement: usize,
    }

    enum DocNode {
        Nil,
        TextStatic(&'static str),
        TextOwned(String),
        Concat(Doc, Doc),
        Break(usize),
        Nest(usize, Doc),
        Group(Doc),
        Align(Doc),
    }

    impl Doc {
        fn nil() -> Self {
            Self {
                node: Rc::new(DocNode::Nil),
                requirement: 0,
            }
        }

        fn text(s: &'static str) -> Self {
            Self {
                node: Rc::new(DocNode::TextStatic(s)),
                requirement: s.len(),
            }
        }

        fn text_owned(s: String) -> Self {
            let requirement = s.len();
            Self {
                node: Rc::new(DocNode::TextOwned(s)),
                requirement,
            }
        }

        fn concat(self, other: Doc) -> Doc {
            match (self.node.as_ref(), other.node.as_ref()) {
                (DocNode::Nil, _) => other,
                (_, DocNode::Nil) => self,
                _ => {
                    let requirement = self.requirement.saturating_add(other.requirement);
                    Doc {
                        node: Rc::new(DocNode::Concat(self, other)),
                        requirement,
                    }
                }
            }
        }

        fn group(self) -> Doc {
            Doc {
                node: Rc::new(DocNode::Group(self.clone())),
                requirement: self.requirement,
            }
        }

        fn nest(self, indent: usize) -> Doc {
            Doc {
                node: Rc::new(DocNode::Nest(indent, self.clone())),
                requirement: self.requirement,
            }
        }

        fn align(self) -> Doc {
            Doc {
                node: Rc::new(DocNode::Align(self.clone())),
                requirement: self.requirement,
            }
        }

        fn brk(n: usize) -> Doc {
            Doc {
                node: Rc::new(DocNode::Break(n)),
                requirement: n,
            }
        }
    }

    #[derive(Copy, Clone, Eq, PartialEq)]
    enum Mode {
        Flat,
        Break,
    }

    #[derive(Clone)]
    struct Cmd {
        indent: usize,
        mode: Mode,
        doc: Doc,
    }

    fn write_spaces(out: &mut String, mut count: usize) {
        const CHUNK: &str = "                                                                ";
        while count >= CHUNK.len() {
            out.push_str(CHUNK);
            count -= CHUNK.len();
        }
        if count > 0 {
            out.push_str(&CHUNK[..count]);
        }
    }

    fn render(doc: Doc) -> String {
        let mut out = String::new();
        let mut column = 0usize;
        let mut last_indent = 0usize;

        let mut stack = vec![Cmd {
            indent: 0,
            mode: Mode::Break,
            doc,
        }];

        while let Some(cmd) = stack.pop() {
            match cmd.doc.node.as_ref() {
                DocNode::Nil => {}
                DocNode::TextStatic(s) => {
                    out.push_str(s);
                    column += s.len();
                }
                DocNode::TextOwned(s) => {
                    out.push_str(s);
                    column += s.len();
                }
                DocNode::Concat(left, right) => {
                    stack.push(Cmd {
                        indent: cmd.indent,
                        mode: cmd.mode,
                        doc: right.clone(),
                    });
                    stack.push(Cmd {
                        indent: cmd.indent,
                        mode: cmd.mode,
                        doc: left.clone(),
                    });
                }
                DocNode::Break(spaces) => match cmd.mode {
                    Mode::Flat => {
                        write_spaces(&mut out, *spaces);
                        column += spaces;
                    }
                    Mode::Break => {
                        out.push('\n');
                        write_spaces(&mut out, cmd.indent);
                        column = cmd.indent;
                        last_indent = cmd.indent;
                    }
                },
                DocNode::Nest(amount, doc) => stack.push(Cmd {
                    indent: cmd.indent + amount,
                    mode: cmd.mode,
                    doc: doc.clone(),
                }),
                DocNode::Align(doc) => stack.push(Cmd {
                    indent: column,
                    mode: cmd.mode,
                    doc: doc.clone(),
                }),
                DocNode::Group(doc) => {
                    let end_column = column.saturating_add(doc.requirement);
                    let flatten = cmd.mode == Mode::Flat
                        || (end_column <= WIDTH
                            && end_column <= last_indent.saturating_add(RIBBON_WIDTH));
                    stack.push(Cmd {
                        indent: cmd.indent,
                        mode: if flatten { Mode::Flat } else { Mode::Break },
                        doc: doc.clone(),
                    });
                }
            }
        }

        out
    }

    fn concat_all(docs: impl IntoIterator<Item = Doc>) -> Doc {
        docs.into_iter()
            .fold(Doc::nil(), |acc, doc| acc.concat(doc))
    }

    fn separate_map<T>(separator: Doc, items: &[T], mut f: impl FnMut(&T) -> Doc) -> Doc {
        let mut docs = Vec::new();
        for (idx, item) in items.iter().enumerate() {
            if idx != 0 {
                docs.push(separator.clone());
            }
            docs.push(f(item));
        }
        concat_all(docs)
    }

    fn concat_map<T>(items: &[T], mut f: impl FnMut(&T) -> Doc) -> Doc {
        let docs = items.iter().map(|item| f(item));
        concat_all(docs)
    }

    fn parens(inner: Doc) -> Doc {
        Doc::text("(").concat(inner).concat(Doc::text(")"))
    }

    fn brackets(inner: Doc) -> Doc {
        Doc::text("[").concat(inner).concat(Doc::text("]"))
    }

    fn dquotes(inner: Doc) -> Doc {
        Doc::text("\"").concat(inner).concat(Doc::text("\""))
    }

    fn escape_ocaml_string(input: &str) -> String {
        let mut out = String::with_capacity(input.len());
        for ch in input.chars() {
            match ch {
                '\\' => out.push_str("\\\\"),
                '"' => out.push_str("\\\""),
                '\n' => out.push_str("\\n"),
                '\t' => out.push_str("\\t"),
                '\r' => out.push_str("\\r"),
                '\x08' => out.push_str("\\b"),
                '\x0c' => out.push_str("\\f"),
                ch if ch.is_control() => {
                    let code = ch as u32;
                    if code <= 255 {
                        out.push('\\');
                        out.push_str(&format!("{:03}", code));
                    } else {
                        out.push(ch);
                    }
                }
                _ => out.push(ch),
            }
        }
        out
    }

    fn pp_field(field: &Field) -> Doc {
        match field {
            Field::Name(name) => Doc::text_owned(name.clone()),
            Field::Index(index) => Doc::text_owned(index.to_string()),
        }
    }

    fn pp_pattern_internal(c: bool, pattern: &Pattern) -> Doc {
        let wrap = |doc: Doc| if c { parens(doc) } else { doc };
        match pattern {
            Pattern::Any => Doc::text("_"),
            Pattern::Int(value) => Doc::text_owned(value.to_string()),
            Pattern::Bool(true) => Doc::text("true"),
            Pattern::Bool(false) => Doc::text("false"),
            Pattern::Unit => Doc::text("()"),
            Pattern::Var(name) => Doc::text_owned(name.clone()),
            Pattern::Tup(items) => {
                let inner = separate_map(
                    Doc::text(",").concat(Doc::text(" ")),
                    items,
                    |p| pp_pattern_internal(true, p),
                );
                wrap(inner)
            }
            Pattern::CtorApp { name, args } => match args {
                None => Doc::text_owned(name.clone()),
                Some(args) => {
                    let args = if args.len() == 1 {
                        if let Pattern::Tup(inner) = &args[0] {
                            inner.clone()
                        } else {
                            args.clone()
                        }
                    } else {
                        args.clone()
                    };
                    let arg_doc = pp_pattern_internal(true, &Pattern::Tup(args));
                    wrap(Doc::text_owned(name.clone()).concat(Doc::text(" ")).concat(arg_doc))
                }
            },
        }
    }

    fn pp_pattern_doc(pattern: &Pattern) -> Doc {
        pp_pattern_internal(false, pattern)
    }

    fn pp_pattern_prime_doc(pattern: &Pattern) -> Doc {
        pp_pattern_internal(true, pattern)
    }

    fn needs_tight_parens(expr: &Expr) -> bool {
        matches!(expr, Expr::If(_, _, _) | Expr::Let(_, _) | Expr::Match(_, _))
    }

    fn pp_expr_doc(expr: &Expr) -> Doc {
        fn tight_expr(expr: &Expr) -> Doc {
            if needs_tight_parens(expr) {
                parens(expr_doc(false, expr))
            } else {
                expr_doc(true, expr)
            }
        }

        fn expr_doc(c: bool, expr: &Expr) -> Doc {
            let wrap = |doc: Doc| if c { parens(doc) } else { doc };

            match expr {
                Expr::Unit => Doc::text("()"),
                Expr::Int(value) => Doc::text_owned(value.to_string()),
                Expr::Bool(true) => Doc::text("true"),
                Expr::Bool(false) => Doc::text("false"),
                Expr::Str(value) => dquotes(Doc::text_owned(escape_ocaml_string(value))),
                Expr::Builtin(name) => Doc::text_owned(name.clone()),
                Expr::Var(name) => Doc::text_owned(name.clone()),
                Expr::GVar(name) => Doc::text_owned(format!("global:{name}")),
                Expr::Ctor(name) => Doc::text_owned(name.clone()),
                Expr::App(fun, args) => {
                    if let Expr::Ctor(name) = fun.as_ref() {
                        if args.len() > 1 {
                            let tuple_arg = Expr::Tup(args.clone());
                            return expr_doc(
                                c,
                                &Expr::App(Box::new(Expr::Var(name.clone())), vec![tuple_arg]),
                            );
                        }
                    }

                    if args.is_empty() {
                        return expr_doc(c, fun);
                    }

                    let inner = tight_expr(fun)
                        .concat(Doc::text(" "))
                        .concat(separate_map(Doc::text(" "), args, tight_expr));
                    wrap(inner)
                }
                Expr::Op(op, lhs, rhs) => {
                    let inner = tight_expr(lhs)
                        .concat(Doc::text(" "))
                        .concat(Doc::text_owned(op.clone()))
                        .concat(Doc::text(" "))
                        .concat(tight_expr(rhs));
                    wrap(inner)
                }
                Expr::Tup(items) => {
                    let inner = separate_map(
                        Doc::text(",").concat(Doc::text(" ")),
                        items,
                        tight_expr,
                    );
                    parens(inner)
                }
                Expr::Arr(items) => {
                    let inner = separate_map(
                        Doc::text(";").concat(Doc::text(" ")),
                        items,
                        tight_expr,
                    );
                    brackets(inner)
                }
                Expr::Lam(patterns, body) => {
                    let inner = Doc::text("fun")
                        .concat(Doc::text(" "))
                        .concat(separate_map(
                            Doc::text(" "),
                            patterns,
                            pp_pattern_prime_doc,
                        ))
                        .concat(Doc::text(" "))
                        .concat(Doc::text("->"))
                        .concat(
                            Doc::brk(1)
                                .concat(expr_doc(true, body))
                                .nest(2),
                        )
                        .align()
                        .group();
                    wrap(inner)
                }
                Expr::Let(binding, tail) => match binding.as_ref() {
                    Binding::One(pattern, expr) => {
                        let fsb = |pro: Doc, lhs: Doc, rhs: Doc| {
                            pro.concat(Doc::text(" "))
                                .concat(lhs)
                                .concat(Doc::text(" "))
                                .concat(Doc::text("="))
                                .concat(Doc::brk(1).concat(rhs).nest(2))
                                .align()
                                .group()
                        };

                        let inner = fsb(
                            Doc::text("let"),
                            pp_pattern_doc(pattern),
                            expr_doc(false, expr),
                        )
                        .concat(Doc::brk(1))
                        .concat(Doc::text("in"))
                        .group()
                        .concat(Doc::brk(1))
                        .concat(expr_doc(false, tail))
                        .group()
                        .align();

                        inner
                    }
                    Binding::Seq(expr) => expr_doc(false, expr)
                        .align()
                        .concat(Doc::text(";"))
                        .concat(Doc::brk(1))
                        .concat(expr_doc(false, tail))
                        .align(),
                    Binding::Rec(bindings) => {
                        if bindings.is_empty() {
                            panic!("Empty recursive group");
                        }

                        let fsb = |pro: Doc, lhs: Doc, rhs: Doc| {
                            pro.concat(Doc::text(" "))
                                .concat(lhs)
                                .concat(Doc::text(" "))
                                .concat(Doc::text("="))
                                .concat(Doc::brk(1).concat(rhs).nest(2))
                                .align()
                                .group()
                        };

                        let mut docs = Vec::new();
                        for (idx, (pattern, expr)) in bindings.iter().enumerate() {
                            if idx != 0 {
                                docs.push(Doc::brk(1));
                            }
                            let pro =
                                if idx == 0 { Doc::text("let rec") } else { Doc::text("and") };
                            docs.push(fsb(pro, pp_pattern_doc(pattern), expr_doc(false, expr)));
                        }

                        let inner = concat_all(docs)
                            .concat(Doc::brk(1))
                            .concat(Doc::text("in"))
                            .group()
                            .concat(Doc::brk(1))
                            .concat(expr_doc(false, tail))
                            .group()
                            .align();

                        inner
                    }
                },
                Expr::Sel(expr, field) => tight_expr(expr)
                    .concat(Doc::text("."))
                    .concat(pp_field(field)),
                Expr::If(cond, then_branch, else_branch) => Doc::text("if")
                    .concat(Doc::brk(1).concat(expr_doc(true, cond)).nest(2))
                    .group()
                    .concat(Doc::brk(1))
                    .concat(Doc::text("then"))
                    .concat(Doc::brk(1).concat(expr_doc(true, then_branch)).nest(2))
                    .concat(Doc::brk(1))
                    .concat(Doc::text("else"))
                    .concat(Doc::brk(1).concat(expr_doc(true, else_branch)).nest(2))
                    .align()
                    .group(),
                Expr::Match(target, cases) => {
                    let fm = |e: &Expr, inf: Doc| {
                        Doc::text("match")
                            .concat(Doc::text(" "))
                            .concat(expr_doc(false, e))
                            .concat(Doc::text(" "))
                            .concat(Doc::text("with"))
                            .concat(inf)
                            .align()
                            .group()
                    };

                    let fc = |case: &(Pattern, Expr)| {
                        let (pattern, expr) = case;
                        Doc::brk(1)
                            .concat(
                                Doc::text("|")
                                    .concat(Doc::text(" "))
                                    .concat(pp_pattern_doc(pattern))
                                    .concat(Doc::text(" "))
                                    .concat(Doc::text("->"))
                                    .concat(Doc::brk(1).concat(expr_doc(true, expr)).nest(2))
                                    .align()
                                    .group(),
                            )
                    };

                    let cases_doc = concat_map(cases, fc);
                    fm(target, cases_doc)
                }
            }
        }

        expr_doc(false, expr)
    }

    fn pp_ty_doc(ty: &Ty) -> Doc {
        fn ty_doc(c: bool, ty: &Ty) -> Doc {
            let wrap = |doc: Doc| if c { parens(doc) } else { doc };
            match ty {
                Ty::Unit => Doc::text("unit"),
                Ty::Int => Doc::text("int"),
                Ty::Float => Doc::text("float"),
                Ty::Bool => Doc::text("bool"),
                Ty::Named(name) => Doc::text_owned(name.clone()),
                Ty::NamedVar(name) => Doc::text_owned(format!("'{name}")),
                Ty::Apply(base, args) => {
                    if args.is_empty() {
                        return ty_doc(c, base);
                    }

                    let args_doc = if args.len() > 1 {
                        parens(separate_map(Doc::text(","), args, |t| ty_doc(true, t)))
                    } else {
                        separate_map(Doc::text(","), args, |t| ty_doc(true, t))
                    };
                    wrap(args_doc.concat(Doc::text(" ")).concat(ty_doc(c, base)))
                }
                Ty::Arrow(lhs, rhs) => wrap(
                    ty_doc(true, lhs)
                        .concat(Doc::text(" "))
                        .concat(Doc::text("->"))
                        .concat(Doc::text(" "))
                        .concat(ty_doc(true, rhs)),
                ),
                Ty::Tuple(items) => parens(separate_map(Doc::text("*"), items, |t| ty_doc(true, t))),
            }
        }

        ty_doc(false, ty)
    }

    fn pp_type_params(params: &[String]) -> Doc {
        if params.is_empty() {
            Doc::nil()
        } else if params.len() == 1 {
            Doc::text_owned(format!("'{} ", params[0]))
        } else {
            let inner = separate_map(
                Doc::text(","),
                params,
                |param| Doc::text_owned(format!("'{param}")),
            );
            parens(inner).concat(Doc::text(" "))
        }
    }

    fn pp_ctor(ctor: &TyCtor) -> Doc {
        if ctor.args.is_empty() {
            Doc::text_owned(ctor.name.clone())
        } else {
            Doc::text_owned(ctor.name.clone())
                .concat(Doc::text(" "))
                .concat(Doc::text("of"))
                .concat(Doc::text(" "))
                .concat(separate_map(
                    Doc::text(" ").concat(Doc::text("*")).concat(Doc::text(" ")),
                    &ctor.args,
                    pp_ty_doc,
                ))
        }
    }

    fn pp_enum(is_and: bool, name: &str, params: &[String], ctors: &[TyCtor]) -> Doc {
        let header = if is_and { Doc::text("and") } else { Doc::text("type") }
            .concat(Doc::text(" "))
            .concat(pp_type_params(params))
            .concat(Doc::text_owned(name.to_string()))
            .concat(Doc::text(" "))
            .concat(Doc::text("="))
            .concat(
                Doc::brk(1)
                    .concat(Doc::text("|"))
                    .concat(Doc::text(" "))
                    .concat(separate_map(
                        Doc::brk(1).concat(Doc::text("|")).concat(Doc::text(" ")),
                        ctors,
                        pp_ctor,
                    ))
                    .nest(2),
            )
            .align()
            .group();
        header
    }

    fn pp_type_binding(binding: &TyBinding) -> Doc {
        match binding {
            TyBinding::One { name, kind } => match kind {
                TyKind::Enum { params, ctors } => pp_enum(false, name, params, ctors).concat(Doc::text(";;")),
            },
            TyBinding::Rec(groups) => {
                let mut docs = Vec::new();
                for (idx, (name, kind)) in groups.iter().enumerate() {
                    let TyKind::Enum { params, ctors } = kind;
                    if idx != 0 {
                        docs.push(Doc::brk(1));
                    }
                    docs.push(pp_enum(idx != 0, name, params, ctors));
                }
                concat_all(docs).concat(Doc::text(";;"))
            }
        }
    }

    fn pp_term_binding(binding: &Binding) -> Doc {
        match binding {
            Binding::Seq(expr) => Doc::text("let")
                .concat(Doc::text(" "))
                .concat(Doc::text("_"))
                .concat(Doc::text(" "))
                .concat(Doc::text("="))
                .concat(Doc::brk(1).concat(pp_expr_doc(expr).group()).nest(2))
                .concat(Doc::text(";;")),
            Binding::One(pattern, expr) => Doc::text("let")
                .concat(Doc::text(" "))
                .concat(pp_pattern_doc(pattern))
                .concat(Doc::text(" "))
                .concat(Doc::text("="))
                .concat(Doc::brk(1).concat(pp_expr_doc(expr).group()).nest(2))
                .concat(Doc::text(";;")),
            Binding::Rec(bindings) => {
                let mut docs = Vec::new();
                docs.push(Doc::text("let rec"));
                docs.push(Doc::text(" "));
                for (idx, (pattern, expr)) in bindings.iter().enumerate() {
                    if idx != 0 {
                        docs.push(Doc::text(" "));
                        docs.push(Doc::text("and"));
                        docs.push(Doc::text(" "));
                    }
                    docs.push(
                        pp_pattern_doc(pattern)
                            .concat(Doc::text(" "))
                            .concat(Doc::text("="))
                            .concat(Doc::brk(1).concat(pp_expr_doc(expr).group()).nest(2)),
                    );
                }
                concat_all(docs).concat(Doc::text(";;"))
            }
        }
    }

    fn pp_stmt_doc(stmt: &Stmt) -> Doc {
        match stmt {
            Stmt::Type(binding) => pp_type_binding(binding),
            Stmt::Term(binding) => pp_term_binding(binding),
        }
    }

    pub(super) fn pp_prog(prog: &Prog) -> String {
        let stmts = prog.stmts();
        let doc = separate_map(Doc::brk(1), stmts, pp_stmt_doc);
        render(doc)
    }

    pub(super) fn pp_stmt(stmt: &Stmt) -> String {
        render(pp_stmt_doc(stmt))
    }

    pub(super) fn pp_expr(expr: &Expr, c: bool) -> String {
        let doc = pp_expr_doc(expr);
        let doc = if c { parens(doc) } else { doc };
        render(doc)
    }

    pub(super) fn pp_pattern(pattern: &Pattern, c: bool) -> String {
        render(pp_pattern_internal(c, pattern))
    }
}
