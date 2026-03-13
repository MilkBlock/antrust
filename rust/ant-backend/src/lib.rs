use ant_frontend::{Binding, Expr, Field, Pattern, Prog, Stmt, Ty, TyBinding, TyCtor, TyKind};
use std::collections::HashMap;
use std::fmt;

mod compile_memo;
pub use compile_memo::compile_memo;

#[derive(Debug, Clone)]
pub struct BackendError {
    message: String,
}

impl BackendError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for BackendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for BackendError {}

pub fn compile_plain(prog: &Prog) -> Result<String, BackendError> {
    let mut parts = Vec::new();
    for stmt in prog.stmts() {
        parts.push(compile_stmt(stmt)?);
    }
    Ok(parts.join(";;\n\n"))
}

fn is_ignore_pat(pat: &Pattern) -> bool {
    matches!(pat, Pattern::Any) || matches!(pat, Pattern::Var(name) if name == "_")
}

fn compile_stmt(stmt: &Stmt) -> Result<String, BackendError> {
    match stmt {
        Stmt::Type(binding) => Ok(compile_type_binding(binding)),
        Stmt::Term(binding) => match binding {
            Binding::Seq(expr) => Ok(compile_expr(expr)),
            Binding::One(pat, expr) => {
                if is_ignore_pat(pat) {
                    Ok(format!("let () = ignore {}", parens_compile_expr(expr)))
                } else {
                    Ok(format!(
                        "let rec {} = {}",
                        parens_compile_pat(pat),
                        compile_expr(expr)
                    ))
                }
            }
            Binding::Rec(bindings) => {
                if bindings.len() == 1 {
                    let (pat, expr) = &bindings[0];
                    Ok(format!(
                        "let rec {} = {}",
                        parens_compile_pat(pat),
                        compile_expr(expr)
                    ))
                } else {
                    Err(BackendError::new(
                        "compile_plain does not support multi-binding let rec",
                    ))
                }
            }
        },
    }
}

fn compile_type_binding(binding: &TyBinding) -> String {
    match binding {
        TyBinding::One { name, kind } => format!("type {}", compile_type_decl(name, kind)),
        TyBinding::Rec(decls) => {
            let parts: Vec<String> = decls
                .iter()
                .map(|(name, kind)| compile_type_decl(name, kind))
                .collect();
            format!("type {}", parts.join("\nand "))
        }
    }
}

fn compile_type_decl(name: &str, kind: &TyKind) -> String {
    match kind {
        TyKind::Enum { params, ctors } => {
            let mut out = String::new();
            out.push_str(name);
            out.push(' ');
            if !params.is_empty() {
                out.push_str(&params.join(" "));
            }
            out.push_str(" = ");
            let ctors_str = ctors.iter().map(compile_ctor).collect::<Vec<_>>().join("| ");
            out.push_str(&ctors_str);
            out
        }
    }
}

fn compile_ctor(ctor: &TyCtor) -> String {
    if ctor.args.is_empty() {
        ctor.name.clone()
    } else {
        let args = ctor
            .args
            .iter()
            .map(|ty| format!("({})", compile_ty(ty)))
            .collect::<Vec<_>>()
            .join(" * ");
        format!("{} of {}", ctor.name, args)
    }
}

fn compile_ty(ty: &Ty) -> String {
    match ty {
        Ty::Unit => "unit".to_string(),
        Ty::Int => "int".to_string(),
        Ty::Float => "float".to_string(),
        Ty::Bool => "bool".to_string(),
        Ty::Apply(base, args) => {
            if args.is_empty() {
                compile_ty(base)
            } else {
                let args_str = args
                    .iter()
                    .map(compile_ty)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({}) {}", args_str, compile_ty(base))
            }
        }
        Ty::Arrow(lhs, rhs) => format!("{} -> {}", compile_ty(lhs), compile_ty(rhs)),
        Ty::Tuple(items) => format!(
            "({})",
            items.iter().map(compile_ty).collect::<Vec<_>>().join(", ")
        ),
        Ty::Named(name) => name.clone(),
        Ty::NamedVar(name) => name.clone(),
    }
}

fn compile_pat(pat: &Pattern) -> String {
    match pat {
        Pattern::Any => "_".to_string(),
        Pattern::Int(value) => value.to_string(),
        Pattern::Bool(value) => value.to_string(),
        Pattern::Var(name) => name.clone(),
        Pattern::Unit => "()".to_string(),
        Pattern::Tup(items) => format!(
            "({})",
            items
                .iter()
                .map(compile_pat)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Pattern::CtorApp { name, args } => match args {
            None => name.clone(),
            Some(args) => {
                let inner = if args.len() == 1 {
                    compile_pat(&args[0])
                } else {
                    compile_pat(&Pattern::Tup(args.clone()))
                };
                format!("{} {}", name, inner)
            }
        },
    }
}

fn parens_compile_pat(pat: &Pattern) -> String {
    format!("({})", compile_pat(pat))
}

fn compile_expr(expr: &Expr) -> String {
    match expr {
        Expr::Unit => "()".to_string(),
        Expr::Int(value) => value.to_string(),
        Expr::Bool(value) => value.to_string(),
        Expr::Str(value) => value.clone(),
        Expr::Builtin(name) => name.clone(),
        Expr::Var(name) => name.clone(),
        Expr::GVar(name) => name.clone(),
        Expr::Ctor(name) => name.clone(),
        Expr::App(fun, args) => {
            if let Expr::Ctor(name) = &**fun {
                let args_str = args
                    .iter()
                    .map(parens_compile_expr)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{} ({})", name, args_str)
            } else {
                let fun_str = parens_compile_expr(fun);
                if args.is_empty() {
                    fun_str
                } else {
                    let args_str = args
                        .iter()
                        .map(parens_compile_expr)
                        .collect::<Vec<_>>()
                        .join(" ");
                    format!("{} {}", fun_str, args_str)
                }
            }
        }
        Expr::Op(op, lhs, rhs) => format!(
            "({}{}{})",
            parens_compile_expr(lhs),
            op,
            parens_compile_expr(rhs)
        ),
        Expr::Tup(items) => format!(
            "({})",
            items
                .iter()
                .map(compile_expr)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Expr::Arr(items) => format!(
            "[]{}]",
            items
                .iter()
                .map(compile_expr)
                .collect::<Vec<_>>()
                .join("; ")
        ),
        Expr::Lam(pats, value) => {
            let pat_str = pats
                .iter()
                .map(parens_compile_pat)
                .collect::<Vec<_>>()
                .join(" ");
            format!("fun {} -> {}", pat_str, parens_compile_expr(value))
        }
        Expr::Let(binding, value) => compile_binding(binding, parens_compile_expr(value)),
        Expr::Sel(expr, field) => format!("{}.{}", parens_compile_expr(expr), compile_field(field)),
        Expr::If(cond, then_branch, else_branch) => format!(
            "if {} then {} else {}",
            compile_expr(cond),
            parens_compile_expr(then_branch),
            parens_compile_expr(else_branch)
        ),
        Expr::Match(target, cases) => {
            let cases_str = cases
                .iter()
                .map(|(pat, expr)| {
                    format!("{} -> {}", parens_compile_pat(pat), parens_compile_expr(expr))
                })
                .collect::<Vec<_>>()
                .join("| ");
            format!("match {} with {}", compile_expr(target), cases_str)
        }
    }
}

fn parens_compile_expr(expr: &Expr) -> String {
    format!("({})", compile_expr(expr))
}

fn compile_binding(binding: &Binding, cont: String) -> String {
    match binding {
        Binding::Seq(expr) => format!("{};{}", compile_expr(expr), cont),
        Binding::One(pat, expr) => {
            format!("let {} in {}", compile_let(pat, expr), cont)
        }
        Binding::Rec(bindings) => {
            let parts = bindings
                .iter()
                .map(|(pat, expr)| compile_let(pat, expr))
                .collect::<Vec<_>>()
                .join(" and ");
            format!("let rec {} in {}", parts, cont)
        }
    }
}

fn compile_let(pat: &Pattern, expr: &Expr) -> String {
    format!("{} = ({})", parens_compile_pat(pat), compile_expr(expr))
}

fn compile_field(field: &Field) -> String {
    match field {
        Field::Name(name) => name.clone(),
        Field::Index(idx) => idx.to_string(),
    }
}

pub fn compile_seq(prog: &Prog) -> Result<String, BackendError> {
    let mut env = SeqEnv::new();
    let mut parts = Vec::new();
    parts.push("open Ant".to_string());
    parts.push("module Word = Seq.Word".to_string());
    for stmt in prog.stmts() {
        let doc = match stmt {
            Stmt::Type(binding) => compile_seq_type(binding, &mut env)?,
            Stmt::Term(binding) => compile_seq_term(binding, &env)?,
        };
        parts.push(doc);
    }
    Ok(parts.join("\n"))
}

struct SeqEnv {
    next_tag: i32,
    tags: HashMap<String, i32>,
    ctor_owner: HashMap<String, String>,
    primary_type: Option<String>,
}

impl SeqEnv {
    fn new() -> Self {
        Self {
            next_tag: 0,
            tags: HashMap::new(),
            ctor_owner: HashMap::new(),
            primary_type: None,
        }
    }

    fn register_ctor(&mut self, owner: &str, name: &str) -> Result<i32, BackendError> {
        if self.tags.contains_key(name) {
            return Err(BackendError::new(format!(
                "duplicate constructor tag: {name}"
            )));
        }
        let tag = self.next_tag;
        self.next_tag += 1;
        self.tags.insert(name.to_string(), tag);
        self.ctor_owner.insert(name.to_string(), owner.to_string());
        Ok(tag)
    }

    fn tag_for(&self, name: &str) -> Result<i32, BackendError> {
        self.tags
            .get(name)
            .copied()
            .ok_or_else(|| BackendError::new(format!("unknown constructor tag: {name}")))
    }

    fn owner_for(&self, name: &str) -> Result<&str, BackendError> {
        self.ctor_owner
            .get(name)
            .map(|s| s.as_str())
            .ok_or_else(|| BackendError::new(format!("unknown constructor: {name}")))
    }

    fn register_type(&mut self, name: &str) {
        if self.primary_type.is_none() {
            self.primary_type = Some(name.to_string());
        }
    }
}

fn compile_seq_type(binding: &TyBinding, env: &mut SeqEnv) -> Result<String, BackendError> {
    match binding {
        TyBinding::One { name, kind } => match kind {
            TyKind::Enum { ctors, .. } => {
                env.register_type(name);
                let mut lines = Vec::new();
                lines.push(format!("type ocaml_{name} ="));
                for ctor in ctors {
                    let ctor_doc = if ctor.args.is_empty() {
                        ctor.name.clone()
                    } else {
                        let args = ctor
                            .args
                            .iter()
                            .map(compile_seq_ty)
                            .collect::<Result<Vec<_>, _>>()?
                            .join(" * ");
                        format!("{} of {}", ctor.name, args)
                    };
                    lines.push(format!("  | {}", ctor_doc));
                }

                for ctor in ctors {
                    let arity = ctor.args.len();
                    let tag = env.register_ctor(name, &ctor.name)?;
                    let degree = 1 - (arity as i32);
                    let degree_str = if degree < 0 {
                        format!("({})", degree)
                    } else {
                        degree.to_string()
                    };
                    lines.push(format!(
                        "let () = (Seq.set_constructor_degree {} {})",
                        tag, degree_str
                    ));

                    let params = (0..arity).map(|i| format!("x{}", i)).collect::<Vec<_>>();
                    let params_str = if params.is_empty() {
                        String::new()
                    } else {
                        format!(" {}", params.join(" "))
                    };
                    let mut parts = Vec::new();
                    parts.push(format!("(Seq.from_constructor {})", tag));
                    for (idx, ty) in ctor.args.iter().enumerate() {
                        let var = format!("x{}", idx);
                        let part = match ty {
                            Ty::Int => Ok(format!("(Seq.from_int {})", var)),
                            Ty::Named(_) | Ty::Apply(_, _) => Ok(var),
                            _ => Err(BackendError::new(format!(
                                "unsupported type in seq ctor: {ty:?}"
                            ))),
                        }?;
                        parts.push(part);
                    }
                    let appends = format!("(Seq.appends [{}])", parts.join("; "));
                    lines.push(format!(
                        "let {name}_{}{} : Seq.seq = {}",
                        ctor.name, params_str, appends
                    ));
                }

                lines.push(format!("let from_ocaml_{name} x ="));
                lines.push("  match x with".to_string());
                for ctor in ctors {
                    let arity = ctor.args.len();
                    if arity == 0 {
                        lines.push(format!("  | {} -> {name}_{}", ctor.name, ctor.name));
                    } else {
                        let params = (0..arity).map(|i| format!("x{}", i)).collect::<Vec<_>>();
                        let pat = format!("{}({})", ctor.name, params.join(", "));
                        let args = params.join(" ");
                        lines.push(format!("  | {} -> {name}_{} {}", pat, ctor.name, args));
                    }
                }

                lines.push(format!("let to_ocaml_{name} x ="));
                lines.push("  let (h, t) = (Option.get (Seq.list_match x)) in".to_string());
                lines.push("  match ((Word.get_value h)) with".to_string());
                for ctor in ctors {
                    let arity = ctor.args.len();
                    let tag = env.tag_for(&ctor.name)?;
                    if arity == 0 {
                        lines.push(format!("  | {} -> {}", tag, ctor.name));
                    } else {
                        let params = (0..arity).map(|i| format!("x{}", i)).collect::<Vec<_>>();
                        lines.push(format!("  | {} ->", tag));
                        lines.push(format!(
                            "    let [{}] = (Seq.splits t) in",
                            params.join("; ")
                        ));
                        let args = ctor
                            .args
                            .iter()
                            .enumerate()
                            .map(|(idx, ty)| {
                                let var = format!("x{}", idx);
                                match ty {
                                    Ty::Int => Ok(format!("(Seq.to_int {})", var)),
                                    Ty::Named(_) | Ty::Apply(_, _) => Ok(var),
                                    _ => Err(BackendError::new(format!(
                                        "unsupported type in seq ctor: {ty:?}"
                                    ))),
                                }
                            })
                            .collect::<Result<Vec<_>, _>>()?
                            .join(", ");
                        lines.push(format!("    {}({})", ctor.name, args));
                    }
                }
                lines.push("  | _ -> failwith \"unreachable\"".to_string());
                Ok(lines.join("\n"))
            }
        },
        TyBinding::Rec(_) => Err(BackendError::new(
            "compile_seq does not support recursive type bindings",
        )),
    }
}

fn compile_seq_ty(ty: &Ty) -> Result<String, BackendError> {
    match ty {
        Ty::Int => Ok("int".to_string()),
        Ty::Named(_) | Ty::Apply(_, _) => Ok("Seq.seq".to_string()),
        _ => Err(BackendError::new(format!(
            "unsupported type in seq: {ty:?}"
        ))),
    }
}

fn compile_seq_term(binding: &Binding, env: &SeqEnv) -> Result<String, BackendError> {
    match binding {
        Binding::Seq(expr) => compile_seq_expr(expr, env),
        Binding::One(pat, expr) => {
            if is_ignore_pat(pat) {
                Ok(format!(
                    "let () = ignore ({});;",
                    compile_seq_expr(expr, env)?
                ))
            } else {
                Ok(format!(
                    "let rec {} = {};;",
                    pp_pattern_seq(pat, false),
                    compile_seq_expr(expr, env)?
                ))
            }
        }
        Binding::Rec(bindings) => {
            let mut parts = Vec::new();
            for (pat, expr) in bindings {
                parts.push(format!(
                    "{} = {}",
                    pp_pattern_seq(pat, false),
                    compile_seq_expr(expr, env)?
                ));
            }
            Ok(format!("let rec {};;", parts.join(" and ")))
        }
    }
}

fn find_ctor_owner(env: &SeqEnv, pat: &Pattern) -> Option<String> {
    match pat {
        Pattern::CtorApp { name, .. } => env.owner_for(name).ok().map(|s| s.to_string()),
        Pattern::Tup(items) => items.iter().find_map(|p| find_ctor_owner(env, p)),
        _ => None,
    }
}

fn is_primitive_pat(pat: &Pattern) -> bool {
    matches!(
        pat,
        Pattern::Any | Pattern::Int(_) | Pattern::Bool(_) | Pattern::Unit | Pattern::Var(_)
    )
}

fn match_owner_from_cases(env: &SeqEnv, cases: &[(Pattern, Expr)]) -> Result<String, BackendError> {
    for (pat, _) in cases {
        if let Some(owner) = find_ctor_owner(env, pat) {
            return Ok(owner);
        }
    }
    env.primary_type
        .clone()
        .ok_or_else(|| BackendError::new("cannot determine seq match type"))
}

fn compile_seq_expr(expr: &Expr, env: &SeqEnv) -> Result<String, BackendError> {
    match expr {
        Expr::Lam(params, body) => {
            let params_str = params
                .iter()
                .map(|pat| pp_pattern_seq(pat, true))
                .collect::<Vec<_>>()
                .join(" ");
            Ok(format!("fun {} -> {}", params_str, compile_seq_expr(body, env)?))
        }
        Expr::Match(value, cases) => {
            let value_str = compile_seq_expr(value, env)?;
            let primitive_match = cases.iter().all(|(pat, _)| is_primitive_pat(pat));
            let owner = if primitive_match {
                None
            } else {
                Some(match_owner_from_cases(env, cases)?)
            };
            let owner_ref = owner.as_deref();
            let mut out = if let Some(owner) = owner_ref {
                format!(
                    "match (to_ocaml_{owner} {}) with | {}",
                    value_str,
                    compile_seq_case(&cases[0], env, owner_ref)?
                )
            } else {
                format!(
                    "match ({}) with | {}",
                    value_str,
                    compile_seq_case(&cases[0], env, owner_ref)?
                )
            };
            for case in cases.iter().skip(1) {
                out.push('\n');
                out.push('|');
                out.push_str(&compile_seq_case(case, env, owner_ref)?);
            }
            Ok(out)
        }
        Expr::Ctor(name) => {
            let owner = env.owner_for(name)?;
            Ok(format!("{owner}_{name}"))
        }
        Expr::Var(name) => Ok(name.clone()),
        Expr::GVar(name) => Ok(name.clone()),
        Expr::App(fun, args) => {
            if let Expr::Ctor(name) = &**fun {
                let owner = env.owner_for(name)?;
                if args.is_empty() {
                    Ok(format!("{owner}_{name}"))
                } else {
                    let mut parts = Vec::new();
                    for arg in args {
                        parts.push(compile_seq_expr(arg, env)?);
                    }
                    Ok(format!("{owner}_{name}({})", parts.join(",")))
                }
            } else {
                let mut parts = Vec::new();
                parts.push(compile_seq_expr(fun, env)?);
                for arg in args {
                    parts.push(compile_seq_expr(arg, env)?);
                }
                Ok(format!("({})", parts.join(" ")))
            }
        }
        Expr::Op(op, lhs, rhs) => Ok(format!(
            "({}{}{})",
            compile_seq_expr(lhs, env)?,
            op,
            compile_seq_expr(rhs, env)?
        )),
        Expr::Int(value) => Ok(format!("({})", value)),
        _ => Err(BackendError::new(format!(
            "unsupported expr in seq backend: {expr:?}"
        ))),
    }
}

fn compile_seq_case(
    case: &(Pattern, Expr),
    env: &SeqEnv,
    owner: Option<&str>,
) -> Result<String, BackendError> {
    let (pat, expr) = case;
    let mut expr_str = compile_seq_expr(expr, env)?;
    if let (Some(owner), Pattern::Var(name)) = (owner, pat) {
        expr_str = format!("let {name} = from_ocaml_{owner} {name} in {expr_str}");
    }
    Ok(format!(
        "{} -> {}",
        pp_pattern_seq(pat, false),
        expr_str
    ))
}

fn pp_pattern_seq(pat: &Pattern, c: bool) -> String {
    match pat {
        Pattern::Any => "_".to_string(),
        Pattern::Int(value) => value.to_string(),
        Pattern::Bool(value) => value.to_string(),
        Pattern::Unit => "()".to_string(),
        Pattern::Var(name) => name.clone(),
        Pattern::CtorApp { name, args } => match args {
            None => name.clone(),
            Some(args) => {
                let arg_pat = if args.len() == 1 {
                    args[0].clone()
                } else {
                    Pattern::Tup(args.clone())
                };
                let inner = format!("{} {}", name, pp_pattern_seq(&arg_pat, true));
                if c {
                    format!("({})", inner)
                } else {
                    inner
                }
            }
        },
        Pattern::Tup(items) => {
            let inner = items
                .iter()
                .map(|p| pp_pattern_seq(p, true))
                .collect::<Vec<_>>()
                .join(", ");
            if c {
                format!("({})", inner)
            } else {
                inner
            }
        }
    }
}
