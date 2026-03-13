use crate::BackendError;
use ant_frontend::{Binding, Expr, Field, Pattern, Prog, Stmt, Ty, TyBinding, TyCtor, TyKind};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

thread_local! {
    static GENSYM: RefCell<HashMap<String, usize>> = RefCell::new(HashMap::new());
}

fn reset_gensym() {
    GENSYM.with(|g| g.borrow_mut().clear());
}

fn gensym(base: &str) -> String {
    GENSYM.with(|g| {
        let mut map = g.borrow_mut();
        let n = map.get(base).copied().unwrap_or(0);
        map.insert(base.to_string(), n + 1);
        format!("{base}_{n}")
    })
}

#[derive(Clone, Debug)]
struct Info {
    tail: bool,
    fv: BTreeSet<String>,
}

#[derive(Clone, Debug)]
struct AExpr {
    kind: AExprKind,
    info: Info,
}

#[derive(Clone, Debug)]
enum AExprKind {
    Unit,
    Int(i64),
    Bool(bool),
    Str(String),
    Builtin(String),
    Var(String),
    GVar(String),
    Ctor(String),
    App(Box<AExpr>, Vec<AExpr>),
    Op(String, Box<AExpr>, Box<AExpr>),
    Tup(Vec<AExpr>),
    Arr(Vec<AExpr>),
    Lam(Vec<Pattern>, Box<AExpr>),
    Let(Box<ABinding>, Box<AExpr>),
    Sel(Box<AExpr>, Field),
    If(Box<AExpr>, Box<AExpr>, Box<AExpr>),
    Match(Box<AExpr>, Vec<(Pattern, AExpr)>),
}

#[derive(Clone, Debug)]
enum ABinding {
    Seq(Box<AExpr>),
    One(Pattern, Box<AExpr>),
    Rec(Vec<(Pattern, Box<AExpr>)>),
}

#[derive(Clone, Debug)]
enum AStmt {
    Type(TyBinding),
    Term(ABinding),
}

#[derive(Clone, Debug, Default)]
struct FvSet(BTreeSet<String>);

impl FvSet {
    fn empty() -> Self {
        Self(BTreeSet::new())
    }

    fn add(&self, name: &str) -> Self {
        let mut out = self.0.clone();
        out.insert(name.to_string());
        Self(out)
    }

    fn remove(&self, name: &str) -> Self {
        let mut out = self.0.clone();
        out.remove(name);
        Self(out)
    }

    fn union(&self, other: &Self) -> Self {
        let mut out = self.0.clone();
        out.extend(other.0.iter().cloned());
        Self(out)
    }

    fn unions(sets: &[Self]) -> Self {
        let mut out = BTreeSet::new();
        for set in sets {
            out.extend(set.0.iter().cloned());
        }
        Self(out)
    }
}

fn annotate_pattern(pat: &Pattern, fv_after: &FvSet) -> (Pattern, FvSet) {
    match pat {
        Pattern::Var(name) => (pat.clone(), fv_after.remove(name)),
        Pattern::Tup(items) => {
            let mut acc = Vec::with_capacity(items.len());
            let mut fv_tail = fv_after.clone();
            for item in items.iter().rev() {
                let (p, fv_before) = annotate_pattern(item, &fv_tail);
                acc.push(p);
                fv_tail = fv_before;
            }
            acc.reverse();
            (Pattern::Tup(acc), fv_tail)
        }
        Pattern::CtorApp { name, args } => match args {
            None => (pat.clone(), fv_after.clone()),
            Some(args) => {
                let (payload, fv_before) = annotate_pattern_list(args, fv_after);
                (
                    Pattern::CtorApp {
                        name: name.clone(),
                        args: Some(payload),
                    },
                    fv_before,
                )
            }
        },
        _ => (pat.clone(), fv_after.clone()),
    }
}

fn annotate_pattern_list(patterns: &[Pattern], fv_after: &FvSet) -> (Vec<Pattern>, FvSet) {
    let mut acc = Vec::with_capacity(patterns.len());
    let mut fv_tail = fv_after.clone();
    for pat in patterns.iter().rev() {
        let (p, fv_before) = annotate_pattern(pat, &fv_tail);
        acc.push(p);
        fv_tail = fv_before;
    }
    acc.reverse();
    (acc, fv_tail)
}

fn annotate_expr_list(exprs: &[Expr], is_tail: bool, fv_after: &FvSet) -> Result<(Vec<AExpr>, FvSet), BackendError> {
    let mut acc = Vec::with_capacity(exprs.len());
    let mut fv_tail = fv_after.clone();
    for expr in exprs.iter().rev() {
        let (expr_annotated, fv_before) = annotate_expr(expr, is_tail, &fv_tail)?;
        acc.push(expr_annotated);
        fv_tail = fv_before;
    }
    acc.reverse();
    Ok((acc, fv_tail))
}

fn annotate_cases(
    cases: &[(Pattern, Expr)],
    is_tail: bool,
    fv_after: &FvSet,
) -> Result<(Vec<(Pattern, AExpr)>, FvSet), BackendError> {
    let mut annotated = Vec::with_capacity(cases.len());
    let mut branch_reqs = Vec::with_capacity(cases.len());
    for (pat, expr) in cases.iter().rev() {
        let (expr_annotated, fv_before_expr) = annotate_expr(expr, is_tail, fv_after)?;
        let (pat_annotated, fv_before_pat) = annotate_pattern(pat, &fv_before_expr);
        annotated.push((pat_annotated, expr_annotated));
        branch_reqs.push(fv_before_pat);
    }
    annotated.reverse();
    let fv_cases = FvSet::unions(&branch_reqs);
    Ok((annotated, fv_cases))
}

fn annotate_binding(binding: &Binding, fv_after: &FvSet) -> Result<(ABinding, FvSet), BackendError> {
    match binding {
        Binding::Seq(expr) => {
            let (expr_annotated, fv_before) = annotate_expr(expr, false, fv_after)?;
            Ok((ABinding::Seq(Box::new(expr_annotated)), fv_before))
        }
        Binding::One(pat, expr) => {
            let (pat_annotated, fv_for_expr) = annotate_pattern(pat, fv_after);
            let (expr_annotated, fv_before) = annotate_expr(expr, false, &fv_for_expr)?;
            Ok((
                ABinding::One(pat_annotated, Box::new(expr_annotated)),
                fv_before,
            ))
        }
        Binding::Rec(entries) => {
            let mut annotated = Vec::with_capacity(entries.len());
            let mut fv_tail = fv_after.clone();
            for (pat, expr) in entries.iter().rev() {
                let (pat_annotated, fv_for_expr) = annotate_pattern(pat, &fv_tail);
                let (expr_annotated, fv_before) = annotate_expr(expr, false, &fv_for_expr)?;
                annotated.push((pat_annotated, Box::new(expr_annotated)));
                fv_tail = fv_before;
            }
            annotated.reverse();
            Ok((ABinding::Rec(annotated), fv_tail))
        }
    }
}

fn annotate_expr(expr: &Expr, is_tail: bool, fv_after: &FvSet) -> Result<(AExpr, FvSet), BackendError> {
    let info = |fv: &FvSet| Info {
        tail: is_tail,
        fv: fv.0.clone(),
    };
    match expr {
        Expr::Unit => Ok((AExpr { kind: AExprKind::Unit, info: info(fv_after) }, fv_after.clone())),
        Expr::Int(value) => Ok((
            AExpr {
                kind: AExprKind::Int(*value),
                info: info(fv_after),
            },
            fv_after.clone(),
        )),
        Expr::Bool(value) => Ok((
            AExpr {
                kind: AExprKind::Bool(*value),
                info: info(fv_after),
            },
            fv_after.clone(),
        )),
        Expr::Str(value) => Ok((
            AExpr {
                kind: AExprKind::Str(value.clone()),
                info: info(fv_after),
            },
            fv_after.clone(),
        )),
        Expr::Builtin(name) => Ok((
            AExpr {
                kind: AExprKind::Builtin(name.clone()),
                info: info(fv_after),
            },
            fv_after.clone(),
        )),
        Expr::Var(name) => Ok((
            AExpr {
                kind: AExprKind::Var(name.clone()),
                info: info(fv_after),
            },
            fv_after.add(name),
        )),
        Expr::GVar(name) => Ok((
            AExpr {
                kind: AExprKind::GVar(name.clone()),
                info: info(fv_after),
            },
            fv_after.clone(),
        )),
        Expr::Ctor(name) => Ok((
            AExpr {
                kind: AExprKind::Ctor(name.clone()),
                info: info(fv_after),
            },
            fv_after.clone(),
        )),
        Expr::App(fun, args) => {
            let (args_annotated, fv_for_fun) = annotate_expr_list(args, false, fv_after)?;
            let (fun_annotated, fv_before) = annotate_expr(fun, false, &fv_for_fun)?;
            Ok((
                AExpr {
                    kind: AExprKind::App(Box::new(fun_annotated), args_annotated),
                    info: info(fv_after),
                },
                fv_before,
            ))
        }
        Expr::Op(op, lhs, rhs) => {
            let (rhs_annotated, fv_for_lhs) = annotate_expr(rhs, false, fv_after)?;
            let (lhs_annotated, fv_before) = annotate_expr(lhs, false, &fv_for_lhs)?;
            Ok((
                AExpr {
                    kind: AExprKind::Op(op.clone(), Box::new(lhs_annotated), Box::new(rhs_annotated)),
                    info: info(fv_after),
                },
                fv_before,
            ))
        }
        Expr::Tup(values) => {
            let (values_annotated, fv_before) = annotate_expr_list(values, false, fv_after)?;
            Ok((
                AExpr {
                    kind: AExprKind::Tup(values_annotated),
                    info: info(fv_after),
                },
                fv_before,
            ))
        }
        Expr::Arr(values) => {
            let (values_annotated, fv_before) = annotate_expr_list(values, false, fv_after)?;
            Ok((
                AExpr {
                    kind: AExprKind::Arr(values_annotated),
                    info: info(fv_after),
                },
                fv_before,
            ))
        }
        Expr::Lam(params, body) => {
            let (body_annotated, fv_body_entry) = annotate_expr(body, true, &FvSet::empty())?;
            let (params_annotated, fv_closure) = annotate_pattern_list(params, &fv_body_entry);
            let fv_total = fv_after.union(&fv_closure);
            Ok((
                AExpr {
                    kind: AExprKind::Lam(params_annotated, Box::new(body_annotated)),
                    info: info(&fv_total),
                },
                fv_total,
            ))
        }
        Expr::Let(binding, body) => {
            let (body_annotated, fv_after_binding) = annotate_expr(body, is_tail, fv_after)?;
            let (binding_annotated, fv_before) = annotate_binding(binding, &fv_after_binding)?;
            Ok((
                AExpr {
                    kind: AExprKind::Let(Box::new(binding_annotated), Box::new(body_annotated)),
                    info: info(fv_after),
                },
                fv_before,
            ))
        }
        Expr::Sel(target, field) => {
            let (target_annotated, fv_before) = annotate_expr(target, false, fv_after)?;
            Ok((
                AExpr {
                    kind: AExprKind::Sel(Box::new(target_annotated), field.clone()),
                    info: info(fv_after),
                },
                fv_before,
            ))
        }
        Expr::If(cond, if_true, if_false) => {
            let (if_true_annotated, fv_true) = annotate_expr(if_true, is_tail, fv_after)?;
            let (if_false_annotated, fv_false) = annotate_expr(if_false, is_tail, fv_after)?;
            let cond_req = fv_true.union(&fv_false);
            let (cond_annotated, fv_before) = annotate_expr(cond, false, &cond_req)?;
            Ok((
                AExpr {
                    kind: AExprKind::If(
                        Box::new(cond_annotated),
                        Box::new(if_true_annotated),
                        Box::new(if_false_annotated),
                    ),
                    info: info(fv_after),
                },
                fv_before,
            ))
        }
        Expr::Match(cond, cases) => {
            let (cases_annotated, fv_cases) = annotate_cases(cases, is_tail, fv_after)?;
            let (cond_annotated, fv_before) = annotate_expr(cond, false, &fv_cases)?;
            Ok((
                AExpr {
                    kind: AExprKind::Match(Box::new(cond_annotated), cases_annotated),
                    info: info(fv_after),
                },
                fv_before,
            ))
        }
    }
}

fn annotate_stmt(stmt: &Stmt, fv_after: &FvSet) -> Result<(AStmt, FvSet), BackendError> {
    match stmt {
        Stmt::Type(binding) => Ok((AStmt::Type(binding.clone()), fv_after.clone())),
        Stmt::Term(binding) => {
            let (binding_annotated, fv_before) = annotate_binding(binding, fv_after)?;
            Ok((AStmt::Term(binding_annotated), fv_before))
        }
    }
}

fn annotate_stmts(stmts: &[Stmt], fv_after: &FvSet) -> Result<(Vec<AStmt>, FvSet), BackendError> {
    let mut out = Vec::with_capacity(stmts.len());
    let mut fv_tail = fv_after.clone();
    for stmt in stmts.iter().rev() {
        let (stmt_annotated, fv_before) = annotate_stmt(stmt, &fv_tail)?;
        out.push(stmt_annotated);
        fv_tail = fv_before;
    }
    out.reverse();
    Ok((out, fv_tail))
}

fn annotate_prog_with_liveness(prog: &Prog) -> Result<Vec<AStmt>, BackendError> {
    let (stmts, _) = annotate_stmts(prog.stmts(), &FvSet::empty())?;
    Ok(stmts)
}

#[derive(Clone, Debug)]
enum Ir {
    Raw(String),
    Unit,
    Var(String),
    Pair(Box<Ir>, Box<Ir>),
    Tuple(Vec<Ir>),
    Seqs(Vec<Ir>),
    Function(String),
    Paren(Box<Ir>),
    App(Box<Ir>, Vec<Ir>),
    Lam(Vec<Pat>, Box<Ir>),
    Match(Box<Ir>, Vec<(Pat, Ir)>),
    LetIn(Pat, Box<Ir>, Box<Ir>),
}

#[derive(Clone, Debug)]
enum Pat {
    Raw(String),
    Any,
    Paren(Box<Pat>),
    Var(String),
    Pair(Box<Pat>, Box<Pat>),
    Tuple(Vec<Pat>),
    Ctor(String, Option<Box<Pat>>),
    List(Vec<Pat>),
}

#[derive(Clone, Debug)]
enum Code {
    Ir(Ir),
    Pat(Pat),
}

fn pat_to_doc(pat: &Pat) -> String {
    match pat {
        Pat::Raw(doc) => doc.clone(),
        Pat::Any => "_".to_string(),
        Pat::Var(name) => name.clone(),
        Pat::Pair(x, y) => format!("({}, {})", pat_to_doc(x), pat_to_doc(y)),
        Pat::Tuple(xs) => {
            let inner = xs.iter().map(pat_to_doc).collect::<Vec<_>>().join(", ");
            format!("({inner})")
        }
        Pat::Ctor(name, payload) => match payload {
            None => format!("({name})"),
            Some(payload) => format!("({} {})", name, pat_to_doc(payload)),
        },
        Pat::Paren(p) => format!("({})", pat_to_doc(p)),
        Pat::List(xs) => {
            let inner = xs.iter().map(pat_to_doc).collect::<Vec<_>>().join("; ");
            format!("({inner})")
        }
    }
}

fn ir_to_doc(ir: &Ir) -> String {
    match ir {
        Ir::Raw(doc) => doc.clone(),
        Ir::Unit => "()".to_string(),
        Ir::Var(name) => name.clone(),
        Ir::Pair(x, y) => format!("({}, {})", ir_to_doc(x), ir_to_doc(y)),
        Ir::Tuple(xs) => {
            let inner = xs.iter().map(ir_to_doc).collect::<Vec<_>>().join(", ");
            format!("({inner})")
        }
        Ir::Seqs(xs) => match xs.len() {
            0 => "()".to_string(),
            1 => ir_to_doc(&xs[0]),
            _ => {
                let inner = xs.iter().map(ir_to_doc).collect::<Vec<_>>().join(";");
                format!("({inner})")
            }
        },
        Ir::Function(name) => name.clone(),
        Ir::Paren(inner) => format!("({})", ir_to_doc(inner)),
        Ir::App(fun, args) => {
            let mut out = ir_to_doc(fun);
            for arg in args {
                out.push(' ');
                out.push_str(&ir_to_doc(arg));
            }
            out
        }
        Ir::Lam(args, body) => {
            let args_doc = args.iter().map(pat_to_doc).collect::<Vec<_>>().join(" ");
            format!("fun {args_doc} -> {}", ir_to_doc(body))
        }
        Ir::Match(scrutinee, alts) => {
            if alts.is_empty() {
                panic!("match expression must have at least one alternative");
            }
            let mut out = format!("match {} with ", ir_to_doc(scrutinee));
            for (pat, body) in alts {
                out.push_str("| ");
                out.push_str(&pat_to_doc(pat));
                out.push_str(" -> ");
                out.push_str(&ir_to_doc(body));
            }
            out
        }
        Ir::LetIn(pat, value, cont) => format!(
            "let {} = {} in {}",
            pat_to_doc(pat),
            ir_to_doc(value),
            ir_to_doc(cont)
        ),
    }
}

fn optimize_ir(ir: Ir) -> Ir {
    match ir {
        Ir::Raw(doc) => Ir::Raw(doc),
        Ir::Var(name) => Ir::Var(name),
        Ir::Pair(x, y) => Ir::Pair(x, y),
        Ir::Tuple(xs) => Ir::Tuple(xs),
        Ir::Seqs(xs) => {
            let mut out = Vec::new();
            for ir in xs.into_iter().map(optimize_ir) {
                match ir {
                    Ir::Unit => {}
                    Ir::Seqs(items) => out.extend(items),
                    other => out.push(other),
                }
            }
            Ir::Seqs(out)
        }
        Ir::Function(name) => Ir::Function(name),
        Ir::Unit => Ir::Unit,
        Ir::App(fun, args) => match *fun {
            Ir::Paren(inner) => match *inner {
                Ir::App(inner_fun, inner_args) => {
                    let mut merged = inner_args;
                    merged.extend(args.into_iter().map(optimize_ir));
                    optimize_ir(Ir::App(inner_fun, merged))
                }
                other => Ir::App(Box::new(optimize_ir(other)), args.into_iter().map(optimize_ir).collect()),
            },
            other => Ir::App(
                Box::new(optimize_ir(other)),
                args.into_iter().map(optimize_ir).collect(),
            ),
        },
        Ir::Paren(inner) => Ir::Paren(Box::new(optimize_ir(*inner))),
        Ir::Lam(args, body) => Ir::Lam(args, Box::new(optimize_ir(*body))),
        Ir::Match(scrutinee, alts) => Ir::Match(
            Box::new(optimize_ir(*scrutinee)),
            alts
                .into_iter()
                .map(|(pat, body)| (pat, optimize_ir(body)))
                .collect(),
        ),
        Ir::LetIn(pat, value, cont) => Ir::LetIn(
            pat,
            Box::new(optimize_ir(*value)),
            Box::new(optimize_ir(*cont)),
        ),
    }
}

fn uncode(code: Code) -> String {
    match code {
        Code::Ir(ir) => ir_to_doc(&optimize_ir(ir)),
        Code::Pat(pat) => pat_to_doc(&pat),
    }
}

fn code(doc: impl Into<String>) -> Code {
    Code::Ir(Ir::Raw(doc.into()))
}

fn raw(s: &str) -> Code {
    code(s.to_string())
}

fn raw_pat(s: &str) -> Code {
    Code::Pat(Pat::Raw(s.to_string()))
}

fn paren(code: Code) -> Code {
    match code {
        Code::Ir(ir) => Code::Ir(Ir::Paren(Box::new(ir))),
        Code::Pat(pat) => Code::Pat(Pat::Paren(Box::new(pat))),
    }
}

fn var_(name: &str) -> Code {
    Code::Ir(Ir::Var(name.to_string()))
}

fn pair_(x: Code, y: Code) -> Code {
    Code::Ir(Ir::Pair(Box::new(to_ir(x)), Box::new(to_ir(y))))
}

fn ctor_(name: &str, x: Code) -> Code {
    Code::Ir(Ir::App(Box::new(Ir::Raw(name.to_string())), vec![to_ir(x)]))
}

fn ctor_prime(name: &str) -> Code {
    Code::Ir(Ir::App(Box::new(Ir::Raw(name.to_string())), vec![]))
}

fn tuple_(xs: Vec<Code>) -> Code {
    Code::Ir(Ir::Tuple(xs.into_iter().map(to_ir).collect()))
}

fn var_pat_(name: &str) -> Code {
    Code::Pat(Pat::Var(name.to_string()))
}

fn pair_pat_(x: Code, y: Code) -> Code {
    Code::Pat(Pat::Pair(Box::new(to_pat(x)), Box::new(to_pat(y))))
}

fn any_pat_() -> Code {
    Code::Pat(Pat::Any)
}

fn ctor_pat_(name: &str, x: Code) -> Code {
    Code::Pat(Pat::Ctor(name.to_string(), Some(Box::new(to_pat(x)))))
}

fn ctor_pat_prime(name: &str) -> Code {
    Code::Pat(Pat::Ctor(name.to_string(), None))
}

fn to_ir(code: Code) -> Ir {
    match code {
        Code::Ir(ir) => ir,
        Code::Pat(_) => panic!("expected code ir"),
    }
}

fn to_pat(code: Code) -> Pat {
    match code {
        Code::Pat(pat) => pat,
        Code::Ir(_) => panic!("expected pattern"),
    }
}

fn genvar(base: &str) -> (Code, Code) {
    let name = gensym(base);
    (var_(&name), var_pat_(&name))
}

fn int_(i: i32) -> Code {
    code(i.to_string())
}

fn int_lit_(i: i64) -> Code {
    code(i.to_string())
}

fn unit_() -> Code {
    Code::Ir(Ir::Unit)
}

fn lam_(arg: &str, f: impl FnOnce(Code) -> Code) -> Code {
    let name = gensym(arg);
    let var = var_(&name);
    let body = f(var);
    Code::Ir(Ir::Paren(Box::new(Ir::Lam(
        vec![to_pat(var_pat_(&name))],
        Box::new(to_ir(body)),
    ))))
}

fn lam_unit_(f: impl FnOnce() -> Code) -> Code {
    let lam = Ir::Lam(vec![Pat::Any], Box::new(to_ir(f())));
    Code::Ir(Ir::Paren(Box::new(lam)))
}

fn lam_result_(arg: &str, f: impl FnOnce(Code) -> Result<Code, BackendError>) -> Result<Code, BackendError> {
    let name = gensym(arg);
    let var = var_(&name);
    let body = f(var)?;
    Ok(Code::Ir(Ir::Paren(Box::new(Ir::Lam(
        vec![to_pat(var_pat_(&name))],
        Box::new(to_ir(body)),
    )))))
}

fn lam_unit_result_(f: impl FnOnce() -> Result<Code, BackendError>) -> Result<Code, BackendError> {
    let lam = Ir::Lam(vec![Pat::Any], Box::new(to_ir(f()?)));
    Ok(Code::Ir(Ir::Paren(Box::new(lam))))
}

fn lam2_(a: &str, b: &str, f: impl FnOnce(Code, Code) -> Code) -> Code {
    let name_a = gensym(a);
    let name_b = gensym(b);
    let var_a = var_(&name_a);
    let var_b = var_(&name_b);
    let body = f(var_a, var_b);
    let lam = Ir::Lam(
        vec![to_pat(var_pat_(&name_a)), to_pat(var_pat_(&name_b))],
        Box::new(to_ir(body)),
    );
    Code::Ir(Ir::Paren(Box::new(lam)))
}

fn lam3_(a: &str, b: &str, c: &str, f: impl FnOnce(Code, Code, Code) -> Code) -> Code {
    let name_a = gensym(a);
    let name_b = gensym(b);
    let name_c = gensym(c);
    let var_a = var_(&name_a);
    let var_b = var_(&name_b);
    let var_c = var_(&name_c);
    let body = f(var_a, var_b, var_c);
    let lam = Ir::Lam(
        vec![
            to_pat(var_pat_(&name_a)),
            to_pat(var_pat_(&name_b)),
            to_pat(var_pat_(&name_c)),
        ],
        Box::new(to_ir(body)),
    );
    Code::Ir(Ir::Paren(Box::new(lam)))
}

fn lam4_(
    a: &str,
    b: &str,
    c: &str,
    d: &str,
    f: impl FnOnce(Code, Code, Code, Code) -> Code,
) -> Code {
    let name_a = gensym(a);
    let name_b = gensym(b);
    let name_c = gensym(c);
    let name_d = gensym(d);
    let var_a = var_(&name_a);
    let var_b = var_(&name_b);
    let var_c = var_(&name_c);
    let var_d = var_(&name_d);
    let body = f(var_a, var_b, var_c, var_d);
    let lam = Ir::Lam(
        vec![
            to_pat(var_pat_(&name_a)),
            to_pat(var_pat_(&name_b)),
            to_pat(var_pat_(&name_c)),
            to_pat(var_pat_(&name_d)),
        ],
        Box::new(to_ir(body)),
    );
    Code::Ir(Ir::Paren(Box::new(lam)))
}

fn app_(f: Code, a: Code) -> Code {
    let app = Ir::App(Box::new(to_ir(f)), vec![to_ir(a)]);
    Code::Ir(Ir::Paren(Box::new(app)))
}

fn app2_(f: Code, a: Code, b: Code) -> Code {
    let app = Ir::App(Box::new(to_ir(f)), vec![to_ir(a), to_ir(b)]);
    Code::Ir(Ir::Paren(Box::new(app)))
}

fn app3_(f: Code, a: Code, b: Code, c: Code) -> Code {
    let app = Ir::App(Box::new(to_ir(f)), vec![to_ir(a), to_ir(b), to_ir(c)]);
    Code::Ir(Ir::Paren(Box::new(app)))
}

fn app4_(f: Code, a: Code, b: Code, c: Code, d: Code) -> Code {
    let app = Ir::App(Box::new(to_ir(f)), vec![to_ir(a), to_ir(b), to_ir(c), to_ir(d)]);
    Code::Ir(Ir::Paren(Box::new(app)))
}

fn app5_(f: Code, a: Code, b: Code, c: Code, d: Code, e: Code) -> Code {
    let app = Ir::App(
        Box::new(to_ir(f)),
        vec![to_ir(a), to_ir(b), to_ir(c), to_ir(d), to_ir(e)],
    );
    Code::Ir(Ir::Paren(Box::new(app)))
}

fn seqs_(xs: Vec<Code>) -> Code {
    Code::Ir(Ir::Seqs(xs.into_iter().map(to_ir).collect()))
}

fn seq_(x: Code, y: Code) -> Code {
    seqs_(vec![x, y])
}

fn zro_(x: Code) -> Code {
    app_(code("fst"), x)
}

fn pair_value_(x: Code) -> Code {
    app_(code("snd"), x)
}

fn add_(x: Code, y: Code) -> Code {
    code(format!("({} + {})", uncode(x), uncode(y)))
}
fn sub_(x: Code, y: Code) -> Code {
    code(format!("({} - {})", uncode(x), uncode(y)))
}
fn mul_(x: Code, y: Code) -> Code {
    code(format!("({} * {})", uncode(x), uncode(y)))
}
fn div_(x: Code, y: Code) -> Code {
    code(format!("({} / {})", uncode(x), uncode(y)))
}

fn lt_(x: Code, y: Code) -> Code {
    code(format!("(if {} < {} then 1 else 0)", uncode(x), uncode(y)))
}

fn le_(x: Code, y: Code) -> Code {
    code(format!("(if {} <= {} then 1 else 0)", uncode(x), uncode(y)))
}

fn gt_(x: Code, y: Code) -> Code {
    code(format!("(if {} > {} then 1 else 0)", uncode(x), uncode(y)))
}

fn ge_(x: Code, y: Code) -> Code {
    code(format!("(if {} >= {} then 1 else 0)", uncode(x), uncode(y)))
}

fn if_(cond: Code, then_: Code, else_: Code) -> Code {
    code(format!("if {} then {} else {}", uncode(cond), uncode(then_), uncode(else_)))
}

fn dyn_array_get_(arr: Code, i: Code) -> Code {
    app2_(code("Dynarray.get"), arr, i)
}

fn dyn_array_remove_last_(arr: Code) -> Code {
    app_(code("Dynarray.remove_last"), arr)
}

fn world_state_(w: Code) -> Code {
    code(format!("({}.state)", uncode(w)))
}

fn state_env_(s: Code) -> Code {
    code(format!("({}.e)", uncode(s)))
}

fn world_env_(w: Code) -> Code {
    state_env_(world_state_(w))
}

fn state_kont_(s: Code) -> Code {
    code(format!("({}.k)", uncode(s)))
}

fn world_kont_(w: Code) -> Code {
    state_kont_(world_state_(w))
}

fn stepped_(w: Code) -> Code {
    app_(code("stepped"), w)
}

fn set_c_(w: Code, c: Code) -> Code {
    code(format!("({}.c <- {})", uncode(world_state_(w)), uncode(c)))
}

fn set_k_(w: Code, k: Code) -> Code {
    code(format!("({}.k <- {})", uncode(world_state_(w)), uncode(k)))
}

fn from_constructor_(ctag: Code) -> Code {
    app_(code("Memo.from_constructor"), ctag)
}

fn to_unit_(x: Code) -> Code {
    app_(code("ignore"), x)
}

fn pop_env_(w: Code) -> Code {
    app_(code("pop_env"), w)
}

fn goto_(w: Code, pc_value: i32) -> Code {
    seq_(set_c_(w.clone(), pc_to_exp_(pc_(pc_value))), stepped_(w))
}

fn push_env_(w: Code, v: Code) -> Code {
    app2_(code("push_env"), w, v)
}

fn get_env_(w: Code, i: Code) -> Code {
    dyn_array_get_(state_env_(world_state_(w)), i)
}

fn exec_done_(w: Code) -> Code {
    app_(code("exec_done"), w)
}

fn env_call_(w: Code, keep: Code, nargs: Code) -> Code {
    app3_(code("env_call"), w, keep, nargs)
}

fn restore_env_(w: Code, n: Code, seqs: Code) -> Code {
    app3_(code("restore_env"), w, n, seqs)
}

fn get_next_cont_(seqs: Code) -> Code {
    app_(code("get_next_cont"), seqs)
}

fn resolve_(w: Code, src: Code) -> Code {
    app2_(code("resolve"), w, src)
}

fn memo_appends_(xs: Vec<Code>) -> Code {
    let inner = xs.into_iter().map(uncode).collect::<Vec<_>>().join(";");
    app_(code("Memo.appends"), code(format!("[{}]", inner)))
}

fn memo_from_int_(i: Code) -> Code {
    app_(code("Memo.from_int"), i)
}

fn int_from_word_(w: Code) -> Code {
    app_(code("Word.get_value"), w)
}

fn memo_splits_(seq: Code) -> Code {
    app_(code("Memo.splits"), seq)
}

fn memo_splits_specialized_(seq: Code, n: usize) -> Code {
    if n > 4 {
        memo_splits_(seq)
    } else {
        app_(code(format!("Memo.splits_{}", n)), seq)
    }
}

fn memo_list_match_(seq: Code) -> Code {
    app_(code("Memo.list_match"), seq)
}

fn word_get_value_(w: Code) -> Code {
    app_(code("Word.get_value"), w)
}

fn option_get_(c: Code) -> Code {
    app_(code("Option.get"), c)
}

fn let_in_(a: &str, value: Code, body: impl FnOnce(Code) -> Code) -> Code {
    let name = gensym(a);
    Code::Ir(Ir::LetIn(
        Pat::Raw(name.clone()),
        Box::new(to_ir(value)),
        Box::new(to_ir(body(code(name)))),
    ))
}

fn let_in_result_(
    a: &str,
    value: Code,
    body: impl FnOnce(Code) -> Result<Code, BackendError>,
) -> Result<Code, BackendError> {
    let name = gensym(a);
    let var = code(name.clone());
    let body_code = body(var)?;
    Ok(Code::Ir(Ir::LetIn(
        Pat::Raw(name),
        Box::new(to_ir(value)),
        Box::new(to_ir(body_code)),
    )))
}

fn tuple2_pat_(a: Code, b: Code) -> Code {
    Code::Pat(Pat::Pair(Box::new(to_pat(a)), Box::new(to_pat(b))))
}

fn let_pat_in_(pat: Code, value: Code, body: Code) -> Code {
    Code::Ir(Ir::LetIn(to_pat(pat), Box::new(to_ir(value)), Box::new(to_ir(body))))
}

fn list_literal_(xs: Vec<Code>) -> Code {
    let inner = xs.into_iter().map(uncode).collect::<Vec<_>>().join(";");
    code(format!("[{}]", inner))
}

fn list_literal_of_(f: impl Fn(i32) -> Code, xs: Vec<i32>) -> Code {
    list_literal_(xs.into_iter().map(f).collect())
}

fn list_nth_(xs: Code, i: Code) -> Code {
    app2_(code("List.nth"), xs, i)
}

fn list_pat_(xs: Vec<Code>) -> Code {
    Code::Pat(Pat::List(xs.into_iter().map(to_pat).collect()))
}

fn tuple_pat_(xs: Vec<Code>) -> Code {
    Code::Pat(Pat::Tuple(xs.into_iter().map(to_pat).collect()))
}

fn memo_splits_pat_(xs: Vec<Code>) -> Code {
    if xs.len() > 4 {
        list_pat_(xs)
    } else {
        tuple_pat_(xs)
    }
}

fn with_splits(
    count: usize,
    splits: Code,
    k: impl FnOnce(Vec<Code>) -> Result<Code, BackendError>,
) -> Result<Code, BackendError> {
    let splits_name = gensym("splits");
    let splits_var = var_(&splits_name);
    let mut split_names = Vec::with_capacity(count);
    for idx in 0..count {
        split_names.push(gensym(&format!("split{idx}")));
    }
    let split_vars = split_names.iter().map(|n| var_(n)).collect::<Vec<_>>();
    let body = k(split_vars)?;
    let mut body_str = uncode(body);
    for (idx, split_name) in split_names.iter().enumerate().rev() {
        let nth_expr = uncode(list_nth_(splits_var.clone(), int_(idx as i32)));
        body_str = format!("let {split_name} = {nth_expr} in {body_str}");
    }
    let splits_expr = uncode(splits);
    Ok(code(format!(
        "let {splits_name} = {splits_expr} in {body_str}"
    )))
}

fn match_option_(x: Code, none: impl FnOnce() -> Code, a: &str, some: impl FnOnce(Code) -> Code) -> Code {
    let name = gensym(a);
    Code::Ir(Ir::Match(
        Box::new(to_ir(x)),
        vec![
            (Pat::Ctor("None".to_string(), None), to_ir(none())),
            (
                Pat::Ctor("Some".to_string(), Some(Box::new(Pat::Var(name.clone())))),
                to_ir(some(code(name))),
            ),
        ],
    ))
}

fn src_E_(i: i32) -> Code {
    code(format!("(Source.E {i})"))
}

fn match_resolve_(
    x: Code,
    none: impl FnOnce() -> Code,
    a: &str,
    some: impl FnOnce(Code) -> Code,
) -> Code {
    let name = gensym(a);
    Code::Ir(Ir::Match(
        Box::new(to_ir(x)),
        vec![
            (Pat::Ctor("None".to_string(), None), to_ir(none())),
            (
                Pat::Ctor("Some".to_string(), Some(Box::new(Pat::Var(name.clone())))),
                to_ir(some(raw(&name))),
            ),
        ],
    ))
}

fn match_resolve_destruct_(
    x: Code,
    none: impl FnOnce() -> Code,
    hd: &str,
    tl: &str,
    some: impl FnOnce(Code, Code) -> Code,
) -> Code {
    let name_hd = gensym(hd);
    let name_tl = gensym(tl);
    Code::Ir(Ir::Match(
        Box::new(to_ir(x)),
        vec![
            (Pat::Ctor("None".to_string(), None), to_ir(none())),
            (
                Pat::Raw(format!("Some ({}, {})", name_hd, name_tl)),
                to_ir(some(code(name_hd), code(name_tl))),
            ),
        ],
    ))
}

fn match_raw_(x: Code, fs: Vec<(String, Code)>) -> Code {
    let alts = fs
        .into_iter()
        .map(|(c, body)| (Pat::Raw(c), to_ir(body)))
        .collect::<Vec<_>>();
    Code::Ir(Ir::Match(Box::new(to_ir(x)), alts))
}

fn match_int_(x: Code, fs: Vec<(Code, Code)>) -> Code {
    let alts = fs.into_iter().map(|(c, body)| (to_pat(c), to_ir(body))).collect();
    Code::Ir(Ir::Match(Box::new(to_ir(x)), alts))
}

fn match_int_default_(x: Code, fs: Vec<(i32, Code)>, dflt: Code) -> Code {
    let mut alts = fs
        .into_iter()
        .map(|(c, body)| (int_(c), body))
        .collect::<Vec<_>>();
    alts.push((any_pat_(), dflt));
    match_int_(x, alts)
}

fn unreachable_(pc: i32) -> Code {
    code(format!("failwith \"unreachable ({pc})\""))
}

fn match_ctor_tag_default_(x: Code, fs: Vec<(String, Code)>, dflt: Code) -> Code {
    let dummy_name = gensym("c");
    let alts = fs
        .into_iter()
        .map(|(tag_name, body)| {
            (
                Pat::Raw(format!("{dummy_name} when {dummy_name} = {tag_name}")),
                to_ir(body),
            )
        })
        .collect::<Vec<_>>();
    let mut all = alts;
    all.push((Pat::Raw("_".to_string()), to_ir(dflt)));
    Code::Ir(Ir::Match(Box::new(to_ir(x)), all))
}

fn assert_env_length_(w: Code, e: Code) -> Code {
    app2_(code("assert_env_length"), w, e)
}

fn return_n_(w: Code, n: Code, exp: Code) -> Code {
    app3_(code("return_n"), w, n, exp)
}

fn drop_n_(w: Code, e: Code, n: Code) -> Code {
    app3_(code("drop_n"), w, e, n)
}

fn pc_to_int_(pc: Code) -> Code {
    app_(code("pc_to_int"), pc)
}

fn int_to_pc_(int: Code) -> Code {
    app_(code("int_to_pc"), int)
}

fn pc_to_exp_(pc: Code) -> Code {
    app_(code("pc_to_exp"), pc)
}

fn pc_(pc: i32) -> Code {
    int_to_pc_(int_(pc))
}

fn memo_from_constructor_(ctag: Code) -> Code {
    app_(code("Memo.from_constructor"), ctag)
}

fn memo_to_word_(seq: Code) -> Code {
    app_(code("Memo.to_word"), seq)
}

#[derive(Clone)]
struct Ctx {
    arity: HashMap<String, usize>,
    ctag: HashMap<String, i32>,
    ctag_name: HashMap<String, String>,
    constructor_degree: Vec<i32>,
    conts: Vec<(String, Rc<dyn Fn(Code, Code, &mut Compiler) -> Result<Code, BackendError>>)>,
    conts_count: i32,
    func_pc: HashMap<String, i32>,
}

impl Ctx {
    fn new() -> Self {
        let mut ctx = Self {
            arity: HashMap::new(),
            ctag: HashMap::new(),
            ctag_name: HashMap::new(),
            constructor_degree: Vec::new(),
            conts: Vec::new(),
            conts_count: 0,
            func_pc: HashMap::new(),
        };
        ctx.add_cont("cont_done", 0, |w, _tl, _| Ok(exec_done_(w)));
        ctx
    }

    fn get_ctor_tag_name(name: &str) -> String {
        format!("tag_{name}")
    }

    fn add_cont(
        &mut self,
        name: &str,
        arity: usize,
        app: impl Fn(Code, Code, &mut Compiler) -> Result<Code, BackendError> + 'static,
    ) {
        if self.arity.contains_key(name) {
            return;
        }
        let tag = self.ctag.len() as i32;
        self.arity.insert(name.to_string(), arity);
        self.ctag.insert(name.to_string(), tag);
        self.ctag_name
            .insert(name.to_string(), Self::get_ctor_tag_name(name));
        self.constructor_degree.push(1 - arity as i32);
        self.conts.push((name.to_string(), Rc::new(app)));
        self.conts_count += 1;
    }

    fn ctor_tag_name(&self, name: &str) -> Code {
        raw(
            self.ctag_name
                .get(name)
                .unwrap_or(&Self::get_ctor_tag_name(name))
                .as_str(),
        )
    }
}

#[derive(Clone, Debug)]
struct Scope {
    meta_env: BTreeMap<String, Vec<usize>>,
    env_length: usize,
    progressed: bool,
}

impl Scope {
    fn new() -> Self {
        Self {
            meta_env: BTreeMap::new(),
            env_length: 0,
            progressed: false,
        }
    }

    fn check(&self) -> Result<(), BackendError> {
        let mut seen = vec![false; self.env_length];
        for (key, data) in &self.meta_env {
            for idx in data {
                if *idx >= self.env_length {
                    return Err(BackendError::new(format!(
                        "check_scope: variable {key} mapped to invalid index {idx} with env_length {}",
                        self.env_length
                    )));
                }
                if seen[*idx] {
                    return Err(BackendError::new(format!(
                        "check_scope: variable {key} mapped to duplicate index {idx}"
                    )));
                }
                seen[*idx] = true;
            }
        }
        Ok(())
    }

    fn push(&self) -> Self {
        Self {
            meta_env: self.meta_env.clone(),
            env_length: self.env_length + 1,
            progressed: true,
        }
    }

    fn extend(&self, name: &str) -> Result<Self, BackendError> {
        self.check()?;
        let mut meta_env = self.meta_env.clone();
        meta_env.entry(name.to_string()).or_default().push(self.env_length);
        let ret = Self {
            meta_env,
            env_length: self.env_length + 1,
            progressed: self.progressed,
        };
        ret.check()?;
        Ok(ret)
    }

    fn drop(&self, name: &str) -> Result<Self, BackendError> {
        let mut meta_env = self.meta_env.clone();
        let remove_key = {
            let stack = meta_env
                .get_mut(name)
                .ok_or_else(|| BackendError::new(format!("drop_s missing: {name}")))?;
            if stack.pop().is_none() {
                return Err(BackendError::new(format!("drop_s missing: {name}")));
            }
            stack.is_empty()
        };
        if remove_key {
            meta_env.remove(name);
        }
        Ok(Self {
            meta_env,
            env_length: self.env_length - 1,
            progressed: self.progressed,
        })
    }

    fn pop_n(&self, n: usize) -> Result<Self, BackendError> {
        if self.env_length < n {
            return Err(BackendError::new("pop_n underflow"));
        }
        let ret = Self {
            meta_env: self.meta_env.clone(),
            env_length: self.env_length - n,
            progressed: self.progressed,
        };
        ret.check()?;
        Ok(ret)
    }

    fn pop(&self) -> Result<Self, BackendError> {
        self.pop_n(1)
    }
}

type Kont = Rc<dyn Fn(Scope, Code, &mut Compiler) -> Result<Code, BackendError>>;

struct Compiler {
    ctx: Ctx,
    codes: Vec<Option<Code>>,
}

impl Compiler {
    fn new() -> Self {
        Self {
            ctx: Ctx::new(),
            codes: Vec::new(),
        }
    }

    fn add_code(&mut self, c: Option<Code>) -> i32 {
        let pc = self.codes.len() as i32;
        self.codes.push(c);
        pc
    }

    fn set_code(&mut self, pc: i32, c: Code) -> Result<(), BackendError> {
        let idx = pc as usize;
        if idx >= self.codes.len() {
            return Err(BackendError::new("set_code out of range"));
        }
        self.codes[idx] = Some(c);
        Ok(())
    }

    fn add_code_k<T>(
        &mut self,
        f: impl FnOnce(i32, &mut Compiler) -> Result<(Code, T), BackendError>,
    ) -> Result<T, BackendError> {
        let pc = self.add_code(None);
        let (code, ret) = f(pc, self)?;
        self.set_code(pc, code)?;
        Ok(ret)
    }

    fn register_constructor(&mut self, con_name: &str, types: &[Ty]) {
        let arity = types.len();
        if self.ctx.arity.contains_key(con_name) {
            return;
        }
        let constructor_index = self.ctx.ctag.len() as i32;
        self.ctx.arity.insert(con_name.to_string(), arity);
        self.ctx.ctag.insert(con_name.to_string(), constructor_index);
        let tag_name = Ctx::get_ctor_tag_name(con_name);
        self.ctx.ctag_name.insert(con_name.to_string(), tag_name);
        self.ctx.constructor_degree.push(1 - arity as i32);
    }

    fn register_constructors(&mut self, ctors: &[TyCtor]) {
        for ctor in ctors {
            self.register_constructor(&ctor.name, &ctor.args);
        }
    }

    fn tuple_ctor_name(arity: usize) -> String {
        format!("__tuple_{arity}")
    }

    fn ensure_tuple_ctor(&mut self, arity: usize) -> String {
        let name = Self::tuple_ctor_name(arity);
        if !self.ctx.ctag.contains_key(&name) {
            let types = vec![Ty::Unit; arity];
            self.register_constructor(&name, &types);
        }
        name
    }

    fn apply_cont_pc(&mut self) -> i32 {
        self.add_code(None)
    }

    fn drop_vars(&mut self, s: Scope, vars: &[String], w: Code, k: &Kont) -> Result<Code, BackendError> {
        let mut new_s = s.clone();
        let mut n = 0;
        for var in vars {
            if new_s
                .meta_env
                .get(var)
                .map_or(false, |stack| !stack.is_empty())
            {
                new_s = new_s.drop(var)?;
                n += 1;
            }
        }
        let mut seqs = Vec::new();
        seqs.push(assert_env_length_(w.clone(), int_(s.env_length as i32)));
        seqs.push(drop_n_(w.clone(), int_(s.env_length as i32), int_(n)));
        seqs.push(k(new_s, w, self)?);
        Ok(seqs_(seqs))
    }

    fn return_expr(&mut self, s: Scope, w: Code, apply_cont: i32) -> Result<Code, BackendError> {
        Ok(seqs_(vec![
            assert_env_length_(w.clone(), int_(s.env_length as i32)),
            return_n_(w, int_(s.env_length as i32), pc_to_exp_(pc_(apply_cont))),
        ]))
    }

    fn keep_only(&mut self, s: &Scope, fv: &BTreeSet<String>) -> Result<(Vec<i32>, Scope), BackendError> {
        s.check()?;
        let mut keep = vec![true; s.env_length];
        for (key, data) in &s.meta_env {
            let should_keep = fv.contains(key);
            for idx in data {
                keep[*idx] = should_keep;
            }
        }
        for v in fv {
            if !s.meta_env.contains_key(v) {
                return Err(BackendError::new(format!("keep_only not found: {v}")));
            }
        }
        let mut keep_idx: Vec<i32> = Vec::new();
        let mut new_index = vec![-1isize; s.env_length];
        for (i, k) in keep.iter().enumerate() {
            if *k {
                new_index[i] = keep_idx.len() as isize;
                keep_idx.push(i as i32);
            }
        }
        let mut meta_env: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        for (key, data) in &s.meta_env {
            if fv.contains(key) {
                let mut mapped = Vec::with_capacity(data.len());
                for idx in data {
                    let new_idx = new_index[*idx];
                    if new_idx < 0 {
                        return Err(BackendError::new(format!(
                            "keep_only missing index for {key}"
                        )));
                    }
                    mapped.push(new_idx as usize);
                }
                meta_env.insert(key.clone(), mapped);
            } else {
                meta_env.entry(key.clone()).or_insert_with(Vec::new);
            }
        }
        let new_s = Scope {
            meta_env,
            env_length: keep_idx.len(),
            progressed: s.progressed,
        };
        new_s.check()?;
        Ok((keep_idx, new_s))
    }

    fn reading(
        &mut self,
        s: Scope,
        f: impl FnOnce(Scope, Code, &mut Compiler) -> Result<Code, BackendError>,
        w: Code,
    ) -> Result<Code, BackendError> {
        let make_code = |s: Scope, w: Code, this: &mut Compiler| f(s, w, this);
        if s.progressed {
            let code = lam_result_("w", |w| {
                make_code(
                    Scope {
                        meta_env: s.meta_env.clone(),
                        env_length: s.env_length,
                        progressed: false,
                    },
                    w,
                    self,
                )
            })?;
            let pc = self.add_code(Some(code));
            Ok(goto_(w, pc))
        } else {
            make_code(
                Scope {
                    meta_env: s.meta_env.clone(),
                    env_length: s.env_length,
                    progressed: false,
                },
                w,
                self,
            )
        }
    }

    fn compile_pp_expr(
        &mut self,
        s: Scope,
        expr: &AExpr,
        k: &Kont,
        w: Code,
        apply_cont: i32,
    ) -> Result<Code, BackendError> {
        match &expr.kind {
            AExprKind::Var(name) => {
                let loc = s
                    .meta_env
                    .get(name)
                    .and_then(|stack| stack.last().copied())
                    .ok_or_else(|| BackendError::new(format!("compile_pp_expr cannot find var: {name}")))?;
                Ok(seqs_(vec![
                    assert_env_length_(w.clone(), int_(s.env_length as i32)),
                    push_env_(w.clone(), get_env_(w.clone(), int_(loc as i32))),
                    k(s.push(), w, self)?,
                ]))
            }
            AExprKind::GVar(name) => {
                let app_expr = AExpr {
                    kind: AExprKind::App(
                        Box::new(AExpr {
                            kind: AExprKind::GVar(name.clone()),
                            info: expr.info.clone(),
                        }),
                        Vec::new(),
                    ),
                    info: expr.info.clone(),
                };
                self.compile_pp_expr(s, &app_expr, k, w, apply_cont)
            }
            AExprKind::Unit => Ok(seqs_(vec![
                assert_env_length_(w.clone(), int_(s.env_length as i32)),
                push_env_(w.clone(), memo_from_int_(int_(0))),
                k(s.push(), w, self)?,
            ])),
            AExprKind::Bool(b) => {
                let value = if *b { 1 } else { 0 };
                Ok(seqs_(vec![
                    assert_env_length_(w.clone(), int_(s.env_length as i32)),
                    push_env_(w.clone(), memo_from_int_(int_(value))),
                    k(s.push(), w, self)?,
                ]))
            }
            AExprKind::Str(_) | AExprKind::Builtin(_) => Ok(seqs_(vec![
                assert_env_length_(w.clone(), int_(s.env_length as i32)),
                push_env_(w.clone(), memo_from_int_(int_(0))),
                k(s.push(), w, self)?,
            ])),
            AExprKind::Tup(items) => {
                let name = self.ensure_tuple_ctor(items.len());
                let app_expr = AExpr {
                    kind: AExprKind::App(
                        Box::new(AExpr {
                            kind: AExprKind::Ctor(name),
                            info: expr.info.clone(),
                        }),
                        items.clone(),
                    ),
                    info: expr.info.clone(),
                };
                self.compile_pp_expr(s, &app_expr, k, w, apply_cont)
            }
            AExprKind::Arr(items) => {
                let name = self.ensure_tuple_ctor(items.len());
                let app_expr = AExpr {
                    kind: AExprKind::App(
                        Box::new(AExpr {
                            kind: AExprKind::Ctor(name),
                            info: expr.info.clone(),
                        }),
                        items.clone(),
                    ),
                    info: expr.info.clone(),
                };
                self.compile_pp_expr(s, &app_expr, k, w, apply_cont)
            }
            AExprKind::Lam(_, _) => Ok(seqs_(vec![
                assert_env_length_(w.clone(), int_(s.env_length as i32)),
                push_env_(w.clone(), memo_from_int_(int_(0))),
                k(s.push(), w, self)?,
            ])),
            AExprKind::Match(value, cases) => {
                let cases_vec = cases.clone();
                let k_clone = Rc::clone(k);
                let kont: Kont = Rc::new(move |s_after: Scope, w: Code, this: &mut Compiler| {
                    this.reading(
                        s_after,
                        |s2, w2, this2| this2.compile_pp_cases(s2, &cases_vec, &k_clone, w2, apply_cont),
                        w,
                    )
                });
                self.compile_pp_expr(s, value, &kont, w, apply_cont)
            }
            AExprKind::Ctor(name) => Ok(seqs_(vec![
                assert_env_length_(w.clone(), int_(s.env_length as i32)),
                push_env_(w.clone(), from_constructor_(self.ctx.ctor_tag_name(name))),
                k(s.push(), w, self)?,
            ])),
            AExprKind::App(fun, args) => match &fun.kind {
                AExprKind::Ctor(name) => {
                    let name = name.clone();
                    let k_clone = Rc::clone(k);
                    let length = args.len();
                    let kont: Kont = Rc::new(move |s_after: Scope, w: Code, this: &mut Compiler| {
                        let s_popped = s_after.pop_n(length)?;
                        let s_result = s_popped.push();
                        let mut names = Vec::with_capacity(length);
                        for _ in 0..length {
                            names.push(gensym("ctor_arg"));
                        }
                        let mut appends = Vec::with_capacity(length + 1);
                        appends.push(from_constructor_(this.ctx.ctor_tag_name(&name)));
                        for name in names.iter().rev() {
                            appends.push(var_(name));
                        }
                        let body = seqs_(vec![
                            push_env_(w.clone(), memo_appends_(appends)),
                            k_clone(s_result.clone(), w.clone(), this)?,
                        ]);
                        let mut body_str = uncode(body);
                        for name in names.iter().rev() {
                            let pop_expr = uncode(pop_env_(w.clone()));
                            body_str = format!("let {name} = {pop_expr} in {body_str}");
                        }
                        let pop_code = code(body_str);
                        Ok(seqs_(vec![
                            assert_env_length_(w.clone(), int_(s_after.env_length as i32)),
                            pop_code,
                        ]))
                    });
                    self.compile_pp_exprs(s, args, &kont, w, apply_cont)
                }
                AExprKind::Builtin(_name) => {
                    let k_clone = Rc::clone(k);
                    let length = args.len();
                    let kont: Kont = Rc::new(move |s_after: Scope, w: Code, this: &mut Compiler| {
                        let s_popped = s_after.pop_n(length)?;
                        let s_result = s_popped.push();
                        let mut seqs = Vec::new();
                        seqs.push(assert_env_length_(w.clone(), int_(s_after.env_length as i32)));
                        for _ in 0..length {
                            seqs.push(to_unit_(pop_env_(w.clone())));
                        }
                        seqs.push(push_env_(w.clone(), memo_from_int_(int_(0))));
                        seqs.push(k_clone(s_result, w, this)?);
                        Ok(seqs_(seqs))
                    });
                    self.compile_pp_exprs(s, args, &kont, w, apply_cont)
                }
                AExprKind::GVar(name) => {
                    let name = name.clone();
                    let at_tail = expr.info.tail;
                    let fv_after = expr.info.fv.clone();
                    let (keep_idx, keep_s) = self.keep_only(&s, &fv_after)?;
                    let keep_length = keep_s.env_length;
                    let xs_length = args.len();
                    if at_tail {
                        if keep_length != 0 {
                            return Err(BackendError::new("tail call must keep nothing"));
                        }
                        let kont: Kont = Rc::new(move |s_after: Scope, w: Code, this: &mut Compiler| {
                            let func_pc = *this
                                .ctx
                                .func_pc
                                .get(&name)
                                .ok_or_else(|| BackendError::new(format!("unknown function: {name}")))?;
                            Ok(seqs_(vec![
                                assert_env_length_(w.clone(), int_(s_after.env_length as i32)),
                                to_unit_(env_call_(
                                    w.clone(),
                                    list_literal_of_(int_, vec![]),
                                    int_(xs_length as i32),
                                )),
                                goto_(w, func_pc),
                            ]))
                        });
                        self.compile_pp_exprs(s, args, &kont, w, apply_cont)
                    } else {
                        let cont_name = format!("cont_{}", self.ctx.conts_count);
                        let k_clone = Rc::clone(k);
                        let keep_s_clone = keep_s.clone();
                        let cont_name_clone = cont_name.clone();
                        self.ctx.add_cont(&cont_name, keep_length + 1, move |w, tl, this| {
                            Ok(seqs_(vec![
                                set_k_(w.clone(), get_next_cont_(tl.clone())),
                                restore_env_(w.clone(), int_(keep_length as i32), tl),
                                k_clone(keep_s_clone.push(), w, this)?,
                            ]))
                        });
                        let keep_list = keep_idx.clone();
                        let kont: Kont = Rc::new(move |s_after: Scope, w: Code, this: &mut Compiler| {
                            let func_pc = *this
                                .ctx
                                .func_pc
                                .get(&name)
                                .ok_or_else(|| BackendError::new(format!("unknown function: {name}")))?;
                            Ok(seqs_(vec![
                                assert_env_length_(w.clone(), int_(s_after.env_length as i32)),
                                let_in_(
                                    "keep",
                                    env_call_(
                                        w.clone(),
                                        list_literal_of_(int_, keep_list.clone()),
                                        int_(xs_length as i32),
                                    ),
                                    |keep| {
                                        set_k_(
                                            w.clone(),
                                            memo_appends_(vec![
                                                from_constructor_(
                                                    this.ctx.ctor_tag_name(&cont_name_clone)
                                                ),
                                                keep,
                                                world_kont_(w.clone()),
                                            ]),
                                        )
                                    },
                                ),
                                goto_(w, func_pc),
                            ]))
                        });
                        self.compile_pp_exprs(s, args, &kont, w, apply_cont)
                    }
                }
                _ => Err(BackendError::new("compile_pp_expr: unsupported app")),
            },
            AExprKind::If(cond, thn, els) => {
                let cond_clone = cond.clone();
                let thn_clone = thn.clone();
                let els_clone = els.clone();
                let k_outer = Rc::clone(k);
                let kont: Kont = Rc::new(move |s_after: Scope, w: Code, this: &mut Compiler| {
                    let cond_name = gensym("cond");
                    let if_kont_name = gensym("if_kont");
                    let cond_resolve = resolve_(w.clone(), src_E_(s_after.env_length as i32 - 1));
                    let if_kont_value = paren(lam_unit_result_(|| {
                        k_outer(s_after.clone(), w.clone(), this)
                    })?);
                    let if_kont_var = var_(&if_kont_name);
                    let branch_k: Kont = Rc::new(move |_s: Scope, _w: Code, _this: &mut Compiler| {
                        Ok(app_(if_kont_var.clone(), unit_()))
                    });
                    let else_code =
                        this.compile_pp_expr(s_after.pop()?, &els_clone, &branch_k, w.clone(), apply_cont)?;
                    let then_code =
                        this.compile_pp_expr(s_after.pop()?, &thn_clone, &branch_k, w.clone(), apply_cont)?;
                    let cond_bool = code(format!(
                        "({} <> 0)",
                        uncode(int_from_word_(zro_(var_(&cond_name))))
                    ));
                    Ok(seqs_(vec![
                        assert_env_length_(w.clone(), int_(s_after.env_length as i32)),
                        let_pat_in_(
                            var_pat_(&cond_name),
                            cond_resolve,
                            seqs_(vec![
                                to_unit_(pop_env_(w.clone())),
                                let_pat_in_(
                                    var_pat_(&if_kont_name),
                                    if_kont_value.clone(),
                                    if_(cond_bool, then_code, else_code),
                                ),
                            ]),
                        ),
                    ]))
                });
                self.compile_pp_expr(s, &cond_clone, &kont, w, apply_cont)
            }
            AExprKind::Op(op, x0, x1) => {
                let op_code: fn(Code, Code) -> Code = match op.as_str() {
                    "+" => add_,
                    "-" => sub_,
                    "*" => mul_,
                    "/" => div_,
                    "<" => lt_,
                    "<=" => le_,
                    ">" => gt_,
                    ">=" => ge_,
                    _ => return Err(BackendError::new(format!("compile_pp_expr: unsupported op {op}"))),
                };
                let x0_clone = x0.clone();
                let x1_clone = x1.clone();
                let k_outer = Rc::clone(k);
                let kont_x1: Kont = Rc::new(move |s_after: Scope, w: Code, this: &mut Compiler| {
                    this.reading(
                        s_after,
                        |s2, w2, this2| {
                            let s_pop2 = s2.pop()?.pop()?;
                            let s_result = s_pop2.push();
                            Ok(seqs_(vec![
                                assert_env_length_(w2.clone(), int_(s2.env_length as i32)),
                                let_in_result_(
                                    "x0",
                                    resolve_(w2.clone(), src_E_(s2.env_length as i32 - 2)),
                                    |x0v| {
                                        let_in_result_(
                                            "x1",
                                            resolve_(w2.clone(), src_E_(s2.env_length as i32 - 1)),
                                            |x1v| {
                                                let k_code = k_outer(s_result.clone(), w2.clone(), this2)?;
                                                Ok(seqs_(vec![
                                                    to_unit_(pop_env_(w2.clone())),
                                                    to_unit_(pop_env_(w2.clone())),
                                                    push_env_(w2.clone(), memo_from_int_(op_code(int_from_word_(zro_(x0v)), int_from_word_(zro_(x1v))))),
                                                    k_code,
                                                ]))
                                            },
                                        )
                                    },
                                )?,
                            ]))
                        },
                        w,
                    )
                });
                let kont_x0: Kont = Rc::new(move |s_after: Scope, w: Code, this: &mut Compiler| {
                    this.compile_pp_expr(s_after, &x1_clone, &kont_x1, w, apply_cont)
                });
                self.compile_pp_expr(s, &x0_clone, &kont_x0, w, apply_cont)
            }
            AExprKind::Int(value) => Ok(seqs_(vec![
                assert_env_length_(w.clone(), int_(s.env_length as i32)),
                push_env_(w.clone(), memo_from_int_(int_lit_(*value))),
                k(s.push(), w, self)?,
            ])),
                AExprKind::Let(binding, body) => match &**binding {
                ABinding::Seq(value) => {
                    let value_clone = value.clone();
                    let body_clone = body.clone();
                    let k_outer = Rc::clone(k);
                    let kont: Kont = Rc::new(move |s_after: Scope, w: Code, this: &mut Compiler| {
                        let s_body = s_after.pop()?;
                        Ok(seqs_(vec![
                            assert_env_length_(w.clone(), int_(s_after.env_length as i32)),
                            to_unit_(pop_env_(w.clone())),
                            this.compile_pp_expr(s_body, &body_clone, &k_outer, w, apply_cont)?,
                        ]))
                    });
                    self.compile_pp_expr(s, &value_clone, &kont, w, apply_cont)
                }
                ABinding::One(Pattern::Any, value) => {
                    let value_clone = value.clone();
                    let body_clone = body.clone();
                    let k_outer = Rc::clone(k);
                    let kont: Kont = Rc::new(move |s_after: Scope, w: Code, this: &mut Compiler| {
                        let s_body = s_after.pop()?;
                        Ok(seqs_(vec![
                            assert_env_length_(w.clone(), int_(s_after.env_length as i32)),
                            to_unit_(pop_env_(w.clone())),
                            this.compile_pp_expr(s_body, &body_clone, &k_outer, w, apply_cont)?,
                        ]))
                    });
                    self.compile_pp_expr(s, &value_clone, &kont, w, apply_cont)
                }
                ABinding::One(Pattern::Var(name), value) => {
                    let name = name.clone();
                    let value_clone = value.clone();
                    let body_clone = body.clone();
                    let k_outer = Rc::clone(k);
                    let kont: Kont = Rc::new(move |s_after: Scope, w: Code, this: &mut Compiler| {
                        let s_extended = s_after.pop()?.extend(&name)?;
                            let drop_names = vec![name.clone()];
                            let k_outer_inner = Rc::clone(&k_outer);
                            let k_body: Kont = Rc::new(move |s_body: Scope, w_body: Code, this2: &mut Compiler| {
                                this2.drop_vars(s_body, &drop_names, w_body, &k_outer_inner)
                            });
                            this.compile_pp_expr(s_extended, &body_clone, &k_body, w, apply_cont)
                        });
                        self.compile_pp_expr(s, &value_clone, &kont, w, apply_cont)
                    }
                _ => Err(BackendError::new("compile_pp_expr: unsupported let binding")),
            },
            _ => Err(BackendError::new("compile_pp_expr: unsupported expr")),
        }
    }

    fn compile_pp_exprs(
        &mut self,
        s: Scope,
        exprs: &[AExpr],
        k: &Kont,
        w: Code,
        apply_cont: i32,
    ) -> Result<Code, BackendError> {
        if exprs.is_empty() {
            return k(s, w, self);
        }
        let (first, rest) = exprs.split_first().expect("non-empty");
        let rest_vec = rest.to_vec();
        let k_clone = Rc::clone(k);
        let kont: Kont = Rc::new(move |s_after: Scope, w: Code, this: &mut Compiler| {
            this.compile_pp_exprs(s_after, &rest_vec, &k_clone, w, apply_cont)
        });
        self.compile_pp_expr(s, first, &kont, w, apply_cont)
    }

    fn compile_payload(
        &mut self,
        s_after: &Scope,
        pats: &[Pattern],
        expr: &AExpr,
        rest_code: Code,
        x_val: &Code,
        k: &Kont,
        w: &Code,
        apply_cont: i32,
    ) -> Result<Code, BackendError> {
        let eq_int = |lhs: Code, rhs: Code| code(format!("({} = {})", uncode(lhs), uncode(rhs)));
        if pats.is_empty() {
            return Ok(seqs_(vec![
                to_unit_(pop_env_(w.clone())),
                self.compile_pp_expr(s_after.clone(), expr, k, w.clone(), apply_cont)?,
            ]));
        }
        let splits = memo_splits_(pair_value_(x_val.clone()));
        with_splits(pats.len(), splits, |values| {
            if values.len() != pats.len() {
                return Err(BackendError::new("compile_pp_cases: arity mismatch"));
            }
            let mut conds = Vec::new();
            let mut binds: Vec<(String, Code)> = Vec::new();
            for (pat, value) in pats.iter().zip(values.iter()) {
                match pat {
                    Pattern::Var(name) => binds.push((name.clone(), value.clone())),
                    Pattern::Any => {}
                    Pattern::Int(i) => {
                        conds.push(eq_int(
                            word_get_value_(memo_to_word_(value.clone())),
                            int_lit_(*i),
                        ));
                    }
                    Pattern::Bool(b) => {
                        let v = if *b { 1 } else { 0 };
                        conds.push(eq_int(
                            word_get_value_(memo_to_word_(value.clone())),
                            int_(v),
                        ));
                    }
                    Pattern::Unit => {
                        conds.push(eq_int(word_get_value_(memo_to_word_(value.clone())), int_(0)));
                    }
                    _ => return Err(BackendError::new("compile_pp_cases: unsupported pattern")),
                }
            }
            let mut seqs = Vec::new();
            seqs.push(to_unit_(pop_env_(w.clone())));
            for (_, value) in &binds {
                seqs.push(push_env_(w.clone(), value.clone()));
            }
            if binds.is_empty() {
                seqs.push(self.compile_pp_expr(
                    s_after.clone(),
                    expr,
                    k,
                    w.clone(),
                    apply_cont,
                )?);
            } else {
                let mut scope = s_after.clone();
                for (name, _) in &binds {
                    scope = scope.extend(name)?;
                }
                let drop_names = binds
                    .iter()
                    .rev()
                    .map(|(name, _)| name.clone())
                    .collect::<Vec<_>>();
                let k_clone = Rc::clone(k);
                let k_drop: Kont = Rc::new(move |s_body: Scope, w_body: Code, this: &mut Compiler| {
                    this.drop_vars(s_body, &drop_names, w_body, &k_clone)
                });
                seqs.push(self.compile_pp_expr(
                    scope,
                    expr,
                    &k_drop,
                    w.clone(),
                    apply_cont,
                )?);
            }
            let branch = seqs_(seqs);
            if conds.is_empty() {
                Ok(branch)
            } else {
                let cond = if conds.len() == 1 {
                    conds[0].clone()
                } else {
                    let cond_doc = conds
                        .iter()
                        .map(|c| uncode(c.clone()))
                        .collect::<Vec<_>>()
                        .join(" && ");
                    code(format!("({cond_doc})"))
                };
                Ok(if_(cond, branch, rest_code.clone()))
            }
        })
    }

    fn compile_case_list(
        &mut self,
        s_after: &Scope,
        cases: &[(Pattern, AExpr)],
        x_val: &Code,
        k: &Kont,
        w: &Code,
        apply_cont: i32,
    ) -> Result<Code, BackendError> {
        let eq_int = |lhs: Code, rhs: Code| code(format!("({} = {})", uncode(lhs), uncode(rhs)));
        if cases.is_empty() {
            return Ok(unreachable_(self.codes.len() as i32));
        }
        let (pat, expr) = cases.first().expect("non-empty");
        let rest = &cases[1..];
        let rest_code = self.compile_case_list(s_after, rest, x_val, k, w, apply_cont)?;
        let head = word_get_value_(zro_(x_val.clone()));
        match pat {
            Pattern::Any => Ok(seqs_(vec![
                to_unit_(pop_env_(w.clone())),
                self.compile_pp_expr(s_after.clone(), expr, k, w.clone(), apply_cont)?,
            ])),
            Pattern::Var(name) => {
                let name = name.clone();
                let scope = s_after.clone().extend(&name)?;
                let drop_names = vec![name.clone()];
                let k_clone = Rc::clone(k);
                let k_drop: Kont = Rc::new(move |s_body: Scope, w_body: Code, this: &mut Compiler| {
                    this.drop_vars(s_body, &drop_names, w_body, &k_clone)
                });
                Ok(seqs_(vec![
                    push_env_(w.clone(), get_env_(w.clone(), int_(s_after.env_length as i32))),
                    to_unit_(pop_env_(w.clone())),
                    self.compile_pp_expr(scope, expr, &k_drop, w.clone(), apply_cont)?,
                ]))
            }
            Pattern::Int(i) => {
                let cond = eq_int(head, int_lit_(*i));
                let branch = seqs_(vec![
                    to_unit_(pop_env_(w.clone())),
                    self.compile_pp_expr(s_after.clone(), expr, k, w.clone(), apply_cont)?,
                ]);
                Ok(if_(cond, branch, rest_code))
            }
            Pattern::Bool(b) => {
                let v = if *b { 1 } else { 0 };
                let cond = eq_int(head, int_(v));
                let branch = seqs_(vec![
                    to_unit_(pop_env_(w.clone())),
                    self.compile_pp_expr(s_after.clone(), expr, k, w.clone(), apply_cont)?,
                ]);
                Ok(if_(cond, branch, rest_code))
            }
            Pattern::Unit => {
                let cond = eq_int(head, int_(0));
                let branch = seqs_(vec![
                    to_unit_(pop_env_(w.clone())),
                    self.compile_pp_expr(s_after.clone(), expr, k, w.clone(), apply_cont)?,
                ]);
                Ok(if_(cond, branch, rest_code))
            }
            Pattern::CtorApp { name, args } => {
                let cond = eq_int(head, self.ctx.ctor_tag_name(name));
                let pats = match args {
                    None => Vec::new(),
                    Some(args) if args.len() == 1 => match &args[0] {
                        Pattern::Tup(items) => items.clone(),
                        _ => args.clone(),
                    },
                    Some(args) => args.clone(),
                };
                let branch = self.compile_payload(
                    s_after,
                    &pats,
                    expr,
                    rest_code.clone(),
                    x_val,
                    k,
                    w,
                    apply_cont,
                )?;
                Ok(if_(cond, branch, rest_code))
            }
            Pattern::Tup(items) => {
                let name = self.ensure_tuple_ctor(items.len());
                let cond = eq_int(head, self.ctx.ctor_tag_name(&name));
                let branch = self.compile_payload(
                    s_after,
                    items,
                    expr,
                    rest_code.clone(),
                    x_val,
                    k,
                    w,
                    apply_cont,
                )?;
                Ok(if_(cond, branch, rest_code))
            }
            _ => Err(BackendError::new("compile_pp_cases: unsupported pattern")),
        }
    }

    fn compile_pp_cases(
        &mut self,
        s: Scope,
        cases: &[(Pattern, AExpr)],
        k: &Kont,
        w: Code,
        apply_cont: i32,
    ) -> Result<Code, BackendError> {
        let s_after = s.pop()?;
        let last_expr = src_E_(s.env_length as i32 - 1);
        let body = let_in_result_("last", last_expr, |last_var| {
            let_in_result_("x", resolve_(w.clone(), last_var.clone()), |x_var| {
                self.compile_case_list(&s_after, cases, &x_var, k, &w, apply_cont)
            })
        })?;
        Ok(seqs_(vec![
            assert_env_length_(w.clone(), int_(s.env_length as i32)),
            body,
        ]))
    }

    fn compile_pp_stmt(&mut self, stmt: &AStmt, apply_cont: i32) -> Result<String, BackendError> {
        let cont_done_tag = self.ctx.ctor_tag_name("cont_done");
        let compile_binding = |this: &mut Compiler,
                               name: &str,
                               expr: &AExpr,
                               entry_code: i32|
         -> Result<String, BackendError> {
            let (params, term): (Vec<Pattern>, &AExpr) = match &expr.kind {
                AExprKind::Lam(params, term) => (params.clone(), term),
                _ => (Vec::new(), expr),
            };
            let mut s = Scope::new();
            for p in &params {
                match p {
                    Pattern::Var(n) => s = s.extend(n)?,
                    _ => {
                        return Err(BackendError::new(
                            "compile_pp_stmt: unsupported param pattern",
                        ))
                    }
                }
            }
            let arg_num = s.env_length;
            let k_return: Kont = Rc::new(move |s, w, this| this.return_expr(s, w, apply_cont));
            let code = lam_result_("w", |w| this.compile_pp_expr(s.clone(), term, &k_return, w, apply_cont))?;
            this.set_code(entry_code, code)?;
            let mut args = Vec::new();
            for i in 0..arg_num {
                args.push(format!("(x{i} : Value.seq)"));
            }
            let arg_list = args.join(" ");
            let mut arg_vals = Vec::new();
            for i in 0..arg_num {
                arg_vals.push(format!("(x{i})"));
            }
            let arg_vals = arg_vals.join(";");
            let doc = format!(
                "{name} memo {arg_list}: exec_result = (exec_cek (pc_to_exp (int_to_pc {entry_code}))(Dynarray.of_list[{arg_vals}])({}) memo)",
                uncode(from_constructor_(cont_done_tag.clone())),
            );
            Ok(doc)
        };
        let compile_toplevel =
            |this: &mut Compiler, expr: &AExpr, entry_code: i32| -> Result<String, BackendError> {
                let k_return: Kont =
                    Rc::new(move |s, w, this| this.return_expr(s, w, apply_cont));
                let code =
                    lam_result_("w", |w| this.compile_pp_expr(Scope::new(), expr, &k_return, w, apply_cont))?;
                this.set_code(entry_code, code)?;
                Ok(format!(
                    "let () = ignore ((exec_cek (pc_to_exp (int_to_pc {entry_code}))(Dynarray.of_list[])({}) (init_memo ())))",
                    uncode(from_constructor_(cont_done_tag.clone())),
                ))
            };
        match stmt {
            AStmt::Type(binding) => {
                match binding {
                    TyBinding::One { name: _, kind } => match kind {
                        TyKind::Enum { ctors, .. } => self.register_constructors(ctors),
                    },
                    TyBinding::Rec(defs) => {
                        for (_, kind) in defs {
                            if let TyKind::Enum { ctors, .. } = kind {
                                self.register_constructors(ctors);
                            }
                        }
                    }
                }
                compile_type_binding(binding)
            }
            AStmt::Term(binding) => match binding {
                ABinding::Seq(expr) => {
                    let entry_code = self.add_code(None);
                    compile_toplevel(self, expr, entry_code)
                }
                ABinding::One(Pattern::Any, expr) => {
                    let entry_code = self.add_code(None);
                    compile_toplevel(self, expr, entry_code)
                }
                ABinding::One(Pattern::Var(name), expr) => {
                    if name == "_" {
                        let entry_code = self.add_code(None);
                        compile_toplevel(self, expr, entry_code)
                    } else {
                        let entry_code = self.add_code(None);
                        self.ctx.func_pc.insert(name.clone(), entry_code);
                        let doc = compile_binding(self, name, expr, entry_code)?;
                        Ok(format!("let rec {doc}"))
                    }
                }
                ABinding::Rec(bindings) => {
                    let mut entries: Vec<(String, AExpr)> = Vec::new();
                    for (pat, expr) in bindings {
                        match pat {
                            Pattern::Var(name) => entries.push((name.clone(), (*expr.clone()))),
                            _ => {
                                return Err(BackendError::new(
                                    "compile_pp_stmt: unsupported binding pattern",
                                ))
                            }
                        }
                    }
                    if entries.is_empty() {
                        return Err(BackendError::new("compile_pp_stmt: empty recursive binding"));
                    }
                    let pcs = entries.iter().map(|_| self.add_code(None)).collect::<Vec<_>>();
                    for ((name, _), pc) in entries.iter().zip(pcs.iter()) {
                        self.ctx.func_pc.insert(name.clone(), *pc);
                    }
                    let mut docs = Vec::new();
                    for ((name, expr), pc) in entries.iter().zip(pcs.iter()) {
                        docs.push(compile_binding(self, name, expr, *pc)?);
                    }
                    let mut out = String::new();
                    out.push_str("let rec ");
                    out.push_str(&docs[0]);
                    for doc in docs.iter().skip(1) {
                        out.push_str("\nand ");
                        out.push_str(doc);
                    }
                    Ok(out)
                }
                _ => Err(BackendError::new("compile_pp_stmt: unsupported term")),
            },
        }
    }

    fn generate_apply_cont(&mut self, apply_cont: i32) -> Result<(), BackendError> {
        let code = lam_result_("w", |w| {
            let hd = genvar("hd");
            let tl = genvar("tl");
            let mut cont_codes: Vec<(String, Code)> = Vec::new();
            let mut i = 0usize;
            loop {
                if i >= self.ctx.conts.len() {
                    break;
                }
                let (name, action) = {
                    let (name, action) = &self.ctx.conts[i];
                    (name.clone(), Rc::clone(action))
                };
                let tag_name = self
                    .ctx
                    .ctag_name
                    .get(&name)
                    .cloned()
                    .unwrap_or_else(|| Ctx::get_ctor_tag_name(&name));
                let code = action(w.clone(), tl.0.clone(), self)?;
                cont_codes.push((tag_name, code));
                i += 1;
            }
            let pat = pair_pat_(hd.1.clone(), tl.1.clone());
            let body = match_ctor_tag_default_(
                word_get_value_(hd.0.clone()),
                cont_codes,
                unreachable_(apply_cont),
            );
            Ok(seqs_(vec![
                assert_env_length_(w.clone(), int_(1)),
                let_pat_in_(pat, resolve_(w.clone(), raw("K")), paren(body)),
            ]))
        })?;
        self.set_code(apply_cont, code)
    }

    fn ctor_tag_decls(&self) -> String {
        let mut xs = self
            .ctx
            .ctag
            .iter()
            .map(|(name, tag)| (name.clone(), *tag))
            .collect::<Vec<_>>();
        xs.sort_by_key(|(_, tag)| *tag);
        xs.iter()
            .map(|(name, tag)| format!("let {} = {}", Ctx::get_ctor_tag_name(name), tag))
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn pp_cek_ant(&mut self, stmts: &[AStmt]) -> Result<String, BackendError> {
        let apply_cont = self.apply_cont_pc();
        let mut generated = Vec::new();
        for stmt in stmts {
            generated.push(self.compile_pp_stmt(stmt, apply_cont)?);
        }
        self.generate_apply_cont(apply_cont)?;
        let mut out = String::new();
        out.push_str("open Ant\n");
        out.push_str("open Word\n");
        out.push_str("open Memo\n");
        out.push_str("open Value\n");
        out.push_str("open Common\n");
        out.push_str(&self.ctor_tag_decls());
        out.push('\n');
        out.push_str(&generated.join("\n"));
        out.push('\n');
        for (i, code) in self.codes.iter().enumerate() {
            let Some(code) = code else { continue };
            out.push_str("let () = add_exp ");
            out.push_str(&uncode(code.clone()));
            out.push(' ');
            out.push_str(&i.to_string());
            if i + 1 < self.codes.len() {
                out.push('\n');
            }
        }
        out.push('\n');
        for (i, degree) in self.ctx.constructor_degree.iter().enumerate() {
            out.push_str("let () = Words.set_constructor_degree ");
            out.push_str(&i.to_string());
            out.push_str(" (");
            out.push_str(&degree.to_string());
            out.push(')');
            if i + 1 < self.ctx.constructor_degree.len() {
                out.push('\n');
            }
        }
        Ok(out)
    }
}

fn compile_ty(ty: &Ty) -> Result<String, BackendError> {
    Ok(match ty {
        Ty::Unit => "unit".to_string(),
        Ty::Int => "int".to_string(),
        Ty::Float => "float".to_string(),
        Ty::Bool => "bool".to_string(),
        Ty::Apply(base, args) => {
            if args.is_empty() {
                compile_ty(base)?
            } else if args.len() == 1 {
                format!("{} {}", compile_ty(&args[0])?, compile_ty(base)?)
            } else {
                let inner = args.iter().map(compile_ty).collect::<Result<Vec<_>, _>>()?.join(",");
                format!("({}) {}", inner, compile_ty(base)?)
            }
        }
        Ty::Arrow(lhs, rhs) => format!("{} -> {}", compile_ty(lhs)?, compile_ty(rhs)?),
        Ty::Tuple(items) => {
            let inner = items.iter().map(compile_ty).collect::<Result<Vec<_>, _>>()?.join("*");
            format!("({inner})")
        }
        Ty::Named(name) => name.clone(),
        Ty::NamedVar(name) => format!("'{name}"),
    })
}

fn compile_type_binding(binding: &TyBinding) -> Result<String, BackendError> {
    let mut out = String::new();
    match binding {
        TyBinding::One { name, kind } => {
            if let TyKind::Enum { params, ctors } = kind {
                let mut params_str = String::new();
                if !params.is_empty() {
                    if params.len() == 1 {
                        params_str = format!("'{} ", params[0]);
                    } else {
                        let inner = params.iter().map(|p| format!("'{p}")).collect::<Vec<_>>().join(",");
                        params_str = format!("({}) ", inner);
                    }
                }
                let mut ctor_parts = Vec::new();
                for ctor in ctors {
                    if ctor.args.is_empty() {
                        ctor_parts.push(ctor.name.clone());
                    } else {
                        let args = ctor
                            .args
                            .iter()
                            .map(compile_ty)
                            .collect::<Result<Vec<_>, _>>()?
                            .join(" * ");
                        ctor_parts.push(format!("{} of {}", ctor.name, args));
                    }
                }
                out.push_str(&format!("type {params_str}{name} = | {};;", ctor_parts.join(" | ")));
                out.push('\n');
                let (from_doc, to_doc) = compile_type_conversions(name, params, ctors, true)?;
                out.push_str(&from_doc);
                out.push_str(&to_doc);
            }
        }
        TyBinding::Rec(defs) => {
            let mut first = true;
            for (name, kind) in defs {
                if let TyKind::Enum { params, ctors } = kind {
                    let mut params_str = String::new();
                    if !params.is_empty() {
                        if params.len() == 1 {
                            params_str = format!("'{} ", params[0]);
                        } else {
                            let inner = params.iter().map(|p| format!("'{p}")).collect::<Vec<_>>().join(",");
                            params_str = format!("({}) ", inner);
                        }
                    }
                    let mut ctor_parts = Vec::new();
                    for ctor in ctors {
                        if ctor.args.is_empty() {
                            ctor_parts.push(ctor.name.clone());
                        } else {
                            let args = ctor
                                .args
                                .iter()
                                .map(compile_ty)
                                .collect::<Result<Vec<_>, _>>()?
                                .join(" * ");
                            ctor_parts.push(format!("{} of {}", ctor.name, args));
                        }
                    }
                    if first {
                        out.push_str(&format!("type {params_str}{name} = | {}", ctor_parts.join(" | ")));
                        first = false;
                    } else {
                        out.push_str(&format!("\nand {params_str}{name} = | {}", ctor_parts.join(" | ")));
                    }
                }
            }
            out.push_str(";;\n");
            let mut from_docs = Vec::new();
            let mut to_docs = Vec::new();
            let mut first_conv = true;
            for (name, kind) in defs {
                if let TyKind::Enum { params, ctors } = kind {
                    let (from_doc, to_doc) =
                        compile_type_conversions(name, params, ctors, first_conv)?;
                    first_conv = false;
                    from_docs.push(from_doc);
                    to_docs.push(to_doc);
                }
            }
            for doc in from_docs {
                out.push_str(&doc);
            }
            out.push_str(&to_docs.join("\n"));
        }
    }
    Ok(out)
}

fn compile_conv(is_to: bool, ty: &Ty, v: &str) -> Result<String, BackendError> {
    Ok(match ty {
        Ty::Unit => {
            if is_to {
                format!("(ignore (Word.get_value (Memo.to_word {v})); ())")
            } else {
                "(Memo.from_int 0)".to_string()
            }
        }
        Ty::Int => {
            if is_to {
                format!("(Word.get_value (Memo.to_word {v}))")
            } else {
                format!("(Memo.from_int {v})")
            }
        }
        Ty::Bool => {
            if is_to {
                format!("(Word.get_value (Memo.to_word {v}) <> 0)")
            } else {
                format!("(Memo.from_int (if {v} then 1 else 0))")
            }
        }
        Ty::Named(n) => {
            let fname = if is_to { format!("to_ocaml_{n}") } else { format!("from_ocaml_{n}") };
            format!("{fname} {v}")
        }
        Ty::NamedVar(n) => {
            let fname = if is_to { format!("to_generic_{n}") } else { format!("from_generic_{n}") };
            format!("{fname} {v}")
        }
        Ty::Apply(base, args) => {
            if let Ty::Named(n) = &**base {
                let fname = if is_to { format!("to_ocaml_{n}") } else { format!("from_ocaml_{n}") };
                let mut args_conv = Vec::new();
                for arg in args {
                    args_conv.push(format!("(fun x -> {})", compile_conv(is_to, arg, "x")?));
                }
                if args_conv.is_empty() {
                    format!("{fname} {v}")
                } else {
                    format!("{fname} {} {v}", args_conv.join(" "))
                }
            } else {
                "failwith \"complex type not supported\"".to_string()
            }
        }
        Ty::Tuple(_) => "failwith \"tuples not supported directly\"".to_string(),
        _ => "failwith \"complex type not supported\"".to_string(),
    })
}

fn compile_type_conversions(
    name: &str,
    params: &[String],
    ctors: &[TyCtor],
    is_first: bool,
) -> Result<(String, String), BackendError> {
    let prefix = if is_first { "let rec" } else { "and" };
    let params_from = if params.is_empty() {
        String::new()
    } else {
        format!(
            "{} ",
            params
                .iter()
                .map(|p| format!("from_generic_{p}"))
                .collect::<Vec<_>>()
                .join(" ")
        )
    };
    let params_to = if params.is_empty() {
        String::new()
    } else {
        format!(
            "{} ",
            params
                .iter()
                .map(|p| format!("to_generic_{p}"))
                .collect::<Vec<_>>()
                .join(" ")
        )
    };
    let mut from_doc = String::new();
    from_doc.push_str(&format!(
        "{prefix} from_ocaml_{name} {params_from}x =\n"
    ));
    from_doc.push_str("  match x with\n");
    for ctor in ctors {
        if ctor.args.is_empty() {
            from_doc.push_str(&format!("  | {} ->\n", ctor.name));
            from_doc.push_str(&format!(
                "    Memo.appends [Memo.from_constructor tag_{}]\n",
                ctor.name
            ));
        } else {
            let args: Vec<String> = (0..ctor.args.len()).map(|i| format!("x{i}")).collect();
            from_doc.push_str(&format!("  | {} ({}) ->\n", ctor.name, args.join(", ")));
            let mut body_parts = Vec::new();
            body_parts.push(format!("Memo.from_constructor tag_{}", ctor.name));
            for (i, ty) in ctor.args.iter().enumerate() {
                body_parts.push(compile_conv(false, ty, &format!("x{i}"))?);
            }
            from_doc.push_str(&format!("    Memo.appends [{}]\n", body_parts.join("; ")));
        }
    }
    let mut to_doc = String::new();
    to_doc.push_str(&format!(
        "{prefix} to_ocaml_{name} {params_to}x =\n"
    ));
    to_doc.push_str("  let h, t = Option.get (Memo.list_match x) in\n");
    to_doc.push_str("  match Word.get_value h with");
    for ctor in ctors {
        to_doc.push_str(&format!("| c when c = tag_{} ->\n", ctor.name));
        if ctor.args.is_empty() {
            to_doc.push_str(&format!("    {}", ctor.name));
        } else {
            let vars: Vec<String> = (0..ctor.args.len()).map(|i| format!("x{i}")).collect();
            if ctor.args.len() > 4 {
                to_doc.push_str("    let args_list = Memo.splits t in\n");
                for (i, v) in vars.iter().enumerate() {
                    to_doc.push_str(&format!("    let {v} = List.nth args_list {i} in\n"));
                }
            } else {
                let split_fn = format!("Memo.splits_{}", ctor.args.len());
                if ctor.args.len() == 1 {
                    to_doc.push_str(&format!("    let {} = {} t in\n", vars[0], split_fn));
                } else {
                    to_doc.push_str(&format!("    let ({}) = {} t in\n", vars.join(", "), split_fn));
                }
            }
            let mut conv_args = Vec::new();
            for (i, ty) in ctor.args.iter().enumerate() {
                conv_args.push(compile_conv(true, ty, &format!("x{i}"))?);
            }
            to_doc.push_str(&format!("    {} ({})", ctor.name, conv_args.join(", ")));
        }
    }
    to_doc.push_str("\n  | _ -> failwith \"unreachable\"");
    Ok((from_doc, to_doc))
}

pub fn compile_memo(prog: &Prog) -> Result<String, BackendError> {
    reset_gensym();
    let stmts = annotate_prog_with_liveness(prog)?;
    let mut compiler = Compiler::new();
    compiler.pp_cek_ant(&stmts)
}

trait Pipe: Sized {
    fn pipe<T>(self, f: impl FnOnce(Self) -> T) -> T {
        f(self)
    }
}

impl<T> Pipe for T {}
