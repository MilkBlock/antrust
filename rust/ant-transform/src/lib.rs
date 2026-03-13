use ant_frontend::{pp_expr, pp_pattern, Binding, Expr, Pattern, Prog, Stmt, TyBinding, TyKind};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

type ArityCtx = HashMap<String, usize>;
type DefuncCtx = HashMap<String, String>;
type Kont = Rc<dyn Fn(Expr) -> TransformResult<Expr>>;
type KontList = Rc<dyn Fn(Vec<Expr>) -> TransformResult<Expr>>;

type Case = (Pattern, Expr);

#[derive(Debug, Clone)]
pub struct TransformError {
    message: String,
}

impl TransformError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }

    fn cps_scan_ctors_arity_assertion_failed() -> Self {
        Self::new("File \"lib/Transform.ml\", line 194, characters 14-20: Assertion failed")
    }

    fn defunc_assertion_failed() -> Self {
        Self::new("File \"lib/Transform.ml\", line 325, characters 4-10: Assertion failed")
    }
}

impl fmt::Display for TransformError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for TransformError {}

type TransformResult<T> = Result<T, TransformError>;

#[derive(Default)]
struct Fresh {
    counter: i32,
}

impl Fresh {
    fn next_fresh(&mut self, prefix: &str) -> String {
        let i = self.counter;
        self.counter += 1;
        format!("{prefix}{i}")
    }
}

fn mk_fresh(fresh: &Rc<RefCell<Fresh>>, prefix: &str) -> (Pattern, Expr) {
    let name = fresh.borrow_mut().next_fresh(prefix);
    (Pattern::Var(name.clone()), Expr::Var(name))
}

fn mk_fresh_params(
    fresh: &Rc<RefCell<Fresh>>,
    n: usize,
    prefix: &str,
) -> (Vec<Pattern>, Vec<Expr>) {
    let mut pats = Vec::with_capacity(n);
    let mut vars = Vec::with_capacity(n);
    for _ in 0..n {
        let name = fresh.borrow_mut().next_fresh(prefix);
        pats.push(Pattern::Var(name.clone()));
        vars.push(Expr::Var(name));
    }
    (pats, vars)
}

fn is_atomic(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Unit
            | Expr::Int(_)
            | Expr::Bool(_)
            | Expr::Str(_)
            | Expr::Builtin(_)
            | Expr::Var(_)
            | Expr::GVar(_)
            | Expr::Ctor(_)
            | Expr::Lam(_, _)
    )
}

fn atom(ctx: &Rc<ArityCtx>, expr: &Expr, fresh: &Rc<RefCell<Fresh>>) -> TransformResult<Expr> {
    match expr {
        Expr::Unit => Ok(Expr::Unit),
        Expr::Int(i) => Ok(Expr::Int(*i)),
        Expr::Bool(b) => Ok(Expr::Bool(*b)),
        Expr::Str(s) => Ok(Expr::Str(s.clone())),
        Expr::Builtin(b) => Ok(Expr::Builtin(b.clone())),
        Expr::Var(x) => Ok(Expr::Var(x.clone())),
        Expr::GVar(x) => Ok(Expr::GVar(x.clone())),
        Expr::Ctor(x) => {
            let n = ctx
                .get(x)
                .copied()
                .ok_or_else(|| TransformError::new("Not_found"))?;
            if n == 0 {
                Ok(Expr::Ctor(x.clone()))
            } else {
                let (pas, vas) = mk_fresh_params(fresh, n, "_'a");
                let (pks, vks) = mk_fresh_params(fresh, n, "_'k");
                let mut acc = Expr::App(Box::new(Expr::Ctor(x.clone())), vas);
                let mut pairs = Vec::new();
                for (pa, (pk, vk)) in pas
                    .into_iter()
                    .zip(pks.into_iter().zip(vks.into_iter()))
                {
                    pairs.push((pa, pk, vk));
                }
                for (pa, pk, vk) in pairs.into_iter().rev() {
                    let body = Expr::App(Box::new(vk), vec![acc]);
                    acc = Expr::Lam(vec![pa, pk], Box::new(body));
                }
                Ok(acc)
            }
        }
        Expr::Lam(params, body) => {
            let (pk, vk) = mk_fresh(fresh, "_'k");
            let mut new_params = params.clone();
            new_params.push(pk);
            let body = cps_double_prime(ctx.clone(), (**body).clone(), vk, fresh.clone())?;
            Ok(Expr::Lam(new_params, Box::new(body)))
        }
        _ => Err(TransformError::new(format!(
            "not an atom: {}",
            pp_expr(expr, false, 0)
        ))),
    }
}

fn cps_list(
    ctx: Rc<ArityCtx>,
    exprs: Vec<Expr>,
    k: KontList,
    fresh: Rc<RefCell<Fresh>>,
) -> TransformResult<Expr> {
    if exprs.is_empty() {
        return k(Vec::new());
    }
    let head = exprs[0].clone();
    let tail = exprs[1..].to_vec();
    let ctx_tail = ctx.clone();
    let fresh_tail = fresh.clone();
    let k_tail = k.clone();
    let tail_clone = tail.clone();
    cps_prime(
        ctx,
        head,
        Rc::new(move |head_cps| {
            let ctx_inner = ctx_tail.clone();
            let fresh_inner = fresh_tail.clone();
            let k_inner = k_tail.clone();
            let tail_inner = tail_clone.clone();
            cps_list(
                ctx_inner,
                tail_inner,
                Rc::new(move |mut rest_cps| {
                    let mut out = Vec::with_capacity(rest_cps.len() + 1);
                    out.push(head_cps.clone());
                    out.append(&mut rest_cps);
                    k_inner(out)
                }),
                fresh_inner,
            )
        }),
        fresh,
    )
}

fn cps_prime(
    ctx: Rc<ArityCtx>,
    expr: Expr,
    k: Kont,
    fresh: Rc<RefCell<Fresh>>,
) -> TransformResult<Expr> {
    if is_atomic(&expr) {
        return k(atom(&ctx, &expr, &fresh)?);
    }
    match expr {
        Expr::App(f, xs) => {
            let ctx_f = ctx.clone();
            let fresh_f = fresh.clone();
            let k_f = k.clone();
            let xs_clone = xs.clone();
            cps_prime(
                ctx,
                *f,
                Rc::new(move |f_cps| {
                    let ctx_x = ctx_f.clone();
                    let fresh_x = fresh_f.clone();
                    let k_x = k_f.clone();
                    let xs_inner = xs_clone.clone();
                    let fresh_for_list = fresh_x.clone();
                    cps_list(
                        ctx_x,
                        xs_inner,
                        Rc::new(move |xs_cps| {
                            let (pa, va) = mk_fresh(&fresh_x, "_'a");
                            let (pc, vc) = mk_fresh(&fresh_x, "_'cont");
                            let cont_lam =
                                Expr::Lam(vec![pa.clone()], Box::new(k_x(va.clone())?));
                            let binding = Binding::One(pc.clone(), Box::new(cont_lam));
                            let mut args = xs_cps;
                            args.push(vc);
                            Ok(Expr::Let(
                                Box::new(binding),
                                Box::new(Expr::App(Box::new(f_cps.clone()), args)),
                            ))
                        }),
                        fresh_for_list,
                    )
                }),
                fresh,
            )
        }
        Expr::Op(op, e1, e2) => {
            let ctx_e2 = ctx.clone();
            let fresh_e2 = fresh.clone();
            let k_e2 = k.clone();
            cps_prime(
                ctx,
                *e1,
                Rc::new(move |e1_cps| {
                    let ctx_inner = ctx_e2.clone();
                    let fresh_inner = fresh_e2.clone();
                    let k_inner = k_e2.clone();
                    let op_inner = op.clone();
                    cps_prime(
                        ctx_inner,
                        *e2.clone(),
                        Rc::new(move |e2_cps| {
                            k_inner(Expr::Op(
                                op_inner.clone(),
                                Box::new(e1_cps.clone()),
                                Box::new(e2_cps),
                            ))
                        }),
                        fresh_inner,
                    )
                }),
                fresh,
            )
        }
        Expr::Tup(items) => {
            let fresh_items = fresh.clone();
            let k_items = k.clone();
            cps_list(
                ctx,
                items,
                Rc::new(move |items_cps| k_items(Expr::Tup(items_cps))),
                fresh_items,
            )
        }
        Expr::Arr(items) => {
            let fresh_items = fresh.clone();
            let k_items = k.clone();
            cps_list(
                ctx,
                items,
                Rc::new(move |items_cps| k_items(Expr::Arr(items_cps))),
                fresh_items,
            )
        }
        Expr::Let(binding, body) => match *binding {
            Binding::One(pat, expr) => {
                let ctx_body = ctx.clone();
                let fresh_body = fresh.clone();
                let k_body = k.clone();
                cps_prime(
                    ctx,
                    *expr,
                    Rc::new(move |expr_cps| {
                        let body_cps = cps_prime(
                            ctx_body.clone(),
                            *body.clone(),
                            k_body.clone(),
                            fresh_body.clone(),
                        )?;
                        Ok(Expr::Let(
                            Box::new(Binding::One(pat.clone(), Box::new(expr_cps))),
                            Box::new(body_cps),
                        ))
                    }),
                    fresh,
                )
            }
            Binding::Rec(bindings) => {
                let pats: Vec<Pattern> = bindings.iter().map(|(p, _)| p.clone()).collect();
                let rhs: Vec<Expr> = bindings.iter().map(|(_, e)| *e.clone()).collect();
                let ctx_body = ctx.clone();
                let fresh_body = fresh.clone();
                let k_body = k.clone();
                cps_list(
                    ctx,
                    rhs,
                    Rc::new(move |rhs_cps| {
                        let mut new_bindings = Vec::with_capacity(rhs_cps.len());
                        for (pat, expr_cps) in pats.iter().cloned().zip(rhs_cps.into_iter()) {
                            new_bindings.push((pat, Box::new(expr_cps)));
                        }
                        let body_cps = cps_prime(
                            ctx_body.clone(),
                            *body.clone(),
                            k_body.clone(),
                            fresh_body.clone(),
                        )?;
                        Ok(Expr::Let(
                            Box::new(Binding::Rec(new_bindings)),
                            Box::new(body_cps),
                        ))
                    }),
                    fresh,
                )
            }
            Binding::Seq(expr) => {
                let ctx_body = ctx.clone();
                let fresh_body = fresh.clone();
                let k_body = k.clone();
                cps_prime(
                    ctx,
                    *expr,
                    Rc::new(move |expr_cps| {
                        let body_cps = cps_prime(
                            ctx_body.clone(),
                            *body.clone(),
                            k_body.clone(),
                            fresh_body.clone(),
                        )?;
                        Ok(Expr::Let(
                            Box::new(Binding::Seq(Box::new(expr_cps))),
                            Box::new(body_cps),
                        ))
                    }),
                    fresh,
                )
            }
        },
        Expr::Sel(expr, field) => {
            let fresh_sel = fresh.clone();
            let k_sel = k.clone();
            cps_prime(
                ctx,
                *expr,
                Rc::new(move |expr_cps| k_sel(Expr::Sel(Box::new(expr_cps), field.clone()))),
                fresh_sel,
            )
        }
        Expr::If(e1, e2, e3) => {
            let (pk, vk) = mk_fresh(&fresh, "_'k");
            let (pa, va) = mk_fresh(&fresh, "_'a");
            let (pc, vc) = mk_fresh(&fresh, "_'cont");
            let ctx_then = ctx.clone();
            let fresh_then = fresh.clone();
            let k_then = k.clone();
            cps_prime(
                ctx,
                *e1,
                Rc::new(move |cond_cps| {
                    let cont_lam = Expr::Lam(vec![pa.clone()], Box::new(k_then(va.clone())?));
                    let binding = Binding::One(pc.clone(), Box::new(cont_lam));
                    let then_expr =
                        cps_double_prime(ctx_then.clone(), *e2.clone(), vk.clone(), fresh_then.clone())?;
                    let else_expr =
                        cps_double_prime(ctx_then.clone(), *e3.clone(), vk.clone(), fresh_then.clone())?;
                    let inner_lam = Expr::Lam(
                        vec![pk.clone()],
                        Box::new(Expr::If(Box::new(cond_cps), Box::new(then_expr), Box::new(else_expr))),
                    );
                    Ok(Expr::Let(
                        Box::new(binding),
                        Box::new(Expr::App(Box::new(inner_lam), vec![vc.clone()])),
                    ))
                }),
                fresh,
            )
        }
        Expr::Match(cond, cases) => {
            let pats: Vec<Pattern> = cases.iter().map(|(p, _)| p.clone()).collect();
            let arms: Vec<Expr> = cases.iter().map(|(_, e)| e.clone()).collect();
            let ctx_arms = ctx.clone();
            let fresh_arms = fresh.clone();
            let k_arms = k.clone();
            cps_prime(
                ctx,
                *cond,
                Rc::new(move |cond_cps| {
                    let ctx_inner = ctx_arms.clone();
                    let fresh_inner = fresh_arms.clone();
                    let k_inner = k_arms.clone();
                    let pats_inner = pats.clone();
                    cps_list(
                        ctx_inner,
                        arms.clone(),
                        Rc::new(move |arms_cps| {
                            let cases_out = pats_inner
                                .iter()
                                .cloned()
                                .zip(arms_cps.into_iter())
                                .collect::<Vec<_>>();
                            k_inner(Expr::Match(Box::new(cond_cps.clone()), cases_out))
                        }),
                        fresh_inner,
                    )
                }),
                fresh,
            )
        }
        other => Err(TransformError::new(format!(
            "not an valid expr in cps': {}",
            pp_expr(&other, false, 0)
        ))),
    }
}

fn cps_double_prime(
    ctx: Rc<ArityCtx>,
    expr: Expr,
    cont: Expr,
    fresh: Rc<RefCell<Fresh>>,
) -> TransformResult<Expr> {
    if is_atomic(&expr) {
        return Ok(Expr::App(
            Box::new(cont),
            vec![atom(&ctx, &expr, &fresh)?],
        ));
    }
    match expr {
        Expr::App(f, xs) => {
            let ctx_xs = ctx.clone();
            let fresh_xs = fresh.clone();
            let cont_expr = cont.clone();
            cps_prime(
                ctx.clone(),
                *f,
                Rc::new(move |f_cps| {
                    let ctx_inner = ctx_xs.clone();
                    let fresh_inner = fresh_xs.clone();
                    let cont_inner = cont_expr.clone();
                    let xs_inner = xs.clone();
                    cps_list(
                        ctx_inner,
                        xs_inner,
                        Rc::new(move |mut xs_cps| {
                            xs_cps.push(cont_inner.clone());
                            Ok(Expr::App(Box::new(f_cps.clone()), xs_cps))
                        }),
                        fresh_inner,
                    )
                }),
                fresh,
            )
        }
        Expr::Op(op, e1, e2) => {
            let ctx_e2 = ctx.clone();
            let fresh_e2 = fresh.clone();
            let cont_expr = cont.clone();
            cps_prime(
                ctx,
                *e1,
                Rc::new(move |e1_cps| {
                    let ctx_inner = ctx_e2.clone();
                    let fresh_inner = fresh_e2.clone();
                    let cont_inner = cont_expr.clone();
                    let op_inner = op.clone();
                    cps_prime(
                        ctx_inner,
                        *e2.clone(),
                        Rc::new(move |e2_cps| {
                            Ok(Expr::App(
                                Box::new(cont_inner.clone()),
                                vec![Expr::Op(
                                    op_inner.clone(),
                                    Box::new(e1_cps.clone()),
                                    Box::new(e2_cps),
                                )],
                            ))
                        }),
                        fresh_inner,
                    )
                }),
                fresh,
            )
        }
        Expr::Tup(items) => {
            let fresh_items = fresh.clone();
            let cont_expr = cont.clone();
            cps_list(
                ctx,
                items,
                Rc::new(move |items_cps| {
                    Ok(Expr::App(
                        Box::new(cont_expr.clone()),
                        vec![Expr::Tup(items_cps)],
                    ))
                }),
                fresh_items,
            )
        }
        Expr::Arr(items) => {
            let fresh_items = fresh.clone();
            let cont_expr = cont.clone();
            cps_list(
                ctx,
                items,
                Rc::new(move |items_cps| {
                    Ok(Expr::App(
                        Box::new(cont_expr.clone()),
                        vec![Expr::Arr(items_cps)],
                    ))
                }),
                fresh_items,
            )
        }
        Expr::Let(binding, body) => match *binding {
            Binding::One(pat, expr) => {
                let ctx_body = ctx.clone();
                let fresh_body = fresh.clone();
                let cont_expr = cont.clone();
                let k_cont: Kont =
                    Rc::new(move |x| Ok(Expr::App(Box::new(cont_expr.clone()), vec![x])));
                cps_prime(
                    ctx,
                    *expr,
                    Rc::new(move |expr_cps| {
                        let body_cps = cps_prime(
                            ctx_body.clone(),
                            *body.clone(),
                            k_cont.clone(),
                            fresh_body.clone(),
                        )?;
                        Ok(Expr::Let(
                            Box::new(Binding::One(pat.clone(), Box::new(expr_cps))),
                            Box::new(body_cps),
                        ))
                    }),
                    fresh,
                )
            }
            Binding::Rec(bindings) => {
                let pats: Vec<Pattern> = bindings.iter().map(|(p, _)| p.clone()).collect();
                let rhs: Vec<Expr> = bindings.iter().map(|(_, e)| *e.clone()).collect();
                let ctx_body = ctx.clone();
                let fresh_body = fresh.clone();
                let cont_expr = cont.clone();
                let k_cont: Kont =
                    Rc::new(move |x| Ok(Expr::App(Box::new(cont_expr.clone()), vec![x])));
                cps_list(
                    ctx,
                    rhs,
                    Rc::new(move |rhs_cps| {
                        let mut new_bindings = Vec::with_capacity(rhs_cps.len());
                        for (pat, expr_cps) in pats.iter().cloned().zip(rhs_cps.into_iter()) {
                            new_bindings.push((pat, Box::new(expr_cps)));
                        }
                        let body_cps = cps_prime(
                            ctx_body.clone(),
                            *body.clone(),
                            k_cont.clone(),
                            fresh_body.clone(),
                        )?;
                        Ok(Expr::Let(
                            Box::new(Binding::Rec(new_bindings)),
                            Box::new(body_cps),
                        ))
                    }),
                    fresh,
                )
            }
            Binding::Seq(expr) => {
                let ctx_body = ctx.clone();
                let fresh_body = fresh.clone();
                let cont_expr = cont.clone();
                let k_cont: Kont =
                    Rc::new(move |x| Ok(Expr::App(Box::new(cont_expr.clone()), vec![x])));
                cps_prime(
                    ctx,
                    *expr,
                    Rc::new(move |expr_cps| {
                        let body_cps = cps_prime(
                            ctx_body.clone(),
                            *body.clone(),
                            k_cont.clone(),
                            fresh_body.clone(),
                        )?;
                        Ok(Expr::Let(
                            Box::new(Binding::Seq(Box::new(expr_cps))),
                            Box::new(body_cps),
                        ))
                    }),
                    fresh,
                )
            }
        },
        Expr::Sel(expr, field) => {
            let fresh_sel = fresh.clone();
            let cont_expr = cont.clone();
            cps_prime(
                ctx,
                *expr,
                Rc::new(move |expr_cps| {
                    Ok(Expr::App(
                        Box::new(cont_expr.clone()),
                        vec![Expr::Sel(Box::new(expr_cps), field.clone())],
                    ))
                }),
                fresh_sel,
            )
        }
        Expr::If(e1, e2, e3) => {
            let ctx_br = ctx.clone();
            let fresh_br = fresh.clone();
            let cont_expr = cont.clone();
            cps_prime(
                ctx,
                *e1,
                Rc::new(move |cond_cps| {
                    let then_expr = cps_double_prime(
                        ctx_br.clone(),
                        *e2.clone(),
                        cont_expr.clone(),
                        fresh_br.clone(),
                    )?;
                    let else_expr = cps_double_prime(
                        ctx_br.clone(),
                        *e3.clone(),
                        cont_expr.clone(),
                        fresh_br.clone(),
                    )?;
                    Ok(Expr::If(
                        Box::new(cond_cps),
                        Box::new(then_expr),
                        Box::new(else_expr),
                    ))
                }),
                fresh,
            )
        }
        Expr::Match(cond, cases) => {
            let pats: Vec<Pattern> = cases.iter().map(|(p, _)| p.clone()).collect();
            let arms: Vec<Expr> = cases.iter().map(|(_, e)| e.clone()).collect();
            let ctx_arms = ctx.clone();
            let fresh_arms = fresh.clone();
            let cont_expr = cont.clone();
            cps_prime(
                ctx,
                *cond,
                Rc::new(move |cond_cps| {
                    let ctx_inner = ctx_arms.clone();
                    let fresh_inner = fresh_arms.clone();
                    let cont_inner = cont_expr.clone();
                    let pats_inner = pats.clone();
                    let mut arms_out = Vec::with_capacity(arms.len());
                    for arm in arms.iter().cloned() {
                        arms_out.push(cps_double_prime(
                            ctx_inner.clone(),
                            arm,
                            cont_inner.clone(),
                            fresh_inner.clone(),
                        )?);
                    }
                    let cases_out = pats_inner
                        .iter()
                        .cloned()
                        .zip(arms_out.into_iter())
                        .collect::<Vec<_>>();
                    Ok(Expr::Match(Box::new(cond_cps.clone()), cases_out))
                }),
                fresh,
            )
        }
        other => Err(TransformError::new(format!(
            "not an valid expr in cps'': {}",
            pp_expr(&other, false, 0)
        ))),
    }
}

fn scan_ctors_arity(ctx: &mut ArityCtx, binding: &TyBinding) -> TransformResult<()> {
    let mut scan_kind = |kind: &TyKind| -> TransformResult<()> {
        match kind {
            TyKind::Enum { ctors, .. } => {
                for ctor in ctors {
                    let arity = ctor.args.len();
                    if ctx.contains_key(&ctor.name) {
                        return Err(TransformError::cps_scan_ctors_arity_assertion_failed());
                    }
                    ctx.insert(ctor.name.clone(), arity);
                }
                Ok(())
            }
        }
    };

    match binding {
        TyBinding::One { kind, .. } => scan_kind(kind),
        TyBinding::Rec(kinds) => {
            for (_, kind) in kinds {
                scan_kind(kind)?;
            }
            Ok(())
        }
    }
}

fn cps_prog_with_fresh(prog: &Prog, fresh: Rc<RefCell<Fresh>>) -> TransformResult<Prog> {
    let mut ctx: ArityCtx = HashMap::new();
    let mut stmts = Vec::new();
    for stmt in prog.stmts() {
        match stmt {
            Stmt::Type(binding) => {
                scan_ctors_arity(&mut ctx, binding)?;
                stmts.push(Stmt::Type(binding.clone()));
            }
            Stmt::Term(binding) => match binding {
                Binding::One(pat, expr) => {
                    let ctx_rc = Rc::new(ctx.clone());
                    let expr_cps =
                        cps_prime(ctx_rc, (**expr).clone(), Rc::new(|x| Ok(x)), fresh.clone())?;
                    stmts.push(Stmt::Term(Binding::One(pat.clone(), Box::new(expr_cps))));
                }
                Binding::Rec(bindings) => {
                    let ctx_rc = Rc::new(ctx.clone());
                    let mut out = Vec::with_capacity(bindings.len());
                    for (pat, expr) in bindings {
                        let expr_cps = cps_prime(
                            ctx_rc.clone(),
                            (**expr).clone(),
                            Rc::new(|x| Ok(x)),
                            fresh.clone(),
                        )?;
                        out.push((pat.clone(), Box::new(expr_cps)));
                    }
                    stmts.push(Stmt::Term(Binding::Rec(out)));
                }
                Binding::Seq(expr) => {
                    let ctx_rc = Rc::new(ctx.clone());
                    let expr_cps =
                        cps_prime(ctx_rc, (**expr).clone(), Rc::new(|x| Ok(x)), fresh.clone())?;
                    stmts.push(Stmt::Term(Binding::Seq(Box::new(expr_cps))));
                }
            },
        }
    }
    Ok(Prog::new(stmts))
}

pub fn cps_prog(prog: &Prog) -> TransformResult<Prog> {
    let fresh = Rc::new(RefCell::new(Fresh::default()));
    cps_prog_with_fresh(prog, fresh)
}

fn pattern_vars(pattern: &Pattern) -> HashSet<String> {
    match pattern {
        Pattern::Any | Pattern::Int(_) | Pattern::Bool(_) | Pattern::Unit => HashSet::new(),
        Pattern::Var(name) => {
            let mut set = HashSet::new();
            set.insert(name.clone());
            set
        }
        Pattern::Tup(items) => {
            let mut set = HashSet::new();
            for item in items {
                set.extend(pattern_vars(item));
            }
            set
        }
        Pattern::CtorApp { args, .. } => {
            let mut set = HashSet::new();
            if let Some(args) = args {
                for arg in args {
                    set.extend(pattern_vars(arg));
                }
            }
            set
        }
    }
}

fn free_expr(expr: &Expr) -> HashSet<String> {
    match expr {
        Expr::Unit | Expr::Int(_) | Expr::Bool(_) | Expr::Str(_) | Expr::Builtin(_) | Expr::Ctor(_) => {
            HashSet::new()
        }
        Expr::Var(name) | Expr::GVar(name) => {
            let mut set = HashSet::new();
            set.insert(name.clone());
            set
        }
        Expr::Lam(patterns, body) => {
            let mut set = free_expr(body);
            let mut bound = HashSet::new();
            for pat in patterns {
                bound.extend(pattern_vars(pat));
            }
            for b in bound {
                set.remove(&b);
            }
            set
        }
        Expr::App(fun, args) => {
            let mut set = free_expr(fun);
            for arg in args {
                set.extend(free_expr(arg));
            }
            set
        }
        Expr::Op(_, lhs, rhs) => {
            let mut set = free_expr(lhs);
            set.extend(free_expr(rhs));
            set
        }
        Expr::Tup(items) | Expr::Arr(items) => {
            let mut set = HashSet::new();
            for item in items {
                set.extend(free_expr(item));
            }
            set
        }
        Expr::Let(binding, body) => match &**binding {
            Binding::One(pat, expr) => {
                let mut set = free_expr(expr);
                let mut body_set = free_expr(body);
                let bound = pattern_vars(pat);
                for b in bound {
                    body_set.remove(&b);
                }
                set.extend(body_set);
                set
            }
            Binding::Rec(bindings) => {
                let mut set = HashSet::new();
                let mut bound = HashSet::new();
                for (pat, expr) in bindings {
                    bound.extend(pattern_vars(pat));
                    set.extend(free_expr(expr));
                }
                let mut body_set = free_expr(body);
                for b in bound {
                    body_set.remove(&b);
                }
                set.extend(body_set);
                set
            }
            Binding::Seq(expr) => {
                let mut set = free_expr(expr);
                set.extend(free_expr(body));
                set
            }
        },
        Expr::Sel(expr, _) => free_expr(expr),
        Expr::If(e1, e2, e3) => {
            let mut set = free_expr(e1);
            set.extend(free_expr(e2));
            set.extend(free_expr(e3));
            set
        }
        Expr::Match(cond, cases) => {
            let mut set = free_expr(cond);
            for (pat, expr) in cases {
                let mut case_set = free_expr(expr);
                let bound = pattern_vars(pat);
                for b in bound {
                    case_set.remove(&b);
                }
                set.extend(case_set);
            }
            set
        }
    }
}

fn gen_symbol(binding: (&Pattern, &Expr), fresh: &Rc<RefCell<Fresh>>) -> TransformResult<(String, String)> {
    match binding {
        (Pattern::Var(name), Expr::Lam(_, _)) => {
            let ctor = fresh.borrow_mut().next_fresh("`C_'lam");
            Ok((name.clone(), ctor))
        }
        _ => Err(TransformError::new("Unsupported binding in gen_symbol")),
    }
}

fn de_lam(
    ctx: &DefuncCtx,
    ctor: String,
    expr: &Expr,
    fresh: &Rc<RefCell<Fresh>>,
) -> TransformResult<(Expr, Vec<Case>)> {
    match expr {
        Expr::Lam(params, body) => {
            let mut fvs = free_expr(expr);
            for key in ctx.keys() {
                fvs.remove(key);
            }
            let mut fv_list: Vec<String> = fvs.into_iter().collect();
            fv_list.sort();
            let sorted_fvl = fv_list
                .iter()
                .map(|x| Expr::Var(x.clone()))
                .collect::<Vec<_>>();
            let sorted_p_fvl = fv_list
                .iter()
                .map(|x| Pattern::Var(x.clone()))
                .collect::<Vec<_>>();
            let (body_expr, mut cases) = defunc_expr(ctx, body, fresh)?;
            let (abs, case_pat) = if fv_list.is_empty() {
                (
                    Expr::Ctor(ctor.clone()),
                    Pattern::CtorApp {
                        name: ctor.clone(),
                        args: None,
                    },
                )
            } else {
                (
                    Expr::App(Box::new(Expr::Ctor(ctor.clone())), sorted_fvl),
                    Pattern::CtorApp {
                        name: ctor.clone(),
                        args: Some(sorted_p_fvl),
                    },
                )
            };
            let mut tuple_items = Vec::with_capacity(params.len() + 1);
            tuple_items.push(case_pat);
            tuple_items.extend(params.clone());
            let case = (Pattern::Tup(tuple_items), body_expr);
            cases.insert(0, case);
            Ok((abs, cases))
        }
        _ => defunc_expr(ctx, expr, fresh),
    }
}

fn de_app(
    ctx: &DefuncCtx,
    expr: &Expr,
    fresh: &Rc<RefCell<Fresh>>,
) -> TransformResult<(Expr, Vec<Case>)> {
    match expr {
        Expr::App(fun, args) => match fun.as_ref() {
            Expr::Ctor(name) => {
                let mut new_args = Vec::with_capacity(args.len());
                let mut cases = Vec::new();
                for arg in args {
                    let (arg_expr, arg_cases) = defunc_expr(ctx, arg, fresh)?;
                    new_args.push(arg_expr);
                    cases.extend(arg_cases);
                }
                Ok((
                    Expr::App(Box::new(Expr::Ctor(name.clone())), new_args),
                    cases,
                ))
            }
            _ => {
                let (fun_expr, mut cases1) = defunc_expr(ctx, fun, fresh)?;
                let mut new_args = Vec::with_capacity(args.len() + 1);
                new_args.push(fun_expr);
                for arg in args {
                    let (arg_expr, arg_cases) = defunc_expr(ctx, arg, fresh)?;
                    new_args.push(arg_expr);
                    cases1.extend(arg_cases);
                }
                Ok((
                    Expr::App(Box::new(Expr::Var("_'defunc_apply".to_string())), new_args),
                    cases1,
                ))
            }
        },
        _ => defunc_expr(ctx, expr, fresh),
    }
}

fn de_single_binding(
    ctx: &DefuncCtx,
    pat: &Pattern,
    e1: &Expr,
    e2: &Expr,
    fresh: &Rc<RefCell<Fresh>>,
) -> TransformResult<(Pattern, Expr, Expr, Vec<Case>)> {
    match e1 {
        Expr::Lam(_, _) => {
            let (name, ctor) = gen_symbol((pat, e1), fresh)?;
            let mut new_ctx = ctx.clone();
            new_ctx.insert(name, ctor.clone());
            let (e1_expr, mut cases1) = de_lam(ctx, ctor, e1, fresh)?;
            let (e2_expr, cases2) = defunc_expr(&new_ctx, e2, fresh)?;
            cases1.extend(cases2);
            Ok((pat.clone(), e1_expr, e2_expr, cases1))
        }
        _ => {
            let (e1_expr, mut cases1) = defunc_expr(ctx, e1, fresh)?;
            let (e2_expr, cases2) = defunc_expr(ctx, e2, fresh)?;
            cases1.extend(cases2);
            Ok((pat.clone(), e1_expr, e2_expr, cases1))
        }
    }
}

fn de_rec_bindings(
    ctx: &DefuncCtx,
    bindings: &[(Pattern, Box<Expr>)],
    fresh: &Rc<RefCell<Fresh>>,
) -> TransformResult<(Vec<(Pattern, Box<Expr>)>, Vec<Vec<Case>>)> {
    for (_, expr) in bindings {
        if !matches!(expr.as_ref(), Expr::Lam(_, _)) {
            return Err(TransformError::defunc_assertion_failed());
        }
    }
    let mut symbols = Vec::with_capacity(bindings.len());
    for (pat, expr) in bindings {
        symbols.push(gen_symbol((pat, expr), fresh)?);
    }
    let mut new_ctx = ctx.clone();
    for (name, ctor) in &symbols {
        new_ctx.insert(name.clone(), ctor.clone());
    }
    let mut new_bindings = Vec::with_capacity(bindings.len());
    let mut lists = Vec::new();
    for ((pat, expr), (_, ctor)) in bindings.iter().zip(symbols.iter()) {
        let (expr_out, cases) = de_lam(&new_ctx, ctor.clone(), expr, fresh)?;
        new_bindings.push((pat.clone(), Box::new(expr_out)));
        lists.push(cases);
    }
    lists.reverse();
    Ok((new_bindings, lists))
}

fn defunc_expr(
    ctx: &DefuncCtx,
    expr: &Expr,
    fresh: &Rc<RefCell<Fresh>>,
) -> TransformResult<(Expr, Vec<Case>)> {
    match expr {
        Expr::Unit => Ok((Expr::Unit, Vec::new())),
        Expr::Int(i) => Ok((Expr::Int(*i), Vec::new())),
        Expr::Bool(b) => Ok((Expr::Bool(*b), Vec::new())),
        Expr::Str(s) => Ok((Expr::Str(s.clone()), Vec::new())),
        Expr::Builtin(b) => Ok((Expr::Builtin(b.clone()), Vec::new())),
        Expr::Var(name) => match ctx.get(name) {
            Some(ctor) => Ok((Expr::Ctor(ctor.clone()), Vec::new())),
            None => Ok((Expr::Var(name.clone()), Vec::new())),
        },
        Expr::GVar(name) => Ok((Expr::GVar(name.clone()), Vec::new())),
        Expr::Ctor(name) => Ok((Expr::Ctor(name.clone()), Vec::new())),
        Expr::Op(op, e1, e2) => {
            let (e1_expr, mut cases1) = defunc_expr(ctx, e1, fresh)?;
            let (e2_expr, cases2) = defunc_expr(ctx, e2, fresh)?;
            cases1.extend(cases2);
            Ok((
                Expr::Op(op.clone(), Box::new(e1_expr), Box::new(e2_expr)),
                cases1,
            ))
        }
        Expr::Tup(items) => {
            let mut out_items = Vec::with_capacity(items.len());
            let mut cases = Vec::new();
            for item in items {
                let (expr_out, expr_cases) = defunc_expr(ctx, item, fresh)?;
                out_items.push(expr_out);
                cases.extend(expr_cases);
            }
            Ok((Expr::Tup(out_items), cases))
        }
        Expr::Arr(items) => {
            let mut out_items = Vec::with_capacity(items.len());
            let mut cases = Vec::new();
            for item in items {
                let (expr_out, expr_cases) = defunc_expr(ctx, item, fresh)?;
                out_items.push(expr_out);
                cases.extend(expr_cases);
            }
            Ok((Expr::Arr(out_items), cases))
        }
        Expr::Let(binding, body) => match &**binding {
            Binding::Seq(expr) => {
                let (e1, mut cases1) = defunc_expr(ctx, expr, fresh)?;
                let (e2, cases2) = defunc_expr(ctx, body, fresh)?;
                cases1.extend(cases2);
                Ok((
                    Expr::Let(
                        Box::new(Binding::Seq(Box::new(e1))),
                        Box::new(e2),
                    ),
                    cases1,
                ))
            }
            Binding::One(pat, expr) => {
                let (pat_out, e1, e2, cases) = de_single_binding(ctx, pat, expr, body, fresh)?;
                Ok((
                    Expr::Let(
                        Box::new(Binding::One(pat_out, Box::new(e1))),
                        Box::new(e2),
                    ),
                    cases,
                ))
            }
            Binding::Rec(bindings) => {
                let (new_bindings, lists) = de_rec_bindings(ctx, bindings, fresh)?;
                let (body_expr, body_cases) = defunc_expr(ctx, body, fresh)?;
                let mut cases = Vec::new();
                for list in lists {
                    cases.extend(list);
                }
                cases.extend(body_cases);
                Ok((
                    Expr::Let(Box::new(Binding::Rec(new_bindings)), Box::new(body_expr)),
                    cases,
                ))
            }
        },
        Expr::Sel(expr, field) => {
            let (expr_out, cases) = defunc_expr(ctx, expr, fresh)?;
            Ok((Expr::Sel(Box::new(expr_out), field.clone()), cases))
        }
        Expr::If(e1, e2, e3) => {
            let (e1_expr, mut cases1) = defunc_expr(ctx, e1, fresh)?;
            let (e2_expr, cases2) = defunc_expr(ctx, e2, fresh)?;
            let (e3_expr, cases3) = defunc_expr(ctx, e3, fresh)?;
            cases1.extend(cases2);
            cases1.extend(cases3);
            Ok((
                Expr::If(Box::new(e1_expr), Box::new(e2_expr), Box::new(e3_expr)),
                cases1,
            ))
        }
        Expr::Match(cond, cases) => {
            let (cond_expr, mut cond_cases) = defunc_expr(ctx, cond, fresh)?;
            let mut out_cases = Vec::with_capacity(cases.len());
            let mut lists = Vec::new();
            for (pat, expr) in cases {
                let (expr_out, expr_cases) = defunc_expr(ctx, expr, fresh)?;
                out_cases.push((pat.clone(), expr_out));
                lists.push(expr_cases);
            }
            lists.reverse();
            for list in lists {
                cond_cases.extend(list);
            }
            Ok((Expr::Match(Box::new(cond_expr), out_cases), cond_cases))
        }
        Expr::App(_, _) => de_app(ctx, expr, fresh),
        Expr::Lam(_, _) => {
            let ctor = fresh.borrow_mut().next_fresh("`C_'lam");
            de_lam(ctx, ctor, expr, fresh)
        }
    }
}

fn defunc_prog_with_fresh(prog: &Prog, fresh: Rc<RefCell<Fresh>>) -> TransformResult<Prog> {
    let ctx: DefuncCtx = HashMap::new();
    let mut cases: Vec<Case> = Vec::new();
    let mut stmts: Vec<Stmt> = Vec::new();
    for stmt in prog.stmts() {
        match stmt {
            Stmt::Type(binding) => stmts.push(Stmt::Type(binding.clone())),
            Stmt::Term(binding) => match binding {
                Binding::One(pat, expr) => {
                    let (expr_out, its) = defunc_expr(&ctx, expr, &fresh)?;
                    let mut new_cases = its;
                    new_cases.extend(cases);
                    cases = new_cases;
                    stmts.push(Stmt::Term(Binding::One(pat.clone(), Box::new(expr_out))));
                }
                Binding::Rec(bindings) => {
                    let let_expr = Expr::Let(
                        Box::new(Binding::Rec(bindings.clone())),
                        Box::new(Expr::Tup(Vec::new())),
                    );
                    let (expr_out, its) = defunc_expr(&ctx, &let_expr, &fresh)?;
                    let mut new_cases = its;
                    new_cases.extend(cases);
                    cases = new_cases;
                    stmts.push(Stmt::Term(Binding::One(
                        Pattern::Unit,
                        Box::new(expr_out),
                    )));
                }
                Binding::Seq(expr) => {
                    let (expr_out, its) = defunc_expr(&ctx, expr, &fresh)?;
                    let mut new_cases = its;
                    new_cases.extend(cases);
                    cases = new_cases;
                    stmts.push(Stmt::Term(Binding::Seq(Box::new(expr_out))));
                }
            },
        }
    }

    let defunc_apply = {
        let apply_pat = Pattern::Var("_'defunc_apply".to_string());
        let apply_var = Expr::Var("_'defunc_apply".to_string());
        let f_var = Expr::Var("_'f".to_string());
        let a_var = Expr::Var("_'a".to_string());
        let match_expr = Expr::Match(
            Box::new(Expr::Tup(vec![f_var.clone(), a_var.clone()])),
            cases,
        );
        let lam = Expr::Lam(
            vec![Pattern::Var("_'f".to_string()), Pattern::Var("_'a".to_string())],
            Box::new(match_expr),
        );
        let rec_binding = Binding::Rec(vec![(apply_pat.clone(), Box::new(lam))]);
        let let_expr = Expr::Let(Box::new(rec_binding), Box::new(apply_var.clone()));
        Stmt::Term(Binding::One(apply_pat, Box::new(let_expr)))
    };

    let mut out = Vec::with_capacity(stmts.len() + 1);
    out.push(defunc_apply);
    out.extend(stmts);
    Ok(Prog::new(out))
}

pub fn defunc_prog(prog: &Prog) -> TransformResult<Prog> {
    let fresh = Rc::new(RefCell::new(Fresh::default()));
    defunc_prog_with_fresh(prog, fresh)
}

pub fn cps_defunc_prog(prog: &Prog) -> TransformResult<Prog> {
    let fresh = Rc::new(RefCell::new(Fresh::default()));
    let cpsed = cps_prog_with_fresh(prog, fresh.clone())?;
    defunc_prog_with_fresh(&cpsed, fresh)
}

#[derive(Clone)]
struct PatternMatrix {
    arity: usize,
    occs: Vec<Vec<i32>>,
    bnds: Vec<BTreeMap<Vec<i32>, String>>,
    pats: Vec<Vec<Pattern>>,
    acts: Vec<i32>,
}

fn pp_occ(occ: &[i32]) -> String {
    if occ.is_empty() {
        "\\".to_string()
    } else {
        let mut out = pp_occ(&occ[1..]);
        out.push('.');
        out.push_str(&occ[0].to_string());
        out
    }
}

fn pp_pattern_matrix(mat: &PatternMatrix) -> String {
    let mut lines = Vec::new();
    lines.push(format!("arity = {}", mat.arity));
    let occ_str = mat
        .occs
        .first()
        .map(|occ| pp_occ(occ))
        .unwrap_or_else(|| "\\".to_string());
    lines.push(format!("  occurrence = {}", occ_str));
    for ((row, bnd), act) in mat.pats.iter().zip(mat.bnds.iter()).zip(mat.acts.iter()) {
        let row_str = row
            .iter()
            .map(|pat| pp_pattern(pat, false))
            .collect::<Vec<_>>()
            .join(",");
        let mut line = format!("  ({}) -> {}", row_str, act);
        if !bnd.is_empty() {
            let entries = bnd
                .iter()
                .map(|(occ, name)| format!("{}->{}", pp_occ(occ), name))
                .collect::<Vec<_>>();
            line.push_str(" with ");
            line.push('(');
            line.push_str(&entries.join(") ("));
            line.push(')');
        }
        lines.push(line);
    }
    lines.join("\n")
}

fn make_mat(pats: Vec<Pattern>, acts: Vec<i32>) -> PatternMatrix {
    let arity = 1;
    let occs = vec![Vec::new()];
    let bnds = pats.iter().map(|_| BTreeMap::new()).collect::<Vec<_>>();
    let pats = pats.into_iter().map(|pat| vec![pat]).collect();
    PatternMatrix {
        arity,
        occs,
        bnds,
        pats,
        acts,
    }
}

fn collect_pat_mat(expr: &Expr) -> Vec<PatternMatrix> {
    fn aux(mut acc: Vec<PatternMatrix>, expr: &Expr) -> Vec<PatternMatrix> {
        match expr {
            Expr::Unit
            | Expr::Bool(_)
            | Expr::Int(_)
            | Expr::Str(_)
            | Expr::Builtin(_)
            | Expr::Var(_)
            | Expr::GVar(_)
            | Expr::Ctor(_) => {
                acc.reverse();
                acc
            }
            Expr::App(fun, args) => {
                let acc = aux(acc, fun);
                args.iter().fold(acc, |acc, arg| aux(acc, arg))
            }
            Expr::Op(_, e1, e2) => {
                let acc = aux(acc, e1);
                aux(acc, e2)
            }
            Expr::Tup(items) | Expr::Arr(items) => {
                items.iter().fold(acc, |acc, item| aux(acc, item))
            }
            Expr::Lam(_, body) => aux(acc, body),
            Expr::Let(binding, body) => match binding.as_ref() {
                Binding::Seq(expr) => {
                    let acc = aux(acc, expr);
                    aux(acc, body)
                }
                Binding::One(pat, expr) => {
                    let acc = aux(acc, expr);
                    let mut acc = acc;
                    acc.insert(0, make_mat(vec![pat.clone()], vec![0]));
                    aux(acc, body)
                }
                Binding::Rec(bindings) => {
                    let acc = bindings.iter().fold(acc, |acc, (pat, expr)| {
                        let mut acc = acc;
                        acc.insert(0, make_mat(vec![pat.clone()], vec![0]));
                        aux(acc, expr)
                    });
                    aux(acc, body)
                }
            },
            Expr::Sel(expr, _) => aux(acc, expr),
            Expr::If(cond, then_branch, else_branch) => {
                let acc = aux(acc, cond);
                let acc = aux(acc, then_branch);
                aux(acc, else_branch)
            }
            Expr::Match(expr, cases) => {
                let acc = aux(acc, expr);
                let pats = cases
                    .iter()
                    .map(|(pat, _)| pat.clone())
                    .collect::<Vec<_>>();
                let acts = (0..cases.len()).map(|i| i as i32).collect::<Vec<_>>();
                let mut acc = acc;
                acc.insert(0, make_mat(pats, acts));
                cases.iter().fold(acc, |acc, (_, arm)| aux(acc, arm))
            }
        }
    }

    aux(Vec::new(), expr)
}

pub fn pat_output(prog: &Prog) -> String {
    let mut matrixes: Vec<PatternMatrix> = Vec::new();
    for stmt in prog.stmts() {
        match stmt {
            Stmt::Type(_) => {}
            Stmt::Term(binding) => match binding {
                Binding::Seq(expr) => {
                    let mut mats = collect_pat_mat(expr);
                    mats.extend(matrixes);
                    matrixes = mats;
                }
                Binding::One(pat, expr) => {
                    let mut mats = collect_pat_mat(expr);
                    mats.push(make_mat(vec![pat.clone()], vec![0]));
                    mats.extend(matrixes);
                    matrixes = mats;
                }
                Binding::Rec(bindings) => {
                    let mut acc = matrixes;
                    for (pat, expr) in bindings {
                        let mut mats = collect_pat_mat(expr);
                        mats.push(make_mat(vec![pat.clone()], vec![0]));
                        mats.extend(acc);
                        acc = mats;
                    }
                    matrixes = acc;
                }
            },
        }
    }

    let docs = matrixes
        .iter()
        .map(|mat| format!("pattern matrix:\n{}", pp_pattern_matrix(mat)))
        .collect::<Vec<_>>();
    docs.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;
    use ant_frontend::TyCtor;

    #[test]
    fn cps_prog_missing_ctor_returns_not_found() {
        let prog = Prog::new(vec![Stmt::Term(Binding::One(
            Pattern::Unit,
            Box::new(Expr::Ctor("Missing".to_string())),
        ))]);

        let err = cps_prog(&prog).unwrap_err();
        assert_eq!(err.to_string(), "Not_found");
    }

    #[test]
    fn cps_prog_duplicate_ctor_returns_assertion_failed() {
        let binding = TyBinding::One {
            name: "t".to_string(),
            kind: TyKind::Enum {
                params: Vec::new(),
                ctors: vec![
                    TyCtor {
                        name: "A".to_string(),
                        args: Vec::new(),
                    },
                    TyCtor {
                        name: "A".to_string(),
                        args: Vec::new(),
                    },
                ],
            },
        };

        let prog = Prog::new(vec![Stmt::Type(binding)]);
        let err = cps_prog(&prog).unwrap_err();
        assert_eq!(
            err.to_string(),
            "File \"lib/Transform.ml\", line 194, characters 14-20: Assertion failed"
        );
    }

    #[test]
    fn defunc_prog_unsupported_rec_binding_returns_failure_message() {
        let lam = Expr::Lam(
            vec![Pattern::Var("x".to_string())],
            Box::new(Expr::Var("x".to_string())),
        );
        let prog = Prog::new(vec![Stmt::Term(Binding::Rec(vec![(
            Pattern::Any,
            Box::new(lam),
        )]))]);

        let err = defunc_prog(&prog).unwrap_err();
        assert_eq!(err.to_string(), "Unsupported binding in gen_symbol");
    }
}
