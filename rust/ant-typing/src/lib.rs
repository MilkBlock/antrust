use ant_frontend::{
    pp_expr, pp_pattern, pp_stmt, Binding, Expr, Field, Pattern, Prog, Stmt, Ty, TyBinding, TyKind,
};
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

#[derive(Debug)]
pub struct TypingError {
    message: String,
    expr: Option<String>,
}

impl TypingError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            expr: None,
        }
    }

    fn with_expr(mut self, expr: String) -> Self {
        if self.expr.is_none() {
            self.expr = Some(expr);
        }
        self
    }

    pub fn stdout_message(&self) -> Option<String> {
        self.expr.as_ref().map(|expr| {
            format!(
                "!!!!!! Type error {} in expression:\n{}\n\n",
                self.message, expr
            )
        })
    }
}

impl fmt::Display for TypingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for TypingError {}

type TyResult<T> = Result<T, TypingError>;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Prim {
    Unit,
    Int,
    Float,
    Bool,
    Str,
}

type Level = i32;

const GENERIC_LEVEL: Level = i32::MAX;
const MARKER_LEVEL: Level = i32::MIN;
const GROUND_LEVEL: Level = 0;

thread_local! {
    static CURRENT_LEVEL: Cell<Level> = Cell::new(1);
    static FRESH_SYM: Cell<i32> = Cell::new(0);
    static TO_BE_LEVEL_ADJUSTED: RefCell<Vec<TypeRef>> = RefCell::new(Vec::new());
}

fn enter_level() {
    CURRENT_LEVEL.with(|c| c.set(c.get() + 1));
}

fn leave_level() {
    CURRENT_LEVEL.with(|c| c.set(c.get() - 1));
}

fn current_level() -> Level {
    CURRENT_LEVEL.with(|c| c.get())
}

fn reset_levels() {
    CURRENT_LEVEL.with(|c| c.set(1));
}

fn reset_fresh() {
    FRESH_SYM.with(|c| c.set(0));
}

fn reset_level_adjustment() {
    TO_BE_LEVEL_ADJUSTED.with(|c| c.borrow_mut().clear());
}

fn level_to_string(level: Level) -> String {
    if level == GENERIC_LEVEL {
        "@".to_string()
    } else if level == MARKER_LEVEL {
        "!".to_string()
    } else {
        level.to_string()
    }
}

fn fresh_sym() -> String {
    let idx = FRESH_SYM.with(|c| {
        let idx = c.get();
        c.set(idx + 1);
        idx
    });
    if idx < 26 {
        let ch = (b'a' + (idx as u8)) as char;
        ch.to_string()
    } else {
        format!("t{idx}")
    }
}

#[derive(Clone, Copy)]
struct Levels {
    level_new: Level,
    level_old: Level,
}

#[derive(Clone)]
enum TypeVarState {
    Link(TypeRef),
    Unbound { name: String, level: Level },
}

#[derive(Clone)]
struct TypeVar {
    state: TypeVarState,
}

type TypeVarRef = Rc<RefCell<TypeVar>>;

#[derive(Clone)]
enum TypeNode {
    Prim(Prim),
    Var(TypeVarRef),
    Tup { items: Vec<TypeRef>, levels: Levels },
    Arr { items: Vec<TypeRef>, levels: Levels },
    Arrow { args: Vec<TypeRef>, ret: TypeRef, levels: Levels },
    App { name: String, args: Vec<TypeRef>, levels: Levels },
}

type TypeRef = Rc<RefCell<TypeNode>>;

#[derive(Clone)]
enum TypeView {
    Prim(Prim),
    Var(TypeVarRef),
    Tup { items: Vec<TypeRef>, levels: Levels },
    Arr { items: Vec<TypeRef>, levels: Levels },
    Arrow { args: Vec<TypeRef>, ret: TypeRef, levels: Levels },
    App { name: String, args: Vec<TypeRef>, levels: Levels },
}

fn view(ty: &TypeRef) -> TypeView {
    match &*ty.borrow() {
        TypeNode::Prim(p) => TypeView::Prim(p.clone()),
        TypeNode::Var(tv) => TypeView::Var(tv.clone()),
        TypeNode::Tup { items, levels } => TypeView::Tup {
            items: items.clone(),
            levels: *levels,
        },
        TypeNode::Arr { items, levels } => TypeView::Arr {
            items: items.clone(),
            levels: *levels,
        },
        TypeNode::Arrow { args, ret, levels } => TypeView::Arrow {
            args: args.clone(),
            ret: ret.clone(),
            levels: *levels,
        },
        TypeNode::App { name, args, levels } => TypeView::App {
            name: name.clone(),
            args: args.clone(),
            levels: *levels,
        },
    }
}

fn set_level_new(ty: &TypeRef, level: Level) {
    let mut node = ty.borrow_mut();
    match &mut *node {
        TypeNode::Arrow { levels, .. }
        | TypeNode::Tup { levels, .. }
        | TypeNode::Arr { levels, .. }
        | TypeNode::App { levels, .. } => {
            levels.level_new = level;
        }
        _ => {}
    }
}

fn set_levels(ty: &TypeRef, new_level: Level, old_level: Level) {
    let mut node = ty.borrow_mut();
    match &mut *node {
        TypeNode::Arrow { levels, .. }
        | TypeNode::Tup { levels, .. }
        | TypeNode::Arr { levels, .. }
        | TypeNode::App { levels, .. } => {
            levels.level_new = new_level;
            levels.level_old = old_level;
        }
        _ => {}
    }
}

fn new_levels() -> Levels {
    let level = current_level();
    Levels {
        level_new: level,
        level_old: level,
    }
}

fn ty_prim(p: Prim) -> TypeRef {
    Rc::new(RefCell::new(TypeNode::Prim(p)))
}

fn new_tvar() -> TypeRef {
    let name = fresh_sym();
    let level = current_level();
    let tv = Rc::new(RefCell::new(TypeVar {
        state: TypeVarState::Unbound { name, level },
    }));
    Rc::new(RefCell::new(TypeNode::Var(tv)))
}

fn new_arrow(args: Vec<TypeRef>, ret: TypeRef) -> TypeRef {
    Rc::new(RefCell::new(TypeNode::Arrow {
        args,
        ret,
        levels: new_levels(),
    }))
}

fn new_tup(items: Vec<TypeRef>) -> TypeRef {
    Rc::new(RefCell::new(TypeNode::Tup {
        items,
        levels: new_levels(),
    }))
}

fn new_arr(items: Vec<TypeRef>) -> TypeRef {
    Rc::new(RefCell::new(TypeNode::Arr {
        items,
        levels: new_levels(),
    }))
}

fn new_app(name: String, args: Vec<TypeRef>) -> TypeRef {
    Rc::new(RefCell::new(TypeNode::App {
        name,
        args,
        levels: new_levels(),
    }))
}

fn repr(ty: &TypeRef) -> TypeRef {
    let link = {
        let node = ty.borrow();
        match &*node {
            TypeNode::Var(tv) => match &tv.borrow().state {
                TypeVarState::Link(target) => Some(target.clone()),
                _ => None,
            },
            _ => None,
        }
    };
    if let Some(target) = link {
        let repr_target = repr(&target);
        if let TypeNode::Var(tv) = &mut *ty.borrow_mut() {
            tv.borrow_mut().state = TypeVarState::Link(repr_target.clone());
        }
        repr_target
    } else {
        ty.clone()
    }
}

fn get_level(ty: &TypeRef) -> Level {
    let ty = repr(ty);
    let result = match view(&ty) {
        TypeView::Var(tv) => match &tv.borrow().state {
            TypeVarState::Unbound { level, .. } => *level,
            TypeVarState::Link(target) => get_level(target),
        },
        TypeView::Arrow { levels, .. }
        | TypeView::App { levels, .. }
        | TypeView::Tup { levels, .. }
        | TypeView::Arr { levels, .. } => levels.level_new,
        TypeView::Prim(_) => GROUND_LEVEL,
    };
    result
}

fn push_adjustment(ty: &TypeRef) {
    TO_BE_LEVEL_ADJUSTED.with(|c| c.borrow_mut().push(ty.clone()));
}

fn update_level(level: Level, ty: &TypeRef) -> TyResult<()> {
    let ty = repr(ty);
    match &mut *ty.borrow_mut() {
        TypeNode::Var(tv) => match &mut tv.borrow_mut().state {
            TypeVarState::Unbound { level: l, .. } => {
                if level < *l {
                    *l = level;
                }
            }
            TypeVarState::Link(_) => {
                return Err(TypingError::new("update_level: unexpected link"));
            }
        },
        TypeNode::Arrow { levels, .. }
        | TypeNode::App { levels, .. }
        | TypeNode::Tup { levels, .. }
        | TypeNode::Arr { levels, .. } => {
            if levels.level_new == GENERIC_LEVEL {
                return Err(TypingError::new("failed to update level: generic level"));
            }
            if levels.level_new == MARKER_LEVEL {
                return Err(TypingError::new("update_level: cycle detected"));
            }
            if level < levels.level_new {
                if levels.level_new == levels.level_old {
                    push_adjustment(&ty);
                }
                levels.level_new = level;
            }
        }
        TypeNode::Prim(_) => {}
    }
    Ok(())
}

fn unify(ty1: &TypeRef, ty2: &TypeRef) -> TyResult<()> {
    if Rc::ptr_eq(ty1, ty2) {
        return Ok(());
    }
    let t1 = repr(ty1);
    let t2 = repr(ty2);
    if Rc::ptr_eq(&t1, &t2) {
        return Ok(());
    }
    let v1 = view(&t1);
    let v2 = view(&t2);
    match (v1, v2) {
        (TypeView::Var(tv1), TypeView::Var(tv2)) => {
            let (l1, l2) = match (&tv1.borrow().state, &tv2.borrow().state) {
                (
                    TypeVarState::Unbound { level: l1, .. },
                    TypeVarState::Unbound { level: l2, .. },
                ) => (*l1, *l2),
                _ => return Err(TypingError::new("unify: unexpected link")),
            };
            if Rc::ptr_eq(&tv1, &tv2) {
                return Ok(());
            }
            if l2 < l1 {
                tv1.borrow_mut().state = TypeVarState::Link(t2.clone());
            } else {
                tv2.borrow_mut().state = TypeVarState::Link(t1.clone());
            }
            Ok(())
        }
        (TypeView::Var(tv), _) => {
            let level = match &tv.borrow().state {
                TypeVarState::Unbound { level, .. } => *level,
                _ => return Err(TypingError::new("unify: unexpected link")),
            };
            update_level(level, &t2)?;
            tv.borrow_mut().state = TypeVarState::Link(t2.clone());
            Ok(())
        }
        (_, TypeView::Var(tv)) => {
            let level = match &tv.borrow().state {
                TypeVarState::Unbound { level, .. } => *level,
                _ => return Err(TypingError::new("unify: unexpected link")),
            };
            update_level(level, &t1)?;
            tv.borrow_mut().state = TypeVarState::Link(t1.clone());
            Ok(())
        }
        (
            TypeView::Arrow {
                args: args1,
                ret: ret1,
                levels: l1,
            },
            TypeView::Arrow {
                args: args2,
                ret: ret2,
                levels: l2,
            },
        ) => {
            if l1.level_new == MARKER_LEVEL || l2.level_new == MARKER_LEVEL {
                return Err(TypingError::new("unify: cycle detected"));
            }
            let min_level = l1.level_new.min(l2.level_new);
            set_level_new(&t1, MARKER_LEVEL);
            set_level_new(&t2, MARKER_LEVEL);
            if args1.len() != args2.len() {
                return Err(TypingError::new("unify: the arity of arrows must be the same"));
            }
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                unify_lev(min_level, a1, a2)?;
            }
            unify_lev(min_level, &ret1, &ret2)?;
            set_level_new(&t1, min_level);
            set_level_new(&t2, min_level);
            Ok(())
        }
        (TypeView::Prim(p1), TypeView::Prim(p2)) if p1 == p2 => Ok(()),
        (
            TypeView::Tup {
                items: items1,
                levels: l1,
            },
            TypeView::Tup {
                items: items2,
                levels: l2,
            },
        )
        | (
            TypeView::Arr {
                items: items1,
                levels: l1,
            },
            TypeView::Arr {
                items: items2,
                levels: l2,
            },
        ) => {
            if l1.level_new == MARKER_LEVEL || l2.level_new == MARKER_LEVEL {
                return Err(TypingError::new("unify: cycle detected"));
            }
            let min_level = l1.level_new.min(l2.level_new);
            set_level_new(&t1, MARKER_LEVEL);
            set_level_new(&t2, MARKER_LEVEL);
            if items1.len() != items2.len() {
                return Err(TypingError::new(
                    "unify: the arity of tuples or arrays must be the same",
                ));
            }
            for (a1, a2) in items1.iter().zip(items2.iter()) {
                unify_lev(min_level, a1, a2)?;
            }
            set_level_new(&t1, min_level);
            set_level_new(&t2, min_level);
            Ok(())
        }
        (
            TypeView::App {
                name: n1,
                args: args1,
                levels: l1,
            },
            TypeView::App {
                name: n2,
                args: args2,
                levels: l2,
            },
        ) => {
            if l1.level_new == MARKER_LEVEL || l2.level_new == MARKER_LEVEL {
                return Err(TypingError::new("unify: cycle detected"));
            }
            if n1 != n2 {
                return Err(TypingError::new(format!(
                    "unify: type mismatch: {n1} and {n2}"
                )));
            }
            if args1.len() != args2.len() {
                return Err(TypingError::new(
                    "unify: the arity of type applications must be the same",
                ));
            }
            let min_level = l1.level_new.min(l2.level_new);
            set_level_new(&t1, MARKER_LEVEL);
            set_level_new(&t2, MARKER_LEVEL);
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                unify_lev(min_level, a1, a2)?;
            }
            set_level_new(&t1, min_level);
            set_level_new(&t2, min_level);
            Ok(())
        }
        _ => Err(TypingError::new(format!(
            "unify: type mismatch: {} and {}",
            pp_ty(&t1, false),
            pp_ty(&t2, false)
        ))),
    }
}

fn unify_lev(level: Level, ty1: &TypeRef, ty2: &TypeRef) -> TyResult<()> {
    let ty1 = repr(ty1);
    update_level(level, &ty1)?;
    unify(&ty1, ty2)
}

fn cycle_free(ty: &TypeRef) -> TyResult<()> {
    let ty = repr(ty);
    match view(&ty) {
        TypeView::Var(tv) => match &tv.borrow().state {
            TypeVarState::Unbound { .. } => Ok(()),
            TypeVarState::Link(target) => cycle_free(target),
        },
        TypeView::Prim(_) => Ok(()),
        TypeView::Arrow { args, ret, levels } => {
            if levels.level_new == MARKER_LEVEL {
                return Err(TypingError::new("cycle_free: cycle detected"));
            }
            let saved = levels.level_new;
            set_level_new(&ty, MARKER_LEVEL);
            for arg in args {
                cycle_free(&arg)?;
            }
            cycle_free(&ret)?;
            set_level_new(&ty, saved);
            Ok(())
        }
        TypeView::Tup { items, levels }
        | TypeView::Arr { items, levels }
        | TypeView::App { args: items, levels, .. } => {
            if levels.level_new == MARKER_LEVEL {
                return Err(TypingError::new("cycle_free: cycle detected"));
            }
            let saved = levels.level_new;
            set_level_new(&ty, MARKER_LEVEL);
            for item in items {
                cycle_free(&item)?;
            }
            set_level_new(&ty, saved);
            Ok(())
        }
    }
}

fn force_delayed_adjustments() -> TyResult<()> {
    fn loop_adjust(acc: &mut Vec<TypeRef>, level: Level, ty: &TypeRef) -> TyResult<()> {
        let ty = repr(ty);
        match view(&ty) {
            TypeView::Var(tv) => match &mut tv.borrow_mut().state {
                TypeVarState::Unbound { level: l, .. } => {
                    if level < *l {
                        *l = level;
                    }
                    Ok(())
                }
                TypeVarState::Link(target) => loop_adjust(acc, level, target),
            },
            TypeView::Arrow { levels, .. }
            | TypeView::Tup { levels, .. }
            | TypeView::Arr { levels, .. }
            | TypeView::App { levels, .. } => {
                if levels.level_new == MARKER_LEVEL {
                    return Err(TypingError::new(
                        "force_delayed_adjustments: cycle detected",
                    ));
                }
                if level < levels.level_new {
                    set_level_new(&ty, level);
                }
                adjust_one(acc, &ty)
            }
            TypeView::Prim(_) => Ok(()),
        }
    }

    fn adjust_one(acc: &mut Vec<TypeRef>, ty: &TypeRef) -> TyResult<()> {
        let ty = repr(ty);
        match view(&ty) {
            TypeView::Arrow { args, ret, levels } => {
                if levels.level_old <= current_level() {
                    acc.push(ty.clone());
                    return Ok(());
                }
                if levels.level_old == levels.level_new {
                    return Ok(());
                }
                let level = levels.level_new;
                set_level_new(&ty, MARKER_LEVEL);
                for arg in args {
                    loop_adjust(acc, level, &arg)?;
                }
                loop_adjust(acc, level, &ret)?;
                set_levels(&ty, level, level);
                Ok(())
            }
            TypeView::Tup { items, levels }
            | TypeView::Arr { items, levels }
            | TypeView::App { args: items, levels, .. } => {
                if levels.level_old <= current_level() {
                    acc.push(ty.clone());
                    return Ok(());
                }
                if levels.level_old == levels.level_new {
                    return Ok(());
                }
                let level = levels.level_new;
                set_level_new(&ty, MARKER_LEVEL);
                for item in items {
                    loop_adjust(acc, level, &item)?;
                }
                set_levels(&ty, level, level);
                Ok(())
            }
            _ => Ok(()),
        }
    }

    let items = TO_BE_LEVEL_ADJUSTED.with(|c| c.borrow_mut().drain(..).collect::<Vec<_>>());
    let mut acc = Vec::new();
    for item in items {
        adjust_one(&mut acc, &item)?;
    }
    TO_BE_LEVEL_ADJUSTED.with(|c| *c.borrow_mut() = acc);
    Ok(())
}

fn generalize(ty: &TypeRef) -> TyResult<()> {
    force_delayed_adjustments()?;
    fn walk(ty: &TypeRef) -> TyResult<()> {
        let ty = repr(ty);
        match view(&ty) {
            TypeView::Var(tv) => match &mut tv.borrow_mut().state {
                TypeVarState::Unbound { level, .. } => {
                    if current_level() < *level {
                        *level = GENERIC_LEVEL;
                    }
                    Ok(())
                }
                TypeVarState::Link(target) => walk(target),
            },
            TypeView::Arrow { args, ret, levels } => {
                if current_level() < levels.level_new {
                    for arg in &args {
                        walk(arg)?;
                    }
                    walk(&ret)?;
                    let mut max_level = get_level(&ret);
                    for arg in &args {
                        max_level = max_level.max(get_level(arg));
                    }
                    set_levels(&ty, max_level, max_level);
                }
                Ok(())
            }
            TypeView::Tup { items, levels }
            | TypeView::Arr { items, levels }
            | TypeView::App { args: items, levels, .. } => {
                if current_level() < levels.level_new {
                    for item in &items {
                        walk(item)?;
                    }
                    let mut max_level = GROUND_LEVEL;
                    for item in &items {
                        max_level = max_level.max(get_level(item));
                    }
                    set_levels(&ty, max_level, max_level);
                }
                Ok(())
            }
            TypeView::Prim(_) => Ok(()),
        }
    }
    walk(ty)
}

fn instantiate(ty: &TypeRef) -> TypeRef {
    fn fold_aux(
        loop_fn: &dyn Fn(&mut HashMap<String, TypeRef>, &TypeRef) -> TypeRef,
        subst: &mut HashMap<String, TypeRef>,
        args: &[TypeRef],
    ) -> Vec<TypeRef> {
        let mut out = Vec::new();
        for arg in args {
            out.push(loop_fn(subst, arg));
        }
        out
    }

    fn loop_fn(subst: &mut HashMap<String, TypeRef>, ty: &TypeRef) -> TypeRef {
        let ty = repr(ty);
        match view(&ty) {
            TypeView::Var(tv) => match &tv.borrow().state {
                TypeVarState::Unbound { name, level } if *level == GENERIC_LEVEL => {
                    if let Some(existing) = subst.get(name) {
                        existing.clone()
                    } else {
                        let tv = new_tvar();
                        subst.insert(name.clone(), tv.clone());
                        tv
                    }
                }
                TypeVarState::Link(target) => loop_fn(subst, target),
                _ => ty.clone(),
            },
            TypeView::Arrow { args, ret, levels } if levels.level_new == GENERIC_LEVEL => {
                let args = fold_aux(&loop_fn, subst, &args);
                let ret = loop_fn(subst, &ret);
                new_arrow(args, ret)
            }
            TypeView::App { name, args, levels } if levels.level_new == GENERIC_LEVEL => {
                let args = fold_aux(&loop_fn, subst, &args);
                new_app(name, args)
            }
            TypeView::Tup { items, levels } if levels.level_new == GENERIC_LEVEL => {
                let items = fold_aux(&loop_fn, subst, &items);
                new_tup(items)
            }
            TypeView::Arr { items, levels } if levels.level_new == GENERIC_LEVEL => {
                let items = fold_aux(&loop_fn, subst, &items);
                new_arr(items)
            }
            _ => ty.clone(),
        }
    }

    loop_fn(&mut HashMap::new(), ty)
}

fn pp_ty(ty: &TypeRef, print_level: bool) -> String {
    fn doc_level(levels: &Levels, print_level: bool) -> String {
        if print_level {
            format!(
                ":{}~{}",
                level_to_string(levels.level_new),
                level_to_string(levels.level_old)
            )
        } else {
            String::new()
        }
    }

    fn pp(ty: &TypeRef, print_level: bool) -> String {
        let ty = repr(ty);
        match view(&ty) {
            TypeView::Prim(Prim::Unit) => "unit".to_string(),
            TypeView::Prim(Prim::Int) => "int".to_string(),
            TypeView::Prim(Prim::Float) => "float".to_string(),
            TypeView::Prim(Prim::Bool) => "bool".to_string(),
            TypeView::Prim(Prim::Str) => "str".to_string(),
            TypeView::Var(tv) => match &tv.borrow().state {
                TypeVarState::Unbound { name, level } => {
                    if print_level {
                        format!("'{}:{}", name, level_to_string(*level))
                    } else {
                        format!("'{}", name)
                    }
                }
                TypeVarState::Link(target) => pp(target, print_level),
            },
            TypeView::Tup { items, levels } => {
                if levels.level_new == MARKER_LEVEL {
                    return "<!back-ref>".to_string();
                }
                let saved = levels.level_new;
                let level_doc = doc_level(&levels, print_level);
                set_level_new(&ty, MARKER_LEVEL);
                let inner = items
                    .iter()
                    .map(|t| pp(t, print_level))
                    .collect::<Vec<_>>()
                    .join(", ");
                set_level_new(&ty, saved);
                format!("({}){}", inner, level_doc)
            }
            TypeView::Arr { items, levels } => {
                if levels.level_new == MARKER_LEVEL {
                    return "<!back-ref>".to_string();
                }
                let saved = levels.level_new;
                let level_doc = doc_level(&levels, print_level);
                set_level_new(&ty, MARKER_LEVEL);
                let inner = items
                    .iter()
                    .map(|t| pp(t, print_level))
                    .collect::<Vec<_>>()
                    .join(", ");
                set_level_new(&ty, saved);
                format!("[{}]{}", inner, level_doc)
            }
            TypeView::Arrow { args, ret, levels } => {
                if levels.level_new == MARKER_LEVEL {
                    return "<!back-ref>".to_string();
                }
                let saved = levels.level_new;
                let level_doc = doc_level(&levels, print_level);
                set_level_new(&ty, MARKER_LEVEL);
                let args_doc = if !args.is_empty() {
                    let inner = args
                        .iter()
                        .map(|t| pp(t, print_level))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("({})", inner)
                } else {
                    args.iter()
                        .map(|t| pp(t, print_level))
                        .collect::<Vec<_>>()
                        .join(", ")
                };
                let ret_doc = pp(&ret, print_level);
                set_level_new(&ty, saved);
                format!("{} -> {}{}", args_doc, ret_doc, level_doc)
            }
            TypeView::App { name, args, levels } => {
                if levels.level_new == MARKER_LEVEL {
                    return "<!back-ref>".to_string();
                }
                let saved = levels.level_new;
                let level_doc = doc_level(&levels, print_level);
                set_level_new(&ty, MARKER_LEVEL);
                let args_doc = if args.is_empty() {
                    String::new()
                } else {
                    format!(
                        " {}",
                        args.iter()
                            .map(|t| pp(t, print_level))
                            .collect::<Vec<_>>()
                            .join(" ")
                    )
                };
                set_level_new(&ty, saved);
                format!("{}{}{}", name, args_doc, level_doc)
            }
        }
    }
    pp(ty, print_level)
}

type Ctx = BTreeMap<String, TypeRef>;
type Arity = BTreeMap<String, usize>;

fn update_ctx_nodup(ctx: &Ctx, key: &str, value: TypeRef) -> TyResult<Ctx> {
    if ctx.contains_key(key) {
        return Err(TypingError::new(format!(
            "update_ctx_nodup: duplicate definition: {key}"
        )));
    }
    let mut next = ctx.clone();
    next.insert(key.to_string(), value);
    Ok(next)
}

#[allow(dead_code)]
fn update_ctx_shadow(ctx: &Ctx, key: &str, value: TypeRef) -> Ctx {
    let mut next = ctx.clone();
    next.insert(key.to_string(), value);
    next
}

fn update_arity_nodup(arity: &Arity, key: &str, value: usize) -> TyResult<Arity> {
    if arity.contains_key(key) {
        return Err(TypingError::new(format!(
            "update_ctx_nodup: duplicate definition: {key}"
        )));
    }
    let mut next = arity.clone();
    next.insert(key.to_string(), value);
    Ok(next)
}

fn type_of_builtin(name: &str) -> TyResult<TypeRef> {
    match name {
        "print_endline" | "print_string" => Ok(new_arrow(vec![ty_prim(Prim::Str)], ty_prim(Prim::Unit))),
        _ => Err(TypingError::new("type_of_builtin: unknown builtin")),
    }
}

fn type_of_op(op: &str) -> TyResult<TypeRef> {
    match op {
        "+" | "-" | "*" | "/" | "%" => {
            let t = new_tvar();
            Ok(new_arrow(vec![t.clone(), t.clone()], t))
        }
        "<" | "<=" | ">" | ">=" | "==" | "!=" => {
            let t = new_tvar();
            Ok(new_arrow(vec![t.clone(), t.clone()], ty_prim(Prim::Bool)))
        }
        _ => Err(TypingError::new(format!(
            "type_of_op: unknown op: {op}"
        ))),
    }
}

#[derive(Clone)]
struct PatternInfo {
    ty: TypeRef,
    bindings: Vec<(String, TypeRef)>,
}

fn type_of_pattern(ctx: &Ctx, pat: &Pattern) -> TyResult<PatternInfo> {
    match pat {
        Pattern::Any => Ok(PatternInfo {
            ty: new_tvar(),
            bindings: Vec::new(),
        }),
        Pattern::Int(_) => Ok(PatternInfo {
            ty: ty_prim(Prim::Int),
            bindings: Vec::new(),
        }),
        Pattern::Bool(_) => Ok(PatternInfo {
            ty: ty_prim(Prim::Bool),
            bindings: Vec::new(),
        }),
        Pattern::Unit => Ok(PatternInfo {
            ty: ty_prim(Prim::Unit),
            bindings: Vec::new(),
        }),
        Pattern::Var(name) => {
            let tv = new_tvar();
            Ok(PatternInfo {
                ty: tv.clone(),
                bindings: vec![(name.clone(), tv)],
            })
        }
        Pattern::Tup(items) => {
            let mut tys = Vec::new();
            let mut bindings = Vec::new();
            for item in items {
                let info = type_of_pattern(ctx, item)?;
                tys.push(info.ty);
                bindings.extend(info.bindings);
            }
            Ok(PatternInfo {
                ty: new_tup(tys),
                bindings,
            })
        }
        Pattern::CtorApp { name, args } => {
            let ctor_ty = ctx
                .get(name)
                .ok_or_else(|| TypingError::new(format!("Constructor not found: {name}")))?;
            let ctor_ty = instantiate(ctor_ty);
            match args.as_ref() {
                None => Ok(PatternInfo {
                    ty: ctor_ty,
                    bindings: Vec::new(),
                }),
                Some(args) if args.is_empty() => Ok(PatternInfo {
                    ty: ctor_ty,
                    bindings: Vec::new(),
                }),
                Some(args) => {
                    let ctor_arity = match view(&repr(&ctor_ty)) {
                        TypeView::Arrow { args, .. } => Some(args.len()),
                        _ => None,
                    };
                    let mut arg_refs: Vec<&Pattern> = Vec::new();
                    if args.len() == 1 {
                        if let Pattern::Tup(items) = &args[0] {
                            if ctor_arity == Some(items.len()) {
                                arg_refs.extend(items.iter());
                            } else {
                                arg_refs.extend(args.iter());
                            }
                        } else {
                            arg_refs.extend(args.iter());
                        }
                    } else {
                        arg_refs.extend(args.iter());
                    }

                    let mut arg_tys = Vec::new();
                    let mut bindings = Vec::new();
                    for arg in arg_refs {
                        let info = type_of_pattern(ctx, arg)?;
                        arg_tys.push(info.ty);
                        bindings.extend(info.bindings);
                    }
                    let ret = new_tvar();
                    unify(&ctor_ty, &new_arrow(arg_tys, ret.clone()))?;
                    Ok(PatternInfo { ty: ret, bindings })
                }
            }
        }
    }
}

fn bind_pattern_variables_shadow(ctx: &Ctx, bindings: &[(String, TypeRef)]) -> TyResult<Ctx> {
    let mut seen = HashSet::new();
    let mut next = ctx.clone();
    for (name, ty) in bindings {
        if !seen.insert(name) {
            return Err(TypingError::new(format!(
                "Variable {name} already bound"
            )));
        }
        next.insert(name.clone(), ty.clone());
    }
    Ok(next)
}

fn generalize_pattern_variables(bindings: &[(String, TypeRef)]) -> TyResult<()> {
    for (_, ty) in bindings {
        generalize(ty)?;
    }
    Ok(())
}

fn type_of(ctx: &Ctx, expr: &Expr) -> TyResult<TypeRef> {
    let result: TyResult<TypeRef> = (|| match expr {
        Expr::Unit => Ok(ty_prim(Prim::Unit)),
        Expr::Int(_) => Ok(ty_prim(Prim::Int)),
        Expr::Bool(_) => Ok(ty_prim(Prim::Bool)),
        Expr::Str(_) => Ok(ty_prim(Prim::Str)),
        Expr::Builtin(name) => {
            let ty = type_of_builtin(name)?;
            Ok(instantiate(&ty))
        }
        Expr::Var(name) => {
            let ty = ctx
                .get(name)
                .ok_or_else(|| TypingError::new(format!("Variable not found: {name}")))?;
            Ok(instantiate(ty))
        }
        Expr::GVar(name) => {
            let ty = ctx.get(name).ok_or_else(|| {
                TypingError::new(format!("Global definition not found: {name}"))
            })?;
            Ok(instantiate(ty))
        }
        Expr::Ctor(name) => {
            let ty = ctx
                .get(name)
                .ok_or_else(|| TypingError::new(format!("Constructor not found: {name}")))?;
            Ok(instantiate(ty))
        }
        Expr::App(fun, args) => {
            let fun_ty = type_of(ctx, fun)?;
            let mut arg_tys = Vec::new();
            for arg in args {
                arg_tys.push(type_of(ctx, arg)?);
            }
            let ret = new_tvar();
            unify(&fun_ty, &new_arrow(arg_tys, ret.clone()))?;
            Ok(ret)
        }
        Expr::If(cond, then_branch, else_branch) => {
            let cond_ty = type_of(ctx, cond)?;
            let then_ty = type_of(ctx, then_branch)?;
            let else_ty = type_of(ctx, else_branch)?;
            unify(&cond_ty, &ty_prim(Prim::Bool))?;
            unify(&then_ty, &else_ty)?;
            Ok(then_ty)
        }
        Expr::Op(op, lhs, rhs) => {
            let op_ty = type_of_op(op)?;
            let lhs_ty = type_of(ctx, lhs)?;
            let rhs_ty = type_of(ctx, rhs)?;
            let ret = new_tvar();
            unify(&op_ty, &new_arrow(vec![lhs_ty, rhs_ty], ret.clone()))?;
            Ok(ret)
        }
        Expr::Let(binding, body) => match &**binding {
            Binding::Seq(expr) => {
                let ty1 = type_of(ctx, expr)?;
                unify(&ty1, &ty_prim(Prim::Unit))?;
                type_of(ctx, body)
            }
            Binding::One(pat, expr) => {
                enter_level();
                let ty1 = type_of(ctx, expr)?;
                cycle_free(&ty1)?;
                let pat_info = type_of_pattern(ctx, pat)?;
                unify(&pat_info.ty, &ty1)?;
                leave_level();
                generalize_pattern_variables(&pat_info.bindings)?;
                if pat_info.bindings.is_empty() {
                    generalize(&pat_info.ty)?;
                }
                let ctx2 = bind_pattern_variables_shadow(ctx, &pat_info.bindings)?;
                type_of(&ctx2, body)
            }
            Binding::Rec(bindings) => {
                enter_level();
                let mut infos = Vec::new();
                for (pat, expr) in bindings {
                    let pat_info = type_of_pattern(ctx, pat)?;
                    infos.push((pat_info, expr));
                }
                let mut rec_ctx = ctx.clone();
                for (info, _) in &infos {
                    rec_ctx = bind_pattern_variables_shadow(&rec_ctx, &info.bindings)?;
                }
                for (info, expr) in &infos {
                    let ty_e = type_of(&rec_ctx, expr)?;
                    unify(&info.ty, &ty_e)?;
                }
                leave_level();
                for (info, _) in &infos {
                    generalize_pattern_variables(&info.bindings)?;
                    cycle_free(&info.ty)?;
                }
                let mut ctx_final = ctx.clone();
                for (info, _) in infos {
                    ctx_final = bind_pattern_variables_shadow(&ctx_final, &info.bindings)?;
                }
                type_of(&ctx_final, body)
            }
        },
        Expr::Tup(items) => {
            let mut tys = Vec::new();
            for item in items {
                tys.push(type_of(ctx, item)?);
            }
            Ok(new_tup(tys))
        }
        Expr::Arr(items) => {
            let mut tys = Vec::new();
            for item in items {
                tys.push(type_of(ctx, item)?);
            }
            Ok(new_arr(tys))
        }
        Expr::Lam(patterns, body) => {
            let mut arg_tys = Vec::new();
            let mut bindings = Vec::new();
            for pat in patterns {
                let info = type_of_pattern(ctx, pat)?;
                arg_tys.push(info.ty);
                bindings.extend(info.bindings);
            }
            let ctx2 = bind_pattern_variables_shadow(ctx, &bindings)?;
            let body_ty = type_of(&ctx2, body)?;
            Ok(new_arrow(arg_tys, body_ty))
        }
        Expr::Sel(_, Field::Index(_)) | Expr::Sel(_, Field::Name(_)) => {
            Err(TypingError::new("selection is not implemented"))
        }
        Expr::Match(_, cases) if cases.is_empty() => {
            Err(TypingError::new("match with no cases"))
        }
        Expr::Match(target, cases) => {
            let target_ty = type_of(ctx, target)?;
            let mut case_expr_tys = Vec::new();
            for (pat, expr) in cases {
                let pat_info = type_of_pattern(ctx, pat)?;
                let ctx2 = bind_pattern_variables_shadow(ctx, &pat_info.bindings)?;
                let expr_ty = type_of(&ctx2, expr)?;
                unify(&pat_info.ty, &target_ty)?;
                case_expr_tys.push(expr_ty);
            }
            let first = case_expr_tys
                .first()
                .cloned()
                .ok_or_else(|| TypingError::new("match with no cases"))?;
            for ty in case_expr_tys.iter().skip(1) {
                unify(ty, &first)?;
            }
            Ok(first)
        }
    })();
    result.map_err(|err| err.with_expr(pp_expr(expr, false, 0)))
}

fn convert_ty(ctx: &BTreeMap<String, TypeRef>, arity: &Arity, ty: &Ty) -> TyResult<TypeRef> {
    match ty {
        Ty::Unit => Ok(ty_prim(Prim::Unit)),
        Ty::Int => Ok(ty_prim(Prim::Int)),
        Ty::Float => Ok(ty_prim(Prim::Float)),
        Ty::Bool => Ok(ty_prim(Prim::Bool)),
        Ty::Named(name) => match arity.get(name) {
            Some(0) => Ok(new_app(name.clone(), Vec::new())),
            Some(n) => Err(TypingError::new(format!(
                "Type {name} requires {n} arguments, but you provided 0"
            ))),
            None => Err(TypingError::new(format!("Type {name} not defined"))),
        },
        Ty::Apply(base, args) => match &**base {
            Ty::Named(name) => match arity.get(name) {
                Some(expected) if *expected == args.len() => {
                    let mut converted = Vec::new();
                    for arg in args {
                        converted.push(convert_ty(ctx, arity, arg)?);
                    }
                    Ok(new_app(name.clone(), converted))
                }
                Some(expected) => Err(TypingError::new(format!(
                    "Type {name} requires {expected} arguments, but you provided {}",
                    args.len()
                ))),
                None => Err(TypingError::new(format!("Type {name} not defined"))),
            },
            _ => Err(TypingError::new(
                "Type application has invalid syntax".to_string(),
            )),
        },
        Ty::Arrow(_, _) => {
            let mut args = Vec::new();
            let mut cursor = ty;
            while let Ty::Arrow(left, right) = cursor {
                args.push(left.as_ref());
                cursor = right.as_ref();
            }
            let mut converted_args = Vec::new();
            for arg in args {
                converted_args.push(convert_ty(ctx, arity, arg)?);
            }
            let ret = convert_ty(ctx, arity, cursor)?;
            Ok(new_arrow(converted_args, ret))
        }
        Ty::Tuple(items) => {
            let mut converted = Vec::new();
            for item in items {
                converted.push(convert_ty(ctx, arity, item)?);
            }
            Ok(new_tup(converted))
        }
        Ty::NamedVar(name) => ctx
            .get(name)
            .cloned()
            .ok_or_else(|| TypingError::new(format!("Type variable not found: {name}"))),
    }
}

fn decl_ctor(
    arity: &Arity,
    enum_name: &str,
    _ctor_name: &str,
    args: &[Ty],
    params: &[String],
) -> TyResult<TypeRef> {
    enter_level();
    let mut ty_params = Vec::new();
    let mut ty_ctx = BTreeMap::new();
    for param in params {
        let tv = new_tvar();
        ty_ctx.insert(param.clone(), tv.clone());
        ty_params.push(tv);
    }
    let ret = new_app(enum_name.to_string(), ty_params);
    let mut arg_tys = Vec::new();
    for arg in args {
        arg_tys.push(convert_ty(&ty_ctx, arity, arg)?);
    }
    let ctor_ty = if arg_tys.is_empty() {
        ret
    } else {
        new_arrow(arg_tys, ret)
    };
    leave_level();
    generalize(&ctor_ty)?;
    Ok(ctor_ty)
}

fn decl_type(
    ctx: &Ctx,
    arity: &Arity,
    binding: &TyBinding,
) -> TyResult<(Vec<(String, TypeRef)>, Ctx, Arity)> {
    match binding {
        TyBinding::One { name, kind } => {
            let params = match kind {
                TyKind::Enum { params, .. } => params,
            };
            let arity = update_arity_nodup(arity, name, params.len())?;
            let mut ctor_types = Vec::new();
            let mut next_ctx = ctx.clone();
            let ctors = match kind {
                TyKind::Enum { ctors, .. } => ctors,
            };
            for ctor in ctors {
                let ty = decl_ctor(&arity, name, &ctor.name, &ctor.args, params)?;
                next_ctx = update_ctx_nodup(&next_ctx, &ctor.name, ty.clone())?;
                ctor_types.push((ctor.name.clone(), ty));
            }
            Ok((ctor_types, next_ctx, arity))
        }
        TyBinding::Rec(groups) => {
            let mut arity_next = arity.clone();
            for (name, kind) in groups {
                let params = match kind {
                    TyKind::Enum { params, .. } => params,
                };
                arity_next = update_arity_nodup(&arity_next, name, params.len())?;
            }
            let mut next_ctx = ctx.clone();
            for (name, kind) in groups {
                let params = match kind {
                    TyKind::Enum { params, .. } => params,
                };
                let ctors = match kind {
                    TyKind::Enum { ctors, .. } => ctors,
                };
                for ctor in ctors {
                    let ty = decl_ctor(&arity_next, name, &ctor.name, &ctor.args, params)?;
                    next_ctx = update_ctx_nodup(&next_ctx, &ctor.name, ty)?;
                }
            }
            Ok((Vec::new(), next_ctx, arity_next))
        }
    }
}

fn reset_state() {
    reset_level_adjustment();
    reset_levels();
    reset_fresh();
}

fn infer_top_level(
    stmt: &Stmt,
    ctx: &Ctx,
    arity: &Arity,
    print_level: bool,
) -> TyResult<(String, Ctx, Arity)> {
    match stmt {
        Stmt::Type(binding) => {
            let (ctor_types, ctx, arity) = decl_type(ctx, arity, binding)?;
            let mut out = String::new();
            if !ctor_types.is_empty() {
                let mut lines = Vec::new();
                for (name, ty) in ctor_types {
                    lines.push(format!("(* {}: {} *)", name, pp_ty(&ty, print_level)));
                }
                out.push_str(&lines.join("\n"));
                out.push('\n');
            }
            out.push_str(&pp_stmt(stmt));
            Ok((out, ctx, arity))
        }
        Stmt::Term(binding) => match binding {
            Binding::Seq(expr) => {
                let ty = type_of(ctx, expr)?;
                cycle_free(&ty)?;
                let comment = format!("(* {} *)", pp_ty(&ty, print_level));
                let out = format!("{}\n{}", comment, pp_stmt(stmt));
                Ok((out, ctx.clone(), arity.clone()))
            }
            Binding::One(pat, expr) => {
                enter_level();
                let ty_e = type_of(ctx, expr)?;
                let pat_info = type_of_pattern(ctx, pat)?;
                unify(&pat_info.ty, &ty_e)?;
                leave_level();
                generalize_pattern_variables(&pat_info.bindings)?;
                if pat_info.bindings.is_empty() {
                    generalize(&pat_info.ty)?;
                }
                cycle_free(&pat_info.ty)?;
                let ctx_next = bind_pattern_variables_shadow(ctx, &pat_info.bindings)?;
                let comment = format!(
                    "(* {} {} *)",
                    pp_pattern(pat, false),
                    pp_ty(&pat_info.ty, print_level)
                );
                let out = format!("{}\n{}", comment, pp_stmt(stmt));
                Ok((out, ctx_next, arity.clone()))
            }
            Binding::Rec(bindings) => {
                enter_level();
                let mut infos = Vec::new();
                for (pat, expr) in bindings {
                    let info = type_of_pattern(ctx, pat)?;
                    infos.push((pat, expr, info));
                }
                let mut rec_ctx = ctx.clone();
                for (_, _, info) in &infos {
                    rec_ctx = bind_pattern_variables_shadow(&rec_ctx, &info.bindings)?;
                }
                for (_, expr, info) in &infos {
                    let ty_e = type_of(&rec_ctx, expr)?;
                    unify(&info.ty, &ty_e)?;
                }
                leave_level();
                for (_, _, info) in &infos {
                    generalize_pattern_variables(&info.bindings)?;
                    cycle_free(&info.ty)?;
                }
                let mut ctx_next = ctx.clone();
                for (_, _, info) in &infos {
                    ctx_next = bind_pattern_variables_shadow(&ctx_next, &info.bindings)?;
                }
                let mut parts = Vec::new();
                for (pat, _, info) in infos {
                    parts.push(format!(
                        "{} {}",
                        pp_pattern(pat, false),
                        pp_ty(&info.ty, print_level)
                    ));
                }
                let comment = format!("(* {} *)", parts.join(" and "));
                let out = format!("{}\n{}", comment, pp_stmt(stmt));
                Ok((out, ctx_next, arity.clone()))
            }
        },
    }
}

pub fn typing_output(prog: &Prog, print_level: bool) -> TyResult<String> {
    let mut ctx: Ctx = BTreeMap::new();
    let mut arity: Arity = BTreeMap::new();
    let mut outputs = Vec::new();
    for stmt in prog.stmts() {
        reset_state();
        let (out, next_ctx, next_arity) = infer_top_level(stmt, &ctx, &arity, print_level)?;
        outputs.push(out);
        ctx = next_ctx;
        arity = next_arity;
    }
    Ok(outputs.join("\n"))
}
