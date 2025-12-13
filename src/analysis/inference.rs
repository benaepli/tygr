use crate::analysis::resolver::{
    DefID, Name, Resolved, ResolvedAdt, ResolvedAnnotation, ResolvedAnnotationKind, ResolvedKind,
    ResolvedMatchBranch, ResolvedPattern, ResolvedPatternKind,
};
use crate::builtin::{
    BOOL_TYPE, BuiltinFn, FLOAT_TYPE, INT_TYPE, LIST_TYPE, STRING_TYPE, UNIT_TYPE,
};
use crate::parser::{BinOp, Span};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::rc::Rc;
use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeID(pub usize);

impl fmt::Display for TypeID {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone)]
pub struct TypeScheme {
    pub vars: Vec<TypeID>,
    pub ty: Rc<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Var(TypeID),
    Star(DefID),
    App(Rc<Type>, Rc<Type>),

    Function(Rc<Type>, Rc<Type>),
    Pair(Rc<Type>, Rc<Type>),
    Record(BTreeMap<String, Rc<Type>>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Var(id) => write!(f, "{}", id),
            Type::Star(id) => write!(f, "@{}", id.0),
            Type::App(lhs, rhs) => write!(f, "{}[{}]", lhs, rhs),
            Type::Pair(a, b) => write!(f, "({} * {})", a, b),
            Type::Function(arg, ret) => match arg.as_ref() {
                Type::Function(_, _) => write!(f, "({}) -> {}", arg, ret),
                _ => write!(f, "{} -> {}", arg, ret),
            },
            Type::Record(fields) => {
                write!(f, "{{ ")?;
                let mut first = true;
                for (name, ty) in fields {
                    if !first {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", name, ty)?;
                    first = false;
                }
                write!(f, " }}")
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypedPattern {
    pub kind: TypedPatternKind,
    pub ty: Rc<Type>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TypedPatternKind {
    Var { name: Name },
    Unit,
    Pair(Box<TypedPattern>, Box<TypedPattern>),
    Wildcard,
    Cons(Box<TypedPattern>, Box<TypedPattern>),
    EmptyList,
    Constructor(DefID, Name, Box<TypedPattern>),
}

#[derive(Debug, Clone)]
pub struct TypedMatchPattern {
    pub pattern: TypedPattern,
    pub expr: Box<Typed>,
    pub ty: Rc<Type>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Typed {
    pub kind: TypedKind,
    pub ty: Rc<Type>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TypedKind {
    Var(Name),
    Lambda {
        param: TypedPattern,
        body: Box<Typed>,
        captures: HashSet<Name>,
    },
    App(Box<Typed>, Box<Typed>),
    Let {
        name: TypedPattern,
        value: Box<Typed>,
        body: Box<Typed>,
    },
    Fix(Box<Typed>),
    If(Box<Typed>, Box<Typed>, Box<Typed>),
    Match(Box<Typed>, Vec<TypedMatchPattern>),
    Cons(Box<Typed>, Box<Typed>),

    UnitLit,
    PairLit(Box<Typed>, Box<Typed>),
    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StringLit(String),
    EmptyListLit,
    RecordLit(BTreeMap<String, Typed>),

    BinOp(BinOp, Box<Typed>, Box<Typed>),
    FieldAccess(Box<Typed>, String),

    Builtin(BuiltinFn),
    Constructor(DefID, Name),
}

#[derive(Debug, Clone)]
pub struct TypedAdt {
    pub schemes: HashMap<Name, TypeScheme>,
    pub ty: Rc<Type>,
}

type Environment = HashMap<Name, TypeScheme>;
type Substitution = HashMap<TypeID, Rc<Type>>;
type TypeContext = HashMap<DefID, Rc<Type>>;

pub struct Inferrer {
    substitution: Substitution,
    next_var: TypeID,

    type_ctx: TypeContext,

    adts: HashMap<DefID, TypedAdt>,
}

#[derive(Debug, Error)]
pub enum TypeError {
    #[error("type mismatch: expected {0}, found {1}")]
    Mismatch(Rc<Type>, Rc<Type>, Span),

    #[error("occurs check failed: type variable {0} occurs in {1}")]
    OccursCheck(TypeID, Rc<Type>, Span),

    #[error("unbound variable: {0}")]
    UnboundVariable(Name, Span),

    #[error("record field mismatch: records have different fields")]
    RecordFieldMismatch(Rc<Type>, Rc<Type>, Span),

    #[error("field access on non-record type: {0}")]
    FieldAccessOnNonRecord(Rc<Type>, Span),
}

impl Inferrer {
    pub fn new() -> Self {
        Self {
            substitution: HashMap::new(),
            next_var: TypeID(0),

            type_ctx: HashMap::new(),

            adts: HashMap::new(),
        }
    }

    fn new_type(&mut self) -> Rc<Type> {
        let id = self.next_var.0;
        self.next_var.0 += 1;
        Rc::new(Type::Var(TypeID(id)))
    }

    fn instantiate_annotation(&self, annot: &ResolvedAnnotation) -> Rc<Type> {
        match &annot.kind {
            ResolvedAnnotationKind::Var(name_id) => {
                if let Some(ty) = self.type_ctx.get(name_id) {
                    ty.clone()
                } else {
                    Rc::new(Type::Star(*name_id))
                }
            }
            ResolvedAnnotationKind::App(lhs, rhs) => {
                let t_lhs = self.instantiate_annotation(lhs);
                let t_rhs = self.instantiate_annotation(rhs);
                Rc::new(Type::App(t_lhs, t_rhs))
            }
            ResolvedAnnotationKind::Pair(lhs, rhs) => {
                let t_lhs = self.instantiate_annotation(lhs);
                let t_rhs = self.instantiate_annotation(rhs);
                Rc::new(Type::Pair(t_lhs, t_rhs))
            }
            ResolvedAnnotationKind::Lambda(param, ret) => {
                let t_param = self.instantiate_annotation(param);
                let t_ret = self.instantiate_annotation(ret);
                Rc::new(Type::Function(t_param, t_ret))
            }
            ResolvedAnnotationKind::Record(fields) => {
                let mut field_types = BTreeMap::new();
                for (name, annot) in fields {
                    field_types.insert(name.clone(), self.instantiate_annotation(annot));
                }
                Rc::new(Type::Record(field_types))
            }
        }
    }

    pub fn register_adt(&mut self, adt: ResolvedAdt) {
        let mut params = Vec::new();
        for param_id in adt.type_params {
            let id = TypeID(self.next_var.0);
            self.next_var.0 += 1;
            let ty = Rc::new(Type::Var(id));
            self.type_ctx.insert(param_id.clone(), ty);
            params.push(id);
        }

        let mut schemes = HashMap::new();
        let ty = Rc::new(Type::Star(adt.name));

        for (name, ctor) in adt.constructors.into_iter() {
            let instantiated = self.instantiate_annotation(&ctor.annotation);
            schemes.insert(
                name,
                TypeScheme {
                    vars: params.clone(),
                    ty: Rc::new(Type::Function(instantiated, ty.clone())),
                },
            );
        }
    }

    fn apply_subst(&self, ty: &Rc<Type>) -> Rc<Type> {
        match ty.as_ref() {
            Type::Var(id) => {
                if let Some(t) = self.substitution.get(id) {
                    self.apply_subst(t)
                } else {
                    ty.clone()
                }
            }
            Type::Pair(a, b) => {
                let a_subst = self.apply_subst(a);
                let b_subst = self.apply_subst(b);
                Rc::new(Type::Pair(a_subst, b_subst))
            }
            Type::Function(arg, ret) => {
                let arg_subst = self.apply_subst(arg);
                let ret_subst = self.apply_subst(ret);
                Rc::new(Type::Function(arg_subst, ret_subst))
            }
            Type::App(lhs, rhs) => {
                let lhs_subst = self.apply_subst(lhs);
                let rhs_subst = self.apply_subst(rhs);
                Rc::new(Type::App(lhs_subst, rhs_subst))
            }
            Type::Record(fields) => {
                let mut new_fields = BTreeMap::new();
                for (name, ty) in fields {
                    new_fields.insert(name.clone(), self.apply_subst(ty));
                }
                Rc::new(Type::Record(new_fields))
            }
            Type::Star(_) => ty.clone(),
        }
    }

    fn instantiate(&mut self, scheme: &TypeScheme) -> Rc<Type> {
        let mut mapping = HashMap::new();
        for &var in &scheme.vars {
            mapping.insert(var, self.new_type());
        }
        self.instantiate_with_mapping(&scheme.ty, &mapping)
    }

    fn instantiate_with_mapping(
        &self,
        ty: &Rc<Type>,
        mapping: &HashMap<TypeID, Rc<Type>>,
    ) -> Rc<Type> {
        match ty.as_ref() {
            Type::Var(id) => {
                if let Some(new_ty) = mapping.get(id) {
                    new_ty.clone()
                } else {
                    ty.clone()
                }
            }
            Type::Pair(a, b) => {
                let new_a = self.instantiate_with_mapping(a, mapping);
                let new_b = self.instantiate_with_mapping(b, mapping);
                Rc::new(Type::Pair(new_a, new_b))
            }
            Type::Function(arg, ret) => {
                let new_arg = self.instantiate_with_mapping(arg, mapping);
                let new_ret = self.instantiate_with_mapping(ret, mapping);
                Rc::new(Type::Function(new_arg, new_ret))
            }
            Type::App(lhs, rhs) => {
                let new_lhs = self.instantiate_with_mapping(lhs, mapping);
                let new_rhs = self.instantiate_with_mapping(rhs, mapping);
                Rc::new(Type::App(new_lhs, new_rhs))
            }
            Type::Record(fields) => {
                let mut new_fields = BTreeMap::new();
                for (name, ty) in fields {
                    new_fields.insert(name.clone(), self.instantiate_with_mapping(ty, mapping));
                }
                Rc::new(Type::Record(new_fields))
            }
            Type::Star(_) => ty.clone(),
        }
    }

    fn occurs(&self, id: TypeID, ty: &Rc<Type>) -> bool {
        let ty = self.apply_subst(ty);
        match ty.as_ref() {
            Type::Var(var_id) => *var_id == id,
            Type::Pair(a, b) => self.occurs(id, a) || self.occurs(id, b),
            Type::Function(arg, ret) => self.occurs(id, arg) || self.occurs(id, ret),
            Type::App(lhs, rhs) => self.occurs(id, lhs) || self.occurs(id, rhs),
            Type::Record(fields) => fields.values().any(|ty| self.occurs(id, ty)),
            Type::Star(_) => false,
        }
    }

    fn unify(&mut self, t1: &Rc<Type>, t2: &Rc<Type>, span: Span) -> Result<(), TypeError> {
        let t1 = self.apply_subst(t1);
        let t2 = self.apply_subst(t2);

        match (t1.as_ref(), t2.as_ref()) {
            (Type::Var(id1), Type::Var(id2)) if id1 == id2 => Ok(()),
            (Type::Var(id), _) => self.unify_var(*id, &t2, span),
            (_, Type::Var(id)) => self.unify_var(*id, &t1, span),

            (Type::Star(n1), Type::Star(n2)) if n1 == n2 => Ok(()),

            (Type::App(l1, r1), Type::App(l2, r2)) => {
                self.unify(l1, l2, span)?;
                self.unify(r1, r2, span)
            }

            (Type::Pair(a1, b1), Type::Pair(a2, b2)) => {
                self.unify(a1, a2, span)?;
                self.unify(b1, b2, span)?;
                Ok(())
            }

            (Type::Function(arg1, ret1), Type::Function(arg2, ret2)) => {
                self.unify(arg1, arg2, span)?;
                self.unify(ret1, ret2, span)?;
                Ok(())
            }
            (Type::Record(s1), Type::Record(s2)) => {
                let equal_keys = s1.len() == s2.len() && s1.keys().all(|k| s2.contains_key(k));
                if !equal_keys {
                    return Err(TypeError::RecordFieldMismatch(t1.clone(), t2.clone(), span));
                }
                for k in s1.keys() {
                    let t1 = &s1[k];
                    let t2 = &s2[k];
                    self.unify(t1, t2, span)?;
                }
                Ok(())
            }

            _ => Err(TypeError::Mismatch(t1.clone(), t2.clone(), span)),
        }
    }

    fn unify_var(&mut self, id: TypeID, ty: &Rc<Type>, span: Span) -> Result<(), TypeError> {
        if self.occurs(id, ty) {
            return Err(TypeError::OccursCheck(id, ty.clone(), span));
        }
        self.substitution.insert(id, ty.clone());
        Ok(())
    }

    fn free_in_type(&self, ty: &Rc<Type>) -> HashSet<TypeID> {
        let ty = self.apply_subst(ty);
        match ty.as_ref() {
            Type::Var(id) => {
                let mut set = HashSet::new();
                set.insert(*id);
                set
            }
            Type::Pair(a, b) => {
                let mut set = self.free_in_type(a);
                set.extend(self.free_in_type(b));
                set
            }
            Type::Function(arg, ret) => {
                let mut set = self.free_in_type(arg);
                set.extend(self.free_in_type(ret));
                set
            }
            Type::App(lhs, rhs) => {
                let mut set = self.free_in_type(lhs);
                set.extend(self.free_in_type(rhs));
                set
            }
            Type::Record(fields) => {
                let mut set = HashSet::new();
                for ty in fields.values() {
                    set.extend(self.free_in_type(ty));
                }
                set
            }
            Type::Star(_) => HashSet::new(),
        }
    }

    fn free_in_scheme(&self, scheme: &TypeScheme) -> HashSet<TypeID> {
        let mut free = self.free_in_type(&scheme.ty);
        for &var in &scheme.vars {
            free.remove(&var);
        }
        free
    }

    fn free_in_env(&self, env: &Environment) -> HashSet<TypeID> {
        let mut free = HashSet::new();
        for scheme in env.values() {
            free.extend(self.free_in_scheme(scheme));
        }
        free
    }

    fn generalize(&self, env: &Environment, ty: &Rc<Type>) -> TypeScheme {
        let type_vars = self.free_in_type(ty);
        let env_vars = self.free_in_env(env);
        let vars: Vec<TypeID> = type_vars.difference(&env_vars).copied().collect();
        TypeScheme {
            vars,
            ty: ty.clone(),
        }
    }

    pub fn infer(&mut self, expr: Resolved) -> Result<Typed, TypeError> {
        let env = Environment::new();
        self.infer_type(&env, expr)
    }

    fn infer_pattern(
        &mut self,
        pat: ResolvedPattern,
        new_env: &mut Environment,
    ) -> Result<TypedPattern, TypeError> {
        let span = pat.span;
        match pat.kind {
            ResolvedPatternKind::Var(name) => {
                let ty = self.new_type();
                let scheme = TypeScheme {
                    vars: vec![],
                    ty: ty.clone(),
                };
                new_env.insert(name, scheme);
                Ok(TypedPattern {
                    kind: TypedPatternKind::Var { name },
                    ty,
                    span,
                })
            }
            ResolvedPatternKind::Wildcard => Ok(TypedPattern {
                kind: TypedPatternKind::Wildcard,
                ty: self.new_type(),
                span,
            }),
            ResolvedPatternKind::Unit => Ok(TypedPattern {
                kind: TypedPatternKind::Unit,
                ty: Rc::new(Type::Star(UNIT_TYPE)),
                span,
            }),
            ResolvedPatternKind::Pair(p1, p2) => {
                let typed_p1 = self.infer_pattern(*p1, new_env)?;
                let typed_p2 = self.infer_pattern(*p2, new_env)?;
                let pair_ty = Rc::new(Type::Pair(typed_p1.ty.clone(), typed_p2.ty.clone()));
                Ok(TypedPattern {
                    kind: TypedPatternKind::Pair(Box::new(typed_p1), Box::new(typed_p2)),
                    ty: pair_ty,
                    span,
                })
            }
            ResolvedPatternKind::Cons(p1, p2) => {
                let typed_p1 = self.infer_pattern(*p1, new_env)?;
                let typed_p2 = self.infer_pattern(*p2, new_env)?;

                let elem_ty = self.new_type();
                let list_ty = Rc::new(Type::App(Rc::new(Type::Star(LIST_TYPE)), elem_ty.clone()));

                self.unify(&typed_p1.ty, &elem_ty, typed_p1.span)?;
                self.unify(&typed_p2.ty, &list_ty, typed_p2.span)?;

                Ok(TypedPattern {
                    kind: TypedPatternKind::Cons(Box::new(typed_p1), Box::new(typed_p2)),
                    ty: list_ty,
                    span,
                })
            }
            ResolvedPatternKind::EmptyList => Ok(TypedPattern {
                kind: TypedPatternKind::EmptyList,
                ty: Rc::new(Type::App(Rc::new(Type::Star(LIST_TYPE)), self.new_type())),
                span,
            }),
            ResolvedPatternKind::Constructor(adt_id, ctor_id, pat) => {
                let Some(adt) = self.adts.get(&adt_id) else {
                    todo!();
                };
                let Some(ctor_scheme) = adt.schemes.get(&ctor_id).cloned() else {
                    todo!();
                };

                let ctor_ty = self.instantiate(&ctor_scheme);
                let Type::Function(arg_ty, adt_ty) = ctor_ty.as_ref() else {
                    todo!();
                };

                let typed_pat = self.infer_pattern(*pat, new_env)?;
                self.unify(&typed_pat.ty, arg_ty, typed_pat.span)?;

                Ok(TypedPattern {
                    kind: TypedPatternKind::Constructor(adt_id, ctor_id, Box::new(typed_pat)),
                    ty: adt_ty.clone(),
                    span,
                })
            }
        }
    }

    fn infer_type(&mut self, env: &Environment, expr: Resolved) -> Result<Typed, TypeError> {
        let span = expr.span;
        match expr.kind {
            ResolvedKind::IntLit(i) => Ok(Typed {
                kind: TypedKind::IntLit(i),
                ty: Rc::new(Type::Star(INT_TYPE)),
                span,
            }),
            ResolvedKind::FloatLit(f) => Ok(Typed {
                kind: TypedKind::FloatLit(f),
                ty: Rc::new(Type::Star(FLOAT_TYPE)),
                span,
            }),
            ResolvedKind::BoolLit(b) => Ok(Typed {
                kind: TypedKind::BoolLit(b),
                ty: Rc::new(Type::Star(BOOL_TYPE)),
                span,
            }),
            ResolvedKind::StringLit(s) => Ok(Typed {
                kind: TypedKind::StringLit(s),
                ty: Rc::new(Type::Star(STRING_TYPE)),
                span,
            }),
            ResolvedKind::UnitLit => Ok(Typed {
                kind: TypedKind::UnitLit,
                ty: Rc::new(Type::Star(UNIT_TYPE)),
                span,
            }),
            ResolvedKind::PairLit(first, second) => {
                let typed_first = self.infer_type(env, *first)?;
                let typed_second = self.infer_type(env, *second)?;
                let pair_ty = Rc::new(Type::Pair(typed_first.ty.clone(), typed_second.ty.clone()));
                Ok(Typed {
                    kind: TypedKind::PairLit(Box::new(typed_first), Box::new(typed_second)),
                    ty: pair_ty,
                    span,
                })
            }
            ResolvedKind::Var(name) => {
                let scheme = env
                    .get(&name)
                    .ok_or(TypeError::UnboundVariable(name, span))?;
                let ty = self.instantiate(scheme);
                Ok(Typed {
                    kind: TypedKind::Var(name),
                    ty,
                    span,
                })
            }

            ResolvedKind::Lambda {
                param,
                body,
                captures,
                param_type,
            } => {
                let mut new_env = env.clone();
                let typed_param = self.infer_pattern(param, &mut new_env)?;
                if let Some(annot) = param_type {
                    let expected_ty = self.instantiate_annotation(&annot);
                    self.unify(&typed_param.ty, &expected_ty, typed_param.span)?;
                }

                let typed_body = self.infer_type(&new_env, *body)?;
                let body_ty = self.apply_subst(&typed_body.ty);
                let param_ty_subst = self.apply_subst(&typed_param.ty);

                let fn_ty = Rc::new(Type::Function(param_ty_subst, body_ty));

                Ok(Typed {
                    kind: TypedKind::Lambda {
                        param: typed_param,
                        body: Box::new(typed_body),
                        captures,
                    },
                    ty: fn_ty,
                    span,
                })
            }

            ResolvedKind::App(func, arg) => {
                let typed_func = self.infer_type(env, *func)?;
                let typed_arg = self.infer_type(env, *arg)?;

                let result_ty = self.new_type();
                let expected_fn_ty =
                    Rc::new(Type::Function(typed_arg.ty.clone(), result_ty.clone()));

                self.unify(&typed_func.ty, &expected_fn_ty, span)?;
                let result_ty_subst = self.apply_subst(&result_ty);

                Ok(Typed {
                    kind: TypedKind::App(Box::new(typed_func), Box::new(typed_arg)),
                    ty: result_ty_subst,
                    span,
                })
            }

            ResolvedKind::Let {
                pattern,
                value,
                body,
                value_type,
                type_params,
            } => {
                for param_id in type_params {
                    let ty = self.new_type();
                    self.type_ctx.insert(param_id, ty);
                }
                let typed_value = self.infer_type(env, *value)?;
                if let Some(annot) = value_type {
                    let expected_ty = self.instantiate_annotation(&annot);
                    self.unify(&expected_ty, &typed_value.ty, typed_value.span)?;
                }
                let value_ty = self.apply_subst(&typed_value.ty);

                let mut new_env = Environment::new();
                let typed_pattern = self.infer_pattern(pattern, &mut new_env)?;

                self.unify(&value_ty, &typed_pattern.ty, typed_value.span)?;

                let mut extended_env = env.clone();
                for (name, scheme) in new_env {
                    let s = self.generalize(env, &self.apply_subst(&scheme.ty));
                    extended_env.insert(name, s);
                }

                let typed_body = self.infer_type(&extended_env, *body)?;
                let body_ty = self.apply_subst(&typed_body.ty);

                Ok(Typed {
                    kind: TypedKind::Let {
                        name: typed_pattern,
                        value: Box::new(typed_value),
                        body: Box::new(typed_body),
                    },
                    ty: body_ty,
                    span,
                })
            }

            ResolvedKind::Fix(inner_expr) => {
                let typed_expr = self.infer_type(env, *inner_expr)?;
                let a = self.new_type();

                // Constraint 1: The expression must have type 'a -> 'a.
                let expected_generator_ty = Rc::new(Type::Function(a.clone(), a.clone()));
                self.unify(&typed_expr.ty, &expected_generator_ty, span)?;

                // Constraint 2: 'a' must itself be a function.
                // This prevents using `fix` on simple values.
                let function_shape = Rc::new(Type::Function(self.new_type(), self.new_type()));
                self.unify(&a, &function_shape, span)?;

                // The final type is 'a', which is now guaranteed to be a function.
                let result_ty = self.apply_subst(&a);

                Ok(Typed {
                    kind: TypedKind::Fix(Box::new(typed_expr)),
                    ty: result_ty,
                    span,
                })
            }

            ResolvedKind::If(condition, consequent, alternative) => {
                let typed_cond = self.infer_type(env, *condition)?;
                self.unify(
                    &typed_cond.ty,
                    &Rc::new(Type::Star(BOOL_TYPE)),
                    typed_cond.span,
                )?;

                let typed_cons = self.infer_type(env, *consequent)?;
                let typed_alt = self.infer_type(env, *alternative)?;

                self.unify(&typed_cons.ty, &typed_alt.ty, typed_alt.span)?;
                let result_ty = self.apply_subst(&typed_cons.ty);

                Ok(Typed {
                    kind: TypedKind::If(
                        Box::new(typed_cond),
                        Box::new(typed_cons),
                        Box::new(typed_alt),
                    ),
                    ty: result_ty,
                    span,
                })
            }

            ResolvedKind::Match(expr, branches) => {
                let typed_expr = self.infer_type(env, *expr)?;

                let ret_type = self.new_type();
                let mut typed_branches = Vec::new();
                for ResolvedMatchBranch {
                    pattern,
                    expr: body,
                    span,
                } in branches
                {
                    let mut new_env = env.clone();

                    let typed_pattern = self.infer_pattern(pattern, &mut new_env)?;
                    self.unify(&typed_expr.ty, &typed_pattern.ty, span)?;

                    let typed_body = self.infer_type(&new_env, *body)?;
                    let body_ty = self.apply_subst(&typed_body.ty);
                    let param_ty_subst = self.apply_subst(&typed_pattern.ty);
                    self.unify(&body_ty, &ret_type, span)?;

                    // We treat a match branch's type as a function
                    let fn_ty = Rc::new(Type::Function(param_ty_subst, body_ty));

                    typed_branches.push(TypedMatchPattern {
                        pattern: typed_pattern,
                        expr: Box::new(typed_body),
                        ty: fn_ty,
                        span,
                    })
                }

                Ok(Typed {
                    kind: TypedKind::Match(Box::new(typed_expr), typed_branches),
                    ty: ret_type,
                    span,
                })
            }

            ResolvedKind::Cons(first, second) => {
                let typed_first = self.infer_type(env, *first)?;
                let typed_second = self.infer_type(env, *second)?;

                let elem_ty = self.new_type();
                let list_ty = Rc::new(Type::App(Rc::new(Type::Star(LIST_TYPE)), elem_ty.clone()));

                self.unify(&typed_first.ty, &elem_ty, typed_first.span)?;
                self.unify(&typed_second.ty, &list_ty, typed_second.span)?;

                Ok(Typed {
                    kind: TypedKind::Cons(Box::new(typed_first), Box::new(typed_second)),
                    ty: list_ty,
                    span,
                })
            }

            ResolvedKind::EmptyListLit => {
                let list_ty = Rc::new(Type::App(Rc::new(Type::Star(LIST_TYPE)), self.new_type()));
                Ok(Typed {
                    kind: TypedKind::EmptyListLit,
                    ty: list_ty,
                    span,
                })
            }

            ResolvedKind::RecordLit(fields) => {
                let mut typed_fields = BTreeMap::new();
                let mut field_types = BTreeMap::new();

                for (name, expr) in fields {
                    let typed_expr = self.infer_type(env, expr)?;
                    let field_ty = self.apply_subst(&typed_expr.ty);
                    field_types.insert(name.clone(), field_ty);
                    typed_fields.insert(name, typed_expr);
                }

                let record_ty = Rc::new(Type::Record(field_types));

                Ok(Typed {
                    kind: TypedKind::RecordLit(typed_fields),
                    ty: record_ty,
                    span,
                })
            }

            ResolvedKind::BinOp(op, left, right) => {
                let typed_left = self.infer_type(env, *left)?;
                let typed_right = self.infer_type(env, *right)?;

                self.unify(
                    &typed_left.ty,
                    &Rc::new(Type::Star(BOOL_TYPE)),
                    typed_left.span,
                )?;
                self.unify(
                    &typed_right.ty,
                    &Rc::new(Type::Star(BOOL_TYPE)),
                    typed_right.span,
                )?;

                Ok(Typed {
                    kind: TypedKind::BinOp(op, Box::new(typed_left), Box::new(typed_right)),
                    ty: Rc::new(Type::Star(BOOL_TYPE)),
                    span,
                })
            }

            ResolvedKind::FieldAccess(expr, field_name) => {
                let typed_expr = self.infer_type(env, *expr)?;
                let field_ty = self.new_type();

                let t1 = self.apply_subst(&typed_expr.ty);
                let Type::Record(s) = t1.as_ref() else {
                    return Err(TypeError::FieldAccessOnNonRecord(t1.clone(), span));
                };

                let mut expected_fields = s.clone();
                expected_fields.insert(field_name.clone(), field_ty.clone());
                let expected_struct_ty = Rc::new(Type::Record(expected_fields));

                self.unify(&typed_expr.ty, &expected_struct_ty, span)?;

                let result_ty = self.apply_subst(&field_ty);

                Ok(Typed {
                    kind: TypedKind::FieldAccess(Box::new(typed_expr), field_name),
                    ty: result_ty,
                    span,
                })
            }

            ResolvedKind::Builtin(builtin) => {
                let scheme = builtin.type_scheme();
                let ty = self.instantiate(&scheme);

                Ok(Typed {
                    kind: TypedKind::Builtin(builtin),
                    ty,
                    span,
                })
            }
            ResolvedKind::Constructor(adt_id, ctor_id) => {
                let Some(adt) = self.adts.get(&adt_id) else {
                    todo!();
                };
                let Some(ctor) = adt.schemes.get(&ctor_id).cloned() else {
                    todo!();
                };
                let ty = self.instantiate(&ctor);
                Ok(Typed {
                    kind: TypedKind::Constructor(adt_id, ctor_id),
                    ty,
                    span,
                })
            }
        }
    }
}
