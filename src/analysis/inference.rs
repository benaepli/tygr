use crate::analysis::resolver::{
    Name, Resolved, ResolvedKind, ResolvedPattern, ResolvedPatternKind,
};
use crate::builtin::{BuiltinFn, builtin_type};
use crate::parser::{BinOp, Span};
use std::collections::{HashMap, HashSet};
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
    Unit,
    Int,
    Float,
    Bool,
    String,
    Var(TypeID),
    Pair(Rc<Type>, Rc<Type>),
    Function(Rc<Type>, Rc<Type>),
    List(Rc<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Unit => write!(f, "unit"),
            Type::Int => write!(f, "int"),
            Type::Float => write!(f, "float"),
            Type::Bool => write!(f, "bool"),
            Type::String => write!(f, "string"),
            Type::Var(id) => write!(f, "'{}", id),
            Type::Pair(a, b) => write!(f, "({} * {})", a, b),
            Type::Function(arg, ret) => match arg.as_ref() {
                Type::Function(_, _) => write!(f, "({}) -> {}", arg, ret),
                _ => write!(f, "{} -> {}", arg, ret),
            },
            Type::List(ty) => write!(f, "list[{}]", ty),
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
    Cons(Box<Typed>, Box<Typed>),

    UnitLit,
    PairLit(Box<Typed>, Box<Typed>),
    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StringLit(String),
    EmptyListLit,

    BinOp(BinOp, Box<Typed>, Box<Typed>),

    Builtin(BuiltinFn),
}

type Environment = HashMap<Name, TypeScheme>;
type Substitution = HashMap<TypeID, Rc<Type>>;

pub struct Inferrer {
    substitution: Substitution,
    next_var: TypeID,
}

#[derive(Debug, Error)]
pub enum TypeError {
    #[error("type mismatch: expected {0}, found {1}")]
    Mismatch(Rc<Type>, Rc<Type>, Span),

    #[error("occurs check failed: type variable {0} occurs in {1}")]
    OccursCheck(TypeID, Rc<Type>, Span),

    #[error("unbound variable: {0}")]
    UnboundVariable(Name, Span),
}

impl Inferrer {
    pub fn new() -> Self {
        Self {
            substitution: HashMap::new(),
            next_var: TypeID(0),
        }
    }

    fn new_type(&mut self) -> Rc<Type> {
        let id = self.next_var.0;
        self.next_var.0 += 1;
        Rc::new(Type::Var(TypeID(id)))
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
            _ => ty.clone(),
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
            _ => ty.clone(),
        }
    }

    fn occurs(&self, id: TypeID, ty: &Rc<Type>) -> bool {
        let ty = self.apply_subst(ty);
        match ty.as_ref() {
            Type::Var(var_id) => *var_id == id,
            Type::Pair(a, b) => self.occurs(id, a) || self.occurs(id, b),
            Type::Function(arg, ret) => self.occurs(id, arg) || self.occurs(id, ret),
            _ => false,
        }
    }

    fn unify(&mut self, t1: &Rc<Type>, t2: &Rc<Type>, span: Span) -> Result<(), TypeError> {
        let t1 = self.apply_subst(t1);
        let t2 = self.apply_subst(t2);

        match (t1.as_ref(), t2.as_ref()) {
            (Type::Unit, Type::Unit)
            | (Type::Int, Type::Int)
            | (Type::Float, Type::Float)
            | (Type::Bool, Type::Bool)
            | (Type::String, Type::String) => Ok(()),

            (Type::Var(id1), Type::Var(id2)) if id1 == id2 => Ok(()),
            (Type::Var(id), _) => {
                if self.occurs(*id, &t2) {
                    return Err(TypeError::OccursCheck(*id, t2.clone(), span));
                }
                self.substitution.insert(*id, t2.clone());
                Ok(())
            }
            (_, Type::Var(id)) => {
                if self.occurs(*id, &t1) {
                    return Err(TypeError::OccursCheck(*id, t1.clone(), span));
                }
                self.substitution.insert(*id, t1.clone());
                Ok(())
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

            (Type::List(a1), Type::List(a2)) => {
                self.unify(a1, a2, span)?;
                Ok(())
            }

            _ => Err(TypeError::Mismatch(t1.clone(), t2.clone(), span)),
        }
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
            _ => HashSet::new(),
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
                ty: Rc::new(Type::Unit),
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
                let list_ty = Rc::new(Type::List(elem_ty.clone()));

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
                ty: Rc::new(Type::List(self.new_type())),
                span,
            }),
        }
    }

    fn infer_type(&mut self, env: &Environment, expr: Resolved) -> Result<Typed, TypeError> {
        let span = expr.span;
        match expr.kind {
            ResolvedKind::IntLit(i) => Ok(Typed {
                kind: TypedKind::IntLit(i),
                ty: Rc::new(Type::Int),
                span,
            }),
            ResolvedKind::FloatLit(f) => Ok(Typed {
                kind: TypedKind::FloatLit(f),
                ty: Rc::new(Type::Float),
                span,
            }),
            ResolvedKind::BoolLit(b) => Ok(Typed {
                kind: TypedKind::BoolLit(b),
                ty: Rc::new(Type::Bool),
                span,
            }),
            ResolvedKind::StringLit(s) => Ok(Typed {
                kind: TypedKind::StringLit(s),
                ty: Rc::new(Type::String),
                span,
            }),
            ResolvedKind::UnitLit => Ok(Typed {
                kind: TypedKind::UnitLit,
                ty: Rc::new(Type::Unit),
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
            } => {
                let mut new_env = env.clone();
                let typed_param = self.infer_pattern(param, &mut new_env)?;

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
            } => {
                let typed_value = self.infer_type(env, *value)?;
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
                self.unify(&typed_cond.ty, &Rc::new(Type::Bool), typed_cond.span)?;

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

            ResolvedKind::Cons(first, second) => {
                let typed_first = self.infer_type(env, *first)?;
                let typed_second = self.infer_type(env, *second)?;

                let elem_ty = self.new_type();
                let list_ty = Rc::new(Type::List(elem_ty.clone()));

                self.unify(&typed_first.ty, &elem_ty, typed_first.span)?;
                self.unify(&typed_second.ty, &list_ty, typed_second.span)?;

                Ok(Typed {
                    kind: TypedKind::Cons(Box::new(typed_first), Box::new(typed_second)),
                    ty: list_ty,
                    span,
                })
            }

            ResolvedKind::EmptyListLit => {
                let list_ty = Rc::new(Type::List(self.new_type()));
                Ok(Typed {
                    kind: TypedKind::EmptyListLit,
                    ty: list_ty,
                    span,
                })
            }

            ResolvedKind::BinOp(op, left, right) => {
                let typed_left = self.infer_type(env, *left)?;
                let typed_right = self.infer_type(env, *right)?;

                self.unify(&typed_left.ty, &Rc::new(Type::Bool), typed_left.span)?;
                self.unify(&typed_right.ty, &Rc::new(Type::Bool), typed_right.span)?;

                Ok(Typed {
                    kind: TypedKind::BinOp(op, Box::new(typed_left), Box::new(typed_right)),
                    ty: Rc::new(Type::Bool),
                    span,
                })
            }

            ResolvedKind::Builtin(builtin) => {
                let scheme = builtin_type(&builtin);
                let ty = self.instantiate(&scheme);

                Ok(Typed {
                    kind: TypedKind::Builtin(builtin),
                    ty,
                    span,
                })
            }
        }
    }
}
