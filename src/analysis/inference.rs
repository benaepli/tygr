use crate::analysis::name_table::NameTable;
use crate::analysis::resolver::{
    Name, Resolved, ResolvedAnnotation, ResolvedAnnotationKind, ResolvedKind, ResolvedMatchBranch,
    ResolvedPattern, ResolvedPatternKind, ResolvedVariant, TypeName,
};
use crate::builtin::{
    BOOL_TYPE, BuiltinFn, FLOAT_TYPE, INT_TYPE, LIST_TYPE, STRING_TYPE, UNIT_TYPE, builtin_kinds,
};
use crate::parser::{BinOp, Span};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::rc::Rc;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Kind {
    Star,
    Arrow(Rc<Kind>, Rc<Kind>),
    Var(KindID),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct KindID(pub usize);

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
pub struct Type {
    pub ty: TypeKind,
    pub kind: Rc<Kind>,
}

impl Type {
    pub fn new(ty: TypeKind, kind: Rc<Kind>) -> Rc<Self> {
        Rc::new(Self { ty, kind })
    }

    pub fn simple(name: TypeName) -> Rc<Self> {
        Self::new(TypeKind::Con(name), Rc::new(Kind::Star))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeKind {
    Var(TypeID),
    Con(TypeName),
    App(Rc<Type>, Rc<Type>),

    Function(Rc<Type>, Rc<Type>),
    Pair(Rc<Type>, Rc<Type>),
    Record(BTreeMap<String, Rc<Type>>),
}

pub struct TypeDisplay<'a> {
    pub ty: Rc<Type>,
    pub name_table: &'a NameTable,
}

impl<'a> TypeDisplay<'a> {
    pub fn new(ty: Rc<Type>, name_table: &'a NameTable) -> Self {
        Self { ty, name_table }
    }
}

impl<'a> fmt::Display for TypeDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.ty.as_ref().ty {
            TypeKind::Var(id) => write!(f, "{}", id),
            TypeKind::Con(id) => write!(f, "{}", self.name_table.lookup_type_name(&id)),
            TypeKind::App(lhs, rhs) => {
                let lhs_display = TypeDisplay::new(lhs.clone(), self.name_table);
                let rhs_display = TypeDisplay::new(rhs.clone(), self.name_table);
                write!(f, "{}[{}]", lhs_display, rhs_display)
            }
            TypeKind::Pair(a, b) => {
                let a_display = TypeDisplay::new(a.clone(), self.name_table);
                let b_display = TypeDisplay::new(b.clone(), self.name_table);
                write!(f, "({} * {})", a_display, b_display)
            }
            TypeKind::Function(arg, ret) => {
                let arg_display = TypeDisplay::new(arg.clone(), self.name_table);
                let ret_display = TypeDisplay::new(ret.clone(), self.name_table);
                match arg.as_ref().ty {
                    TypeKind::Function(_, _) => write!(f, "({}) -> {}", arg_display, ret_display),
                    _ => write!(f, "{} -> {}", arg_display, ret_display),
                }
            }
            TypeKind::Record(fields) => {
                write!(f, "{{ ")?;
                let mut first = true;
                for (name, ty) in fields {
                    if !first {
                        write!(f, ", ")?;
                    }
                    let ty_display = TypeDisplay::new(ty.clone(), self.name_table);
                    write!(f, "{}: {}", name, ty_display)?;
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
    Record(BTreeMap<String, TypedPattern>),
    Constructor(TypeName, Name, Box<TypedPattern>),
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
    Constructor(TypeName, Name),
}

#[derive(Debug, Clone)]
pub struct TypedVariant {
    pub schemes: HashMap<Name, TypeScheme>,
    pub ty: Rc<Type>,
}

type Environment = HashMap<Name, TypeScheme>;
type Substitution = HashMap<TypeID, Rc<Type>>;
type TypeContext = HashMap<TypeName, Rc<Type>>;

#[derive(Debug, Error)]
pub enum TypeError {
    #[error("type mismatch: expected {1:?}, found {0:?}")]
    Mismatch(Rc<Type>, Rc<Type>, Span),

    #[error("occurs check failed: type variable {0} occurs in {1:?}")]
    OccursCheck(TypeID, Rc<Type>, Span),

    #[error("unbound variable: {0}")]
    UnboundVariable(Name, Span),

    #[error("record field mismatch: records have different fields")]
    RecordFieldMismatch(Rc<Type>, Rc<Type>, Span),

    #[error("field access on non-record type: {0:?}")]
    FieldAccessOnNonRecord(Rc<Type>, Span),

    #[error("variant type not found")]
    VariantNotFound(TypeName, Span),

    #[error("constructor not found in type")]
    ConstructorNotFound(TypeName, Name, Span),

    #[error("invalid constructor type (expected function type)")]
    InvalidConstructorType(Span),

    #[error("kind mismatch: expected {1:?}, found {0:?}")]
    KindMismatch(Rc<Kind>, Rc<Kind>, Span),
}

pub struct Inferrer {
    kind_substitution: HashMap<KindID, Rc<Kind>>,
    next_kind: KindID,

    substitution: Substitution,
    next_var: TypeID,

    type_ctx: TypeContext,

    variants: HashMap<TypeName, TypedVariant>,
}

impl Inferrer {
    pub fn new() -> Self {
        Self {
            kind_substitution: HashMap::new(),
            next_kind: KindID(0),

            substitution: HashMap::new(),
            next_var: TypeID(0),

            type_ctx: HashMap::new(),

            variants: HashMap::new(),
        }
    }

    fn new_kind(&mut self) -> Rc<Kind> {
        let id = KindID(self.next_kind.0);
        self.next_kind.0 += 1;
        Rc::new(Kind::Var(id))
    }

    fn new_type(&mut self) -> TypeKind {
        let id = self.next_var.0;
        self.next_var.0 += 1;
        TypeKind::Var(TypeID(id))
    }

    fn lookup_kind(&self, name: TypeName) -> Option<Rc<Kind>> {
        if let Some(ty) = self.type_ctx.get(&name) {
            return Some(ty.kind.clone());
        }

        if let Some(variant) = self.variants.get(&name) {
            return Some(variant.ty.kind.clone());
        }
        builtin_kinds(name)
    }

    fn unify_kinds(&mut self, k1: &Rc<Kind>, k2: &Rc<Kind>, span: Span) -> Result<(), TypeError> {
        let k1 = self.apply_kind_subst(k1);
        let k2 = self.apply_kind_subst(k2);

        match (k1.as_ref(), k2.as_ref()) {
            (Kind::Star, Kind::Star) => Ok(()),
            (Kind::Arrow(a1, r1), Kind::Arrow(a2, r2)) => {
                self.unify_kinds(a1, a2, span)?;
                self.unify_kinds(r1, r2, span)
            }
            (Kind::Var(id1), Kind::Var(id2)) if id1 == id2 => Ok(()),
            (Kind::Var(id), _) => {
                self.kind_substitution.insert(*id, k2);
                Ok(())
            }
            (_, Kind::Var(id)) => {
                self.kind_substitution.insert(*id, k1);
                Ok(())
            }
            _ => Err(TypeError::KindMismatch(k1, k2, span)),
        }
    }

    fn apply_kind_subst(&self, k: &Rc<Kind>) -> Rc<Kind> {
        match k.as_ref() {
            Kind::Var(id) => {
                if let Some(sub) = self.kind_substitution.get(id) {
                    self.apply_kind_subst(sub)
                } else {
                    k.clone()
                }
            }
            Kind::Arrow(lhs, rhs) => Rc::new(Kind::Arrow(
                self.apply_kind_subst(lhs),
                self.apply_kind_subst(rhs),
            )),
            Kind::Star => k.clone(),
        }
    }

    pub fn instantiate_annotation(&mut self, annot: &ResolvedAnnotation) -> Result<Rc<Type>, TypeError> {
        match &annot.kind {
            ResolvedAnnotationKind::Var(name) => {
                if let Some(ty) = self.type_ctx.get(name) {
                    Ok(ty.clone())
                } else if let Some(kind) = self.lookup_kind(*name) {
                    Ok(Type::new(TypeKind::Con(*name), kind))
                } else {
                    Ok(Type::new(TypeKind::Con(*name), self.new_kind()))
                }
            }
            ResolvedAnnotationKind::App(lhs, rhs) => {
                let t_lhs = self.instantiate_annotation(lhs)?;
                let t_rhs = self.instantiate_annotation(rhs)?;

                let k_ret = self.new_kind();
                let expected_lhs_kind = Rc::new(Kind::Arrow(t_rhs.kind.clone(), k_ret.clone()));

                self.unify_kinds(&t_lhs.kind, &expected_lhs_kind, annot.span)?;

                Ok(Type::new(
                    TypeKind::App(t_lhs, t_rhs),
                    self.apply_kind_subst(&k_ret),
                ))
            }
            ResolvedAnnotationKind::Pair(lhs, rhs) => {
                let t_lhs = self.instantiate_annotation(lhs)?;
                let t_rhs = self.instantiate_annotation(rhs)?;

                self.unify_kinds(&t_lhs.kind, &Rc::new(Kind::Star), annot.span)?;
                self.unify_kinds(&t_rhs.kind, &Rc::new(Kind::Star), annot.span)?;

                Ok(Type::new(TypeKind::Pair(t_lhs, t_rhs), Rc::new(Kind::Star)))
            }
            ResolvedAnnotationKind::Lambda(param, ret) => {
                let t_param = self.instantiate_annotation(param)?;
                let t_ret = self.instantiate_annotation(ret)?;

                self.unify_kinds(&t_param.kind, &Rc::new(Kind::Star), annot.span)?;
                self.unify_kinds(&t_ret.kind, &Rc::new(Kind::Star), annot.span)?;

                Ok(Type::new(
                    TypeKind::Function(t_param, t_ret),
                    Rc::new(Kind::Star),
                ))
            }
            ResolvedAnnotationKind::Record(fields) => {
                let mut new_fields = BTreeMap::new();
                for (name, ann) in fields {
                    let t_field = self.instantiate_annotation(ann)?;
                    self.unify_kinds(&t_field.kind, &Rc::new(Kind::Star), ann.span)?;
                    new_fields.insert(name.clone(), t_field);
                }
                Ok(Type::new(TypeKind::Record(new_fields), Rc::new(Kind::Star)))
            }
        }
    }

    fn apply_wrap(&mut self, lhs: Rc<Type>, args: &[Rc<Type>]) -> Rc<Type> {
        match args.split_first() {
            Some((arg, rest)) => {
                let result_kind = match lhs.kind.as_ref() {
                    Kind::Arrow(_, ret_kind) => ret_kind.clone(),
                    Kind::Var(_) => self.new_kind(),
                    Kind::Star => Rc::new(Kind::Star),
                };
                let new_lhs = Type::new(
                    TypeKind::App(lhs.clone(), arg.clone()),
                    self.apply_kind_subst(&result_kind),
                );
                self.apply_wrap(new_lhs, rest)
            }
            None => lhs,
        }
    }

    pub fn register_variant(&mut self, variant: ResolvedVariant) -> Result<(), TypeError> {
        let mut params = Vec::new();
        let mut param_types = Vec::new();
        for param_id in variant.type_params {
            let id = TypeID(self.next_var.0);
            self.next_var.0 += 1;
            let kind = self.new_kind();
            let ty = Type::new(TypeKind::Var(id), kind);
            param_types.push(ty.clone());
            self.type_ctx.insert(param_id.clone(), ty);
            params.push(id);
        }

        let mut inferred_constructors = Vec::new();
        for (name, ctor) in variant.constructors {
            let ty = self.instantiate_annotation(&ctor.annotation)?;
            inferred_constructors.push((name, ty));
        }

        let mut variant_kind = Rc::new(Kind::Star);
        for p in param_types.iter().rev() {
            let pk = self.apply_kind_subst(&p.kind);
            variant_kind = Rc::new(Kind::Arrow(pk, variant_kind));
        }

        let variant_ty = Type::new(TypeKind::Con(variant.name), variant_kind);
        let mut schemes = HashMap::new();

        for (name, arg_ty) in inferred_constructors {
            let ret_ty = self.apply_wrap(variant_ty.clone(), &param_types);

            schemes.insert(
                name,
                TypeScheme {
                    vars: params.clone(),
                    ty: Type::new(TypeKind::Function(arg_ty, ret_ty), Rc::new(Kind::Star)),
                },
            );
        }

        self.variants.insert(
            variant.name,
            TypedVariant {
                schemes,
                ty: variant_ty,
            },
        );
        Ok(())
    }

    fn apply_subst(&self, ty: &Rc<Type>) -> Rc<Type> {
        match &ty.ty {
            TypeKind::Var(id) => {
                if let Some(t) = self.substitution.get(id) {
                    self.apply_subst(t)
                } else {
                    ty.clone()
                }
            }
            TypeKind::Pair(a, b) => {
                let a_subst = self.apply_subst(a);
                let b_subst = self.apply_subst(b);
                Type::new(TypeKind::Pair(a_subst, b_subst), ty.kind.clone())
            }
            TypeKind::Function(arg, ret) => {
                let arg_subst = self.apply_subst(arg);
                let ret_subst = self.apply_subst(ret);
                Type::new(TypeKind::Function(arg_subst, ret_subst), ty.kind.clone())
            }
            TypeKind::App(lhs, rhs) => {
                let lhs_subst = self.apply_subst(lhs);
                let rhs_subst = self.apply_subst(rhs);
                Type::new(TypeKind::App(lhs_subst, rhs_subst), ty.kind.clone())
            }
            TypeKind::Record(fields) => {
                let mut new_fields = BTreeMap::new();
                for (name, t) in fields {
                    new_fields.insert(name.clone(), self.apply_subst(t));
                }
                Type::new(TypeKind::Record(new_fields), ty.kind.clone())
            }
            TypeKind::Con(_) => ty.clone(),
        }
    }

    fn instantiate(&mut self, scheme: &TypeScheme) -> Rc<Type> {
        let mut mapping = HashMap::new();
        for &var in &scheme.vars {
            mapping.insert(var, Type::new(self.new_type(), self.new_kind()));
        }
        self.instantiate_with_mapping(&scheme.ty, &mapping)
    }

    fn instantiate_with_mapping(
        &self,
        ty: &Rc<Type>,
        mapping: &HashMap<TypeID, Rc<Type>>,
    ) -> Rc<Type> {
        match &ty.ty {
            TypeKind::Var(id) => {
                if let Some(new_ty) = mapping.get(id) {
                    new_ty.clone()
                } else {
                    ty.clone()
                }
            }
            TypeKind::Pair(a, b) => {
                let new_a = self.instantiate_with_mapping(a, mapping);
                let new_b = self.instantiate_with_mapping(b, mapping);
                Type::new(TypeKind::Pair(new_a, new_b), ty.kind.clone())
            }
            TypeKind::Function(arg, ret) => {
                let new_arg = self.instantiate_with_mapping(arg, mapping);
                let new_ret = self.instantiate_with_mapping(ret, mapping);
                Type::new(TypeKind::Function(new_arg, new_ret), ty.kind.clone())
            }
            TypeKind::App(lhs, rhs) => {
                let new_lhs = self.instantiate_with_mapping(lhs, mapping);
                let new_rhs = self.instantiate_with_mapping(rhs, mapping);
                Type::new(TypeKind::App(new_lhs, new_rhs), ty.kind.clone())
            }
            TypeKind::Record(fields) => {
                let mut new_fields = BTreeMap::new();
                for (name, t) in fields {
                    new_fields.insert(name.clone(), self.instantiate_with_mapping(t, mapping));
                }
                Type::new(TypeKind::Record(new_fields), ty.kind.clone())
            }
            TypeKind::Con(_) => ty.clone(),
        }
    }

    fn occurs(&self, id: TypeID, ty: &Rc<Type>) -> bool {
        let ty = self.apply_subst(ty);
        match &ty.ty {
            TypeKind::Var(var_id) => *var_id == id,
            TypeKind::Pair(a, b) => self.occurs(id, a) || self.occurs(id, b),
            TypeKind::Function(arg, ret) => self.occurs(id, arg) || self.occurs(id, ret),
            TypeKind::App(lhs, rhs) => self.occurs(id, lhs) || self.occurs(id, rhs),
            TypeKind::Record(fields) => fields.values().any(|t| self.occurs(id, t)),
            TypeKind::Con(_) => false,
        }
    }

    fn unify(&mut self, t1: &Rc<Type>, t2: &Rc<Type>, span: Span) -> Result<(), TypeError> {
        self.unify_kinds(&t1.kind, &t2.kind, span)?;

        let t1 = self.apply_subst(t1);
        let t2 = self.apply_subst(t2);

        match (&t1.ty, &t2.ty) {
            (TypeKind::Var(id1), TypeKind::Var(id2)) if id1 == id2 => Ok(()),
            (TypeKind::Var(id), _) => self.unify_var(*id, &t2, span),
            (_, TypeKind::Var(id)) => self.unify_var(*id, &t1, span),

            (TypeKind::Con(n1), TypeKind::Con(n2)) if n1 == n2 => Ok(()),

            (TypeKind::App(l1, r1), TypeKind::App(l2, r2)) => {
                self.unify(l1, l2, span)?;
                self.unify(r1, r2, span)
            }

            (TypeKind::Pair(a1, b1), TypeKind::Pair(a2, b2)) => {
                self.unify(a1, a2, span)?;
                self.unify(b1, b2, span)?;
                Ok(())
            }

            (TypeKind::Function(arg1, ret1), TypeKind::Function(arg2, ret2)) => {
                self.unify(arg1, arg2, span)?;
                self.unify(ret1, ret2, span)?;
                Ok(())
            }
            (TypeKind::Record(s1), TypeKind::Record(s2)) => {
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
        match &ty.ty {
            TypeKind::Var(id) => {
                let mut set = HashSet::new();
                set.insert(*id);
                set
            }
            TypeKind::Pair(a, b) => {
                let mut set = self.free_in_type(a);
                set.extend(self.free_in_type(b));
                set
            }
            TypeKind::Function(arg, ret) => {
                let mut set = self.free_in_type(arg);
                set.extend(self.free_in_type(ret));
                set
            }
            TypeKind::App(lhs, rhs) => {
                let mut set = self.free_in_type(lhs);
                set.extend(self.free_in_type(rhs));
                set
            }
            TypeKind::Record(fields) => {
                let mut set = HashSet::new();
                for ty in fields.values() {
                    set.extend(self.free_in_type(ty));
                }
                set
            }
            TypeKind::Con(_) => HashSet::new(),
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

    fn get_list_constructor(&self) -> Rc<Type> {
        let kind = self
            .lookup_kind(LIST_TYPE)
            .expect("List type kind not found");
        Type::new(TypeKind::Con(LIST_TYPE), kind)
    }

    fn infer_pattern(
        &mut self,
        pat: ResolvedPattern,
        new_env: &mut Environment,
    ) -> Result<TypedPattern, TypeError> {
        let span = pat.span;
        match pat.kind {
            ResolvedPatternKind::Var(name) => {
                let ty = Type::new(self.new_type(), Rc::new(Kind::Star));
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
                ty: Type::new(self.new_type(), Rc::new(Kind::Star)),
                span,
            }),
            ResolvedPatternKind::Unit => Ok(TypedPattern {
                kind: TypedPatternKind::Unit,
                ty: Type::simple(UNIT_TYPE),
                span,
            }),
            ResolvedPatternKind::Pair(p1, p2) => {
                let typed_p1 = self.infer_pattern(*p1, new_env)?;
                let typed_p2 = self.infer_pattern(*p2, new_env)?;
                let pair_ty = Type::new(
                    TypeKind::Pair(typed_p1.ty.clone(), typed_p2.ty.clone()),
                    Rc::new(Kind::Star),
                );
                Ok(TypedPattern {
                    kind: TypedPatternKind::Pair(Box::new(typed_p1), Box::new(typed_p2)),
                    ty: pair_ty,
                    span,
                })
            }
            ResolvedPatternKind::Cons(p1, p2) => {
                let typed_p1 = self.infer_pattern(*p1, new_env)?;
                let typed_p2 = self.infer_pattern(*p2, new_env)?;

                let list_ty = Type::new(
                    TypeKind::App(self.get_list_constructor(), typed_p1.ty.clone()),
                    Rc::new(Kind::Star),
                );
                self.unify(&typed_p2.ty, &list_ty, typed_p2.span)?;

                Ok(TypedPattern {
                    kind: TypedPatternKind::Cons(Box::new(typed_p1), Box::new(typed_p2)),
                    ty: list_ty,
                    span,
                })
            }
            ResolvedPatternKind::EmptyList => Ok(TypedPattern {
                kind: TypedPatternKind::EmptyList,
                ty: Type::new(
                    TypeKind::App(
                        self.get_list_constructor(),
                        Type::new(self.new_type(), Rc::new(Kind::Star)),
                    ),
                    Rc::new(Kind::Star),
                ),
                span,
            }),
            ResolvedPatternKind::Record(fields) => {
                let mut typed = BTreeMap::new();
                let mut field_types = BTreeMap::new();
                for (field_name, pattern) in fields {
                    let typed_field = self.infer_pattern(pattern, new_env)?;
                    field_types.insert(field_name.clone(), typed_field.ty.clone());
                    typed.insert(field_name, typed_field);
                }
                let record_ty = Type::new(TypeKind::Record(field_types), Rc::new(Kind::Star));
                Ok(TypedPattern {
                    kind: TypedPatternKind::Record(typed),
                    ty: record_ty,
                    span,
                })
            }
            ResolvedPatternKind::Constructor(variant_id, ctor_id, pat) => {
                let Some(variant) = self.variants.get(&variant_id) else {
                    return Err(TypeError::VariantNotFound(variant_id, span));
                };
                let Some(ctor_scheme) = variant.schemes.get(&ctor_id).cloned() else {
                    return Err(TypeError::ConstructorNotFound(variant_id, ctor_id, span));
                };

                let ctor_ty = self.instantiate(&ctor_scheme);
                let TypeKind::Function(arg_ty, variant_ty) = &ctor_ty.ty else {
                    return Err(TypeError::InvalidConstructorType(span));
                };

                let typed_pat = self.infer_pattern(*pat, new_env)?;
                self.unify(&typed_pat.ty, arg_ty, typed_pat.span)?;

                Ok(TypedPattern {
                    kind: TypedPatternKind::Constructor(variant_id, ctor_id, Box::new(typed_pat)),
                    ty: variant_ty.clone(),
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
                ty: Type::simple(INT_TYPE),
                span,
            }),
            ResolvedKind::FloatLit(f) => Ok(Typed {
                kind: TypedKind::FloatLit(f),
                ty: Type::simple(FLOAT_TYPE),
                span,
            }),
            ResolvedKind::BoolLit(b) => Ok(Typed {
                kind: TypedKind::BoolLit(b),
                ty: Type::simple(BOOL_TYPE),
                span,
            }),
            ResolvedKind::StringLit(s) => Ok(Typed {
                kind: TypedKind::StringLit(s),
                ty: Type::simple(STRING_TYPE),
                span,
            }),
            ResolvedKind::UnitLit => Ok(Typed {
                kind: TypedKind::UnitLit,
                ty: Type::simple(UNIT_TYPE),
                span,
            }),
            ResolvedKind::PairLit(first, second) => {
                let typed_first = self.infer_type(env, *first)?;
                let typed_second = self.infer_type(env, *second)?;
                let pair_ty = Type::new(
                    TypeKind::Pair(typed_first.ty.clone(), typed_second.ty.clone()),
                    Rc::new(Kind::Star),
                );
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
                    let expected_ty = self.instantiate_annotation(&annot)?;
                    self.unify(&typed_param.ty, &expected_ty, typed_param.span)?;
                }

                let typed_body = self.infer_type(&new_env, *body)?;
                let body_ty = self.apply_subst(&typed_body.ty);
                let param_ty_subst = self.apply_subst(&typed_param.ty);

                let fn_ty = Type::new(
                    TypeKind::Function(param_ty_subst, body_ty),
                    Rc::new(Kind::Star),
                );

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

                let result_ty = Type::new(self.new_type(), self.new_kind());
                let expected_fn_ty = Type::new(
                    TypeKind::Function(typed_arg.ty.clone(), result_ty.clone()),
                    Rc::new(Kind::Star),
                );

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
                    let ty = Type::new(self.new_type(), self.new_kind());
                    self.type_ctx.insert(param_id, ty);
                }
                let typed_value = self.infer_type(env, *value)?;
                if let Some(annot) = value_type {
                    let expected_ty = self.instantiate_annotation(&annot)?;
                    self.unify(&typed_value.ty, &expected_ty, typed_value.span)?;
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
                let a = Type::new(self.new_type(), Rc::new(Kind::Star));

                // Constraint 1: The expression must have type 'a -> 'a.
                let expected_generator_ty = Type::new(
                    TypeKind::Function(a.clone(), a.clone()),
                    Rc::new(Kind::Star),
                );
                self.unify(&typed_expr.ty, &expected_generator_ty, span)?;

                // Constraint 2: 'a' must itself be a function.
                // This prevents using `fix` on simple values.
                let function_shape = Rc::new(Type::new(
                    TypeKind::Function(
                        Type::new(self.new_type(), Rc::new(Kind::Star)),
                        Type::new(self.new_type(), Rc::new(Kind::Star)),
                    ),
                    Rc::new(Kind::Star),
                ));
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
                    &Type::new(TypeKind::Con(BOOL_TYPE), Rc::new(Kind::Star)),
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

                let ret_type = Type::new(self.new_type(), Rc::new(Kind::Star));
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
                    let fn_ty = Type::new(
                        TypeKind::Function(param_ty_subst, body_ty),
                        Rc::new(Kind::Star),
                    );

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

                let list_ty = Type::new(
                    TypeKind::App(self.get_list_constructor(), typed_first.ty.clone()),
                    Rc::new(Kind::Star),
                );

                self.unify(&typed_second.ty, &list_ty, typed_second.span)?;

                Ok(Typed {
                    kind: TypedKind::Cons(Box::new(typed_first), Box::new(typed_second)),
                    ty: list_ty,
                    span,
                })
            }

            ResolvedKind::EmptyListLit => {
                let list_ty = Type::new(
                    TypeKind::App(
                        self.get_list_constructor(),
                        Type::new(self.new_type(), Rc::new(Kind::Star)),
                    ),
                    Rc::new(Kind::Star),
                );
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

                let record_ty = Type::new(TypeKind::Record(field_types), Rc::new(Kind::Star));

                Ok(Typed {
                    kind: TypedKind::RecordLit(typed_fields),
                    ty: record_ty,
                    span,
                })
            }

            ResolvedKind::BinOp(op, left, right) => {
                let typed_left = self.infer_type(env, *left)?;
                let typed_right = self.infer_type(env, *right)?;

                self.unify(&typed_left.ty, &Type::simple(BOOL_TYPE), typed_left.span)?;
                self.unify(&typed_right.ty, &Type::simple(BOOL_TYPE), typed_right.span)?;

                Ok(Typed {
                    kind: TypedKind::BinOp(op, Box::new(typed_left), Box::new(typed_right)),
                    ty: Type::simple(BOOL_TYPE),
                    span,
                })
            }

            ResolvedKind::FieldAccess(expr, field_name) => {
                let typed_expr = self.infer_type(env, *expr)?;
                let field_ty = Type::new(self.new_type(), Rc::new(Kind::Star));

                let t1 = self.apply_subst(&typed_expr.ty);
                let TypeKind::Record(s) = &t1.ty else {
                    return Err(TypeError::FieldAccessOnNonRecord(t1.clone(), span));
                };

                let mut expected_fields = s.clone();
                expected_fields.insert(field_name.clone(), field_ty.clone());
                let expected_struct_ty =
                    Type::new(TypeKind::Record(expected_fields), Rc::new(Kind::Star));

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
            ResolvedKind::Constructor(variant_id, ctor_id) => {
                let Some(variant) = self.variants.get(&variant_id) else {
                    return Err(TypeError::VariantNotFound(variant_id, span));
                };
                let Some(ctor) = variant.schemes.get(&ctor_id).cloned() else {
                    return Err(TypeError::ConstructorNotFound(variant_id, ctor_id, span));
                };
                let ty = self.instantiate(&ctor);
                Ok(Typed {
                    kind: TypedKind::Constructor(variant_id, ctor_id),
                    ty,
                    span,
                })
            }
        }
    }
}
