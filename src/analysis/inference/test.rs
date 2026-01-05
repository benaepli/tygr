use super::*;
use crate::analysis::resolver::{
    GlobalName, GlobalType, Name, Resolved, ResolvedAnnotation, ResolvedAnnotationKind,
    ResolvedConstructor, ResolvedKind, ResolvedPattern, ResolvedPatternKind, ResolvedStatement,
    ResolvedTypeAlias, ResolvedVariant, TypeName,
};
use crate::builtin::{BOOL_TYPE, FLOAT_TYPE, INT_TYPE, LIST_TYPE, STRING_TYPE, UNIT_TYPE};
use crate::parser::{SourceId, Span};
use chumsky::span::{SimpleSpan, Span as ChumskySpan};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;

fn span() -> Span {
    SimpleSpan::new(SourceId::SYNTHETIC, 0..0)
}

fn make_type_var(id: usize) -> Rc<Type> {
    Type::new(TypeKind::Var(TypeID(id)), Rc::new(Kind::Star))
}

fn make_int() -> Rc<Type> {
    Type::new(
        TypeKind::Con(GlobalType {
            krate: None,
            name: INT_TYPE,
        }),
        Rc::new(Kind::Star),
    )
}

fn make_float() -> Rc<Type> {
    Type::new(
        TypeKind::Con(GlobalType {
            krate: None,
            name: FLOAT_TYPE,
        }),
        Rc::new(Kind::Star),
    )
}

fn make_bool() -> Rc<Type> {
    Type::new(
        TypeKind::Con(GlobalType {
            krate: None,
            name: BOOL_TYPE,
        }),
        Rc::new(Kind::Star),
    )
}

fn make_string() -> Rc<Type> {
    Type::new(
        TypeKind::Con(GlobalType {
            krate: None,
            name: STRING_TYPE,
        }),
        Rc::new(Kind::Star),
    )
}

fn make_unit() -> Rc<Type> {
    Type::new(
        TypeKind::Con(GlobalType {
            krate: None,
            name: UNIT_TYPE,
        }),
        Rc::new(Kind::Star),
    )
}

fn make_function(arg: Rc<Type>, ret: Rc<Type>) -> Rc<Type> {
    Type::new(TypeKind::Function(arg, ret), Rc::new(Kind::Star))
}

fn make_pair(a: Rc<Type>, b: Rc<Type>) -> Rc<Type> {
    Type::new(TypeKind::Pair(a, b), Rc::new(Kind::Star))
}

fn make_list(elem: Rc<Type>) -> Rc<Type> {
    let list_con = Type::new(
        TypeKind::Con(GlobalType {
            krate: None,
            name: LIST_TYPE,
        }),
        Rc::new(Kind::Arrow(Rc::new(Kind::Star), Rc::new(Kind::Star))),
    );
    Type::new(TypeKind::App(list_con, elem), Rc::new(Kind::Star))
}

fn make_record(fields: Vec<(&str, Rc<Type>)>) -> Rc<Type> {
    let btree: BTreeMap<String, Rc<Type>> = fields
        .into_iter()
        .map(|(k, v)| (k.to_string(), v))
        .collect();
    Type::new(TypeKind::Record(btree), Rc::new(Kind::Star))
}

fn make_scheme(vars: Vec<(usize, Rc<Kind>)>, ty: Rc<Type>) -> TypeScheme {
    TypeScheme {
        vars: vars.into_iter().map(|(id, k)| (TypeID(id), k)).collect(),
        ty,
    }
}

fn global_name(id: usize) -> GlobalName {
    GlobalName {
        krate: None,
        name: Name(id),
    }
}

fn global_type(id: usize) -> GlobalType {
    GlobalType {
        krate: None,
        name: TypeName(id),
    }
}

fn resolved_var(name: GlobalName) -> Resolved {
    Resolved::new(ResolvedKind::Var(name), span())
}

fn resolved_int(val: i64) -> Resolved {
    Resolved::new(ResolvedKind::IntLit(val), span())
}

fn resolved_float(val: f64) -> Resolved {
    Resolved::new(ResolvedKind::FloatLit(val), span())
}

fn resolved_bool(val: bool) -> Resolved {
    Resolved::new(ResolvedKind::BoolLit(val), span())
}

fn resolved_string(val: &str) -> Resolved {
    Resolved::new(ResolvedKind::StringLit(val.to_string()), span())
}

fn resolved_unit() -> Resolved {
    Resolved::new(ResolvedKind::UnitLit, span())
}

fn resolved_pair(a: Resolved, b: Resolved) -> Resolved {
    Resolved::new(ResolvedKind::PairLit(Box::new(a), Box::new(b)), span())
}

fn resolved_empty_list() -> Resolved {
    Resolved::new(ResolvedKind::EmptyListLit, span())
}

fn resolved_cons(head: Resolved, tail: Resolved) -> Resolved {
    Resolved::new(ResolvedKind::Cons(Box::new(head), Box::new(tail)), span())
}

fn resolved_lambda(param: ResolvedPattern, body: Resolved) -> Resolved {
    Resolved::new(
        ResolvedKind::Lambda {
            param,
            body: Box::new(body),
            captures: HashSet::new(),
            param_type: None,
        },
        span(),
    )
}

fn resolved_app(func: Resolved, arg: Resolved) -> Resolved {
    Resolved::new(ResolvedKind::App(Box::new(func), Box::new(arg)), span())
}

fn resolved_if(cond: Resolved, then_expr: Resolved, else_expr: Resolved) -> Resolved {
    Resolved::new(
        ResolvedKind::If(Box::new(cond), Box::new(then_expr), Box::new(else_expr)),
        span(),
    )
}

fn resolved_record(fields: Vec<(&str, Resolved)>) -> Resolved {
    let map: HashMap<String, Resolved> = fields
        .into_iter()
        .map(|(k, v)| (k.to_string(), v))
        .collect();
    Resolved::new(ResolvedKind::RecordLit(map), span())
}

fn resolved_field_access(record: Resolved, field: &str) -> Resolved {
    Resolved::new(
        ResolvedKind::FieldAccess(Box::new(record), field.to_string()),
        span(),
    )
}

fn resolved_block(stmts: Vec<ResolvedStatement>, result: Option<Resolved>) -> Resolved {
    Resolved::new(ResolvedKind::Block(stmts, result.map(Box::new)), span())
}

fn pattern_var(name: GlobalName) -> ResolvedPattern {
    ResolvedPattern::new(ResolvedPatternKind::Var(name), span())
}

fn pattern_wildcard() -> ResolvedPattern {
    ResolvedPattern::new(ResolvedPatternKind::Wildcard, span())
}

fn pattern_unit() -> ResolvedPattern {
    ResolvedPattern::new(ResolvedPatternKind::Unit, span())
}

fn pattern_pair(a: ResolvedPattern, b: ResolvedPattern) -> ResolvedPattern {
    ResolvedPattern::new(ResolvedPatternKind::Pair(Box::new(a), Box::new(b)), span())
}

fn pattern_empty_list() -> ResolvedPattern {
    ResolvedPattern::new(ResolvedPatternKind::EmptyList, span())
}

fn pattern_cons(head: ResolvedPattern, tail: ResolvedPattern) -> ResolvedPattern {
    ResolvedPattern::new(
        ResolvedPatternKind::Cons(Box::new(head), Box::new(tail)),
        span(),
    )
}

fn pattern_record(fields: Vec<(&str, ResolvedPattern)>) -> ResolvedPattern {
    let map: HashMap<String, ResolvedPattern> = fields
        .into_iter()
        .map(|(k, v)| (k.to_string(), v))
        .collect();
    ResolvedPattern::new(ResolvedPatternKind::Record(map), span())
}

fn annotation_var(gt: GlobalType) -> ResolvedAnnotation {
    ResolvedAnnotation::new(ResolvedAnnotationKind::Var(gt), span())
}

fn annotation_alias(gt: GlobalType) -> ResolvedAnnotation {
    ResolvedAnnotation::new(ResolvedAnnotationKind::Alias(gt), span())
}

fn annotation_app(lhs: ResolvedAnnotation, rhs: ResolvedAnnotation) -> ResolvedAnnotation {
    ResolvedAnnotation::new(
        ResolvedAnnotationKind::App(Box::new(lhs), Box::new(rhs)),
        span(),
    )
}

fn annotation_lambda(param: ResolvedAnnotation, ret: ResolvedAnnotation) -> ResolvedAnnotation {
    ResolvedAnnotation::new(
        ResolvedAnnotationKind::Lambda(Box::new(param), Box::new(ret)),
        span(),
    )
}

// Kind tests

#[test]
fn test_kind_star_unification() {
    let mut inf = Inferrer::new();
    let k1 = Rc::new(Kind::Star);
    let k2 = Rc::new(Kind::Star);
    assert!(inf.unify_kinds(&k1, &k2, span()).is_ok());
}

#[test]
fn test_kind_arrow_unification() {
    let mut inf = Inferrer::new();
    let k1 = Rc::new(Kind::Arrow(Rc::new(Kind::Star), Rc::new(Kind::Star)));
    let k2 = Rc::new(Kind::Arrow(Rc::new(Kind::Star), Rc::new(Kind::Star)));
    assert!(inf.unify_kinds(&k1, &k2, span()).is_ok());
}

#[test]
fn test_kind_var_unification() {
    let mut inf = Inferrer::new();
    let kv = inf.new_kind();
    let k = Rc::new(Kind::Star);
    assert!(inf.unify_kinds(&kv, &k, span()).is_ok());
    let applied = inf.apply_kind_subst(&kv);
    assert_eq!(*applied, Kind::Star);
}

#[test]
fn test_kind_mismatch_error() {
    let mut inf = Inferrer::new();
    let k1 = Rc::new(Kind::Star);
    let k2 = Rc::new(Kind::Arrow(Rc::new(Kind::Star), Rc::new(Kind::Star)));
    let result = inf.unify_kinds(&k1, &k2, span());
    assert!(matches!(result, Err(TypeError::KindMismatch(_, _, _))));
}

// Type variable generation tests

#[test]
fn test_new_type_increments() {
    let mut inf = Inferrer::new();
    let t1 = inf.new_type();
    let t2 = inf.new_type();
    let t3 = inf.new_type();
    assert!(matches!(t1, TypeKind::Var(TypeID(0))));
    assert!(matches!(t2, TypeKind::Var(TypeID(1))));
    assert!(matches!(t3, TypeKind::Var(TypeID(2))));
}

#[test]
fn test_new_kind_increments() {
    let mut inf = Inferrer::new();
    let k1 = inf.new_kind();
    let k2 = inf.new_kind();
    assert!(matches!(*k1, Kind::Var(KindID(0))));
    assert!(matches!(*k2, Kind::Var(KindID(1))));
}

// Unification tests

#[test]
fn test_unify_same_type_var() {
    let mut inf = Inferrer::new();
    let tv = make_type_var(0);
    assert!(inf.unify(&tv, &tv, span()).is_ok());
}

#[test]
fn test_unify_different_type_vars() {
    let mut inf = Inferrer::new();
    let tv1 = Type::new(inf.new_type(), Rc::new(Kind::Star));
    let tv2 = Type::new(inf.new_type(), Rc::new(Kind::Star));
    assert!(inf.unify(&tv1, &tv2, span()).is_ok());
    let applied = inf.apply_subst(&tv1);
    let id1 = match &applied.ty {
        TypeKind::Var(id) => *id,
        _ => panic!("expected var"),
    };
    let id2 = match &tv2.ty {
        TypeKind::Var(id) => *id,
        _ => panic!("expected var"),
    };
    assert_eq!(id1, id2);
}

#[test]
fn test_unify_var_with_concrete() {
    let mut inf = Inferrer::new();
    let tv = Type::new(inf.new_type(), Rc::new(Kind::Star));
    let int = make_int();
    assert!(inf.unify(&tv, &int, span()).is_ok());
    let applied = inf.apply_subst(&tv);
    assert!(matches!(applied.ty, TypeKind::Con(_)));
}

#[test]
fn test_unify_concrete_types_match() {
    let mut inf = Inferrer::new();
    let int1 = make_int();
    let int2 = make_int();
    assert!(inf.unify(&int1, &int2, span()).is_ok());
}

#[test]
fn test_unify_concrete_types_mismatch() {
    let mut inf = Inferrer::new();
    let int = make_int();
    let bool_ty = make_bool();
    let result = inf.unify(&int, &bool_ty, span());
    assert!(matches!(result, Err(TypeError::Mismatch(_, _, _))));
}

#[test]
fn test_unify_function_types() {
    let mut inf = Inferrer::new();
    let f1 = make_function(make_int(), make_bool());
    let f2 = make_function(make_int(), make_bool());
    assert!(inf.unify(&f1, &f2, span()).is_ok());
}

#[test]
fn test_unify_function_types_mismatch() {
    let mut inf = Inferrer::new();
    let f1 = make_function(make_int(), make_bool());
    let f2 = make_function(make_int(), make_string());
    let result = inf.unify(&f1, &f2, span());
    assert!(matches!(result, Err(TypeError::Mismatch(_, _, _))));
}

#[test]
fn test_unify_pair_types() {
    let mut inf = Inferrer::new();
    let p1 = make_pair(make_int(), make_bool());
    let p2 = make_pair(make_int(), make_bool());
    assert!(inf.unify(&p1, &p2, span()).is_ok());
}

#[test]
fn test_unify_record_types() {
    let mut inf = Inferrer::new();
    let r1 = make_record(vec![("x", make_int()), ("y", make_bool())]);
    let r2 = make_record(vec![("x", make_int()), ("y", make_bool())]);
    assert!(inf.unify(&r1, &r2, span()).is_ok());
}

#[test]
fn test_unify_record_field_mismatch() {
    let mut inf = Inferrer::new();
    let r1 = make_record(vec![("x", make_int())]);
    let r2 = make_record(vec![("y", make_int())]);
    let result = inf.unify(&r1, &r2, span());
    assert!(matches!(
        result,
        Err(TypeError::RecordFieldMismatch(_, _, _))
    ));
}

#[test]
fn test_unify_app_types() {
    let mut inf = Inferrer::new();
    let l1 = make_list(make_int());
    let l2 = make_list(make_int());
    assert!(inf.unify(&l1, &l2, span()).is_ok());
}

#[test]
fn test_unify_app_types_mismatch() {
    let mut inf = Inferrer::new();
    let l1 = make_list(make_int());
    let l2 = make_list(make_bool());
    let result = inf.unify(&l1, &l2, span());
    assert!(matches!(result, Err(TypeError::Mismatch(_, _, _))));
}

// Occurs check tests

#[test]
fn test_occurs_simple() {
    let inf = Inferrer::new();
    let tv = make_type_var(0);
    assert!(inf.occurs(TypeID(0), &tv));
}

#[test]
fn test_occurs_not_present() {
    let inf = Inferrer::new();
    let tv = make_type_var(1);
    assert!(!inf.occurs(TypeID(0), &tv));
}

#[test]
fn test_occurs_in_function() {
    let inf = Inferrer::new();
    let tv = make_type_var(0);
    let func = make_function(tv.clone(), make_int());
    assert!(inf.occurs(TypeID(0), &func));
}

#[test]
fn test_occurs_in_pair() {
    let inf = Inferrer::new();
    let tv = make_type_var(0);
    let pair = make_pair(make_int(), tv.clone());
    assert!(inf.occurs(TypeID(0), &pair));
}

#[test]
fn test_occurs_in_nested() {
    let inf = Inferrer::new();
    let tv = make_type_var(0);
    let nested = make_function(make_pair(tv.clone(), make_bool()), make_int());
    assert!(inf.occurs(TypeID(0), &nested));
}

#[test]
fn test_occurs_check_error() {
    let mut inf = Inferrer::new();
    let tv = Type::new(inf.new_type(), Rc::new(Kind::Star));
    let func = make_function(tv.clone(), make_int());
    let result = inf.unify(&tv, &func, span());
    assert!(matches!(result, Err(TypeError::OccursCheck(_, _, _))));
}

// Substitution tests

#[test]
fn test_apply_subst_var() {
    let mut inf = Inferrer::new();
    let tv = Type::new(inf.new_type(), Rc::new(Kind::Star));
    let int = make_int();
    inf.unify(&tv, &int, span()).unwrap();
    let applied = inf.apply_subst(&tv);
    assert!(matches!(applied.ty, TypeKind::Con(_)));
}

#[test]
fn test_apply_subst_unbound_var() {
    let inf = Inferrer::new();
    let tv = make_type_var(5);
    let applied = inf.apply_subst(&tv);
    assert!(matches!(applied.ty, TypeKind::Var(TypeID(5))));
}

#[test]
fn test_apply_subst_function() {
    let mut inf = Inferrer::new();
    let tv = Type::new(inf.new_type(), Rc::new(Kind::Star));
    let int = make_int();
    let func = make_function(tv.clone(), make_bool());
    inf.unify(&tv, &int, span()).unwrap();
    let applied = inf.apply_subst(&func);
    if let TypeKind::Function(arg, _) = &applied.ty {
        assert!(matches!(arg.ty, TypeKind::Con(_)));
    } else {
        panic!("expected function");
    }
}

#[test]
fn test_apply_subst_nested() {
    let mut inf = Inferrer::new();
    let tv = Type::new(inf.new_type(), Rc::new(Kind::Star));
    let int = make_int();
    let nested = make_pair(make_function(tv.clone(), make_bool()), tv.clone());
    inf.unify(&tv, &int, span()).unwrap();
    let applied = inf.apply_subst(&nested);
    if let TypeKind::Pair(a, b) = &applied.ty {
        if let TypeKind::Function(arg, _) = &a.ty {
            assert!(matches!(arg.ty, TypeKind::Con(_)));
        }
        assert!(matches!(b.ty, TypeKind::Con(_)));
    } else {
        panic!("expected pair");
    }
}

#[test]
fn test_apply_subst_chain() {
    let mut inf = Inferrer::new();
    let tv1 = Type::new(inf.new_type(), Rc::new(Kind::Star));
    let tv2 = Type::new(inf.new_type(), Rc::new(Kind::Star));
    let int = make_int();
    inf.unify(&tv1, &tv2, span()).unwrap();
    inf.unify(&tv2, &int, span()).unwrap();
    let applied = inf.apply_subst(&tv1);
    assert!(matches!(applied.ty, TypeKind::Con(_)));
}

// Instantiation tests

#[test]
fn test_instantiate_monomorphic() {
    let mut inf = Inferrer::new();
    let scheme = make_scheme(vec![], make_int());
    let instantiated = inf.instantiate(&scheme);
    assert!(matches!(instantiated.ty, TypeKind::Con(_)));
}

#[test]
fn test_instantiate_polymorphic() {
    let mut inf = Inferrer::new();
    let tv = make_type_var(0);
    let scheme = make_scheme(
        vec![(0, Rc::new(Kind::Star))],
        make_function(tv.clone(), tv),
    );
    let instantiated = inf.instantiate(&scheme);
    if let TypeKind::Function(arg, ret) = &instantiated.ty {
        assert!(matches!(arg.ty, TypeKind::Var(_)));
        assert!(matches!(ret.ty, TypeKind::Var(_)));
        if let (TypeKind::Var(id1), TypeKind::Var(id2)) = (&arg.ty, &ret.ty) {
            assert_eq!(id1, id2);
        }
    } else {
        panic!("expected function");
    }
}

#[test]
fn test_instantiate_multiple_vars() {
    let mut inf = Inferrer::new();
    let tv1 = make_type_var(0);
    let tv2 = make_type_var(1);
    let scheme = make_scheme(
        vec![(0, Rc::new(Kind::Star)), (1, Rc::new(Kind::Star))],
        make_function(tv1, tv2),
    );
    let instantiated = inf.instantiate(&scheme);
    if let TypeKind::Function(arg, ret) = &instantiated.ty {
        if let (TypeKind::Var(id1), TypeKind::Var(id2)) = (&arg.ty, &ret.ty) {
            assert_ne!(id1, id2);
        }
    } else {
        panic!("expected function");
    }
}

#[test]
fn test_instantiate_tracking() {
    let mut inf = Inferrer::new();
    let tv = make_type_var(0);
    let scheme = make_scheme(vec![(0, Rc::new(Kind::Star))], tv);
    let (_, fresh_vars) = inf.instantiate_tracking(&scheme);
    assert_eq!(fresh_vars.len(), 1);
}

// Generalization tests

#[test]
fn test_generalize_no_free_vars() {
    let inf = Inferrer::new();
    let env = Environment::new();
    let int = make_int();
    let scheme = inf.generalize(&env, &int);
    assert!(scheme.vars.is_empty());
}

#[test]
fn test_generalize_with_free_vars() {
    let inf = Inferrer::new();
    let env = Environment::new();
    let tv = make_type_var(0);
    let scheme = inf.generalize(&env, &tv);
    assert_eq!(scheme.vars.len(), 1);
}

#[test]
fn test_generalize_respects_env() {
    let inf = Inferrer::new();
    let mut env = Environment::new();
    let tv = make_type_var(0);
    env.insert(
        global_name(0),
        TypeScheme {
            vars: vec![],
            ty: tv.clone(),
        },
    );
    let scheme = inf.generalize(&env, &tv);
    assert!(scheme.vars.is_empty());
}

#[test]
fn test_generalize_multiple_vars() {
    let inf = Inferrer::new();
    let env = Environment::new();
    let tv1 = make_type_var(0);
    let tv2 = make_type_var(1);
    let func = make_function(tv1, tv2);
    let scheme = inf.generalize(&env, &func);
    assert_eq!(scheme.vars.len(), 2);
}

// Free variable extraction tests

#[test]
fn test_free_in_type_var() {
    let inf = Inferrer::new();
    let tv = make_type_var(0);
    let free = inf.free_in_type(&tv);
    assert!(free.contains_key(&TypeID(0)));
}

#[test]
fn test_free_in_concrete() {
    let inf = Inferrer::new();
    let int = make_int();
    let free = inf.free_in_type(&int);
    assert!(free.is_empty());
}

#[test]
fn test_free_in_function() {
    let inf = Inferrer::new();
    let tv1 = make_type_var(0);
    let tv2 = make_type_var(1);
    let func = make_function(tv1, tv2);
    let free = inf.free_in_type(&func);
    assert_eq!(free.len(), 2);
    assert!(free.contains_key(&TypeID(0)));
    assert!(free.contains_key(&TypeID(1)));
}

#[test]
fn test_free_in_scheme() {
    let inf = Inferrer::new();
    let tv1 = make_type_var(0);
    let tv2 = make_type_var(1);
    let func = make_function(tv1, tv2);
    let scheme = TypeScheme {
        vars: vec![(TypeID(0), Rc::new(Kind::Star))],
        ty: func,
    };
    let free = inf.free_in_scheme(&scheme);
    assert_eq!(free.len(), 1);
    assert!(free.contains_key(&TypeID(1)));
    assert!(!free.contains_key(&TypeID(0)));
}

// Pattern inference tests

#[test]
fn test_infer_pattern_var() {
    let mut inf = Inferrer::new();
    let mut env = Environment::new();
    let pat = pattern_var(global_name(0));
    let typed = inf.infer_pattern(pat, &mut env).unwrap();
    assert!(matches!(typed.ty.ty, TypeKind::Var(_)));
    assert!(env.contains_key(&global_name(0)));
}

#[test]
fn test_infer_pattern_wildcard() {
    let mut inf = Inferrer::new();
    let mut env = Environment::new();
    let pat = pattern_wildcard();
    let typed = inf.infer_pattern(pat, &mut env).unwrap();
    assert!(matches!(typed.ty.ty, TypeKind::Var(_)));
}

#[test]
fn test_infer_pattern_unit() {
    let mut inf = Inferrer::new();
    let mut env = Environment::new();
    let pat = pattern_unit();
    let typed = inf.infer_pattern(pat, &mut env).unwrap();
    if let TypeKind::Con(gt) = &typed.ty.ty {
        assert_eq!(gt.name, UNIT_TYPE);
    } else {
        panic!("expected unit type");
    }
}

#[test]
fn test_infer_pattern_pair() {
    let mut inf = Inferrer::new();
    let mut env = Environment::new();
    let pat = pattern_pair(pattern_var(global_name(0)), pattern_var(global_name(1)));
    let typed = inf.infer_pattern(pat, &mut env).unwrap();
    assert!(matches!(typed.ty.ty, TypeKind::Pair(_, _)));
}

#[test]
fn test_infer_pattern_empty_list() {
    let mut inf = Inferrer::new();
    let mut env = Environment::new();
    let pat = pattern_empty_list();
    let typed = inf.infer_pattern(pat, &mut env).unwrap();
    assert!(matches!(typed.ty.ty, TypeKind::App(_, _)));
}

#[test]
fn test_infer_pattern_cons() {
    let mut inf = Inferrer::new();
    let mut env = Environment::new();
    let pat = pattern_cons(pattern_var(global_name(0)), pattern_var(global_name(1)));
    let typed = inf.infer_pattern(pat, &mut env).unwrap();
    assert!(matches!(typed.ty.ty, TypeKind::App(_, _)));
}

#[test]
fn test_infer_pattern_record() {
    let mut inf = Inferrer::new();
    let mut env = Environment::new();
    let pat = pattern_record(vec![("x", pattern_var(global_name(0)))]);
    let typed = inf.infer_pattern(pat, &mut env).unwrap();
    assert!(matches!(typed.ty.ty, TypeKind::Record(_)));
}

// Expression inference tests

#[test]
fn test_infer_int_lit() {
    let mut inf = Inferrer::new();
    let expr = resolved_int(42);
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::Con(gt) = &typed.ty.ty {
        assert_eq!(gt.name, INT_TYPE);
    } else {
        panic!("expected int type");
    }
}

#[test]
fn test_infer_float_lit() {
    let mut inf = Inferrer::new();
    let expr = resolved_float(3.14);
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::Con(gt) = &typed.ty.ty {
        assert_eq!(gt.name, FLOAT_TYPE);
    } else {
        panic!("expected float type");
    }
}

#[test]
fn test_infer_bool_lit() {
    let mut inf = Inferrer::new();
    let expr = resolved_bool(true);
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::Con(gt) = &typed.ty.ty {
        assert_eq!(gt.name, BOOL_TYPE);
    } else {
        panic!("expected bool type");
    }
}

#[test]
fn test_infer_string_lit() {
    let mut inf = Inferrer::new();
    let expr = resolved_string("hello");
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::Con(gt) = &typed.ty.ty {
        assert_eq!(gt.name, STRING_TYPE);
    } else {
        panic!("expected string type");
    }
}

#[test]
fn test_infer_unit_lit() {
    let mut inf = Inferrer::new();
    let expr = resolved_unit();
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::Con(gt) = &typed.ty.ty {
        assert_eq!(gt.name, UNIT_TYPE);
    } else {
        panic!("expected unit type");
    }
}

#[test]
fn test_infer_pair_lit() {
    let mut inf = Inferrer::new();
    let expr = resolved_pair(resolved_int(1), resolved_bool(true));
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::Pair(a, b) = &typed.ty.ty {
        if let TypeKind::Con(gt) = &a.ty {
            assert_eq!(gt.name, INT_TYPE);
        }
        if let TypeKind::Con(gt) = &b.ty {
            assert_eq!(gt.name, BOOL_TYPE);
        }
    } else {
        panic!("expected pair type");
    }
}

#[test]
fn test_infer_empty_list() {
    let mut inf = Inferrer::new();
    let expr = resolved_empty_list();
    let typed = inf.infer(expr).unwrap();
    assert!(matches!(typed.ty.ty, TypeKind::App(_, _)));
}

#[test]
fn test_infer_cons() {
    let mut inf = Inferrer::new();
    let expr = resolved_cons(resolved_int(1), resolved_empty_list());
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::App(con, elem) = &typed.ty.ty {
        if let TypeKind::Con(gt) = &con.ty {
            assert_eq!(gt.name, LIST_TYPE);
        }
        if let TypeKind::Con(gt) = &elem.ty {
            assert_eq!(gt.name, INT_TYPE);
        }
    } else {
        panic!("expected list type");
    }
}

#[test]
fn test_infer_lambda() {
    let mut inf = Inferrer::new();
    let param = pattern_var(global_name(0));
    let body = resolved_var(global_name(0));
    let expr = resolved_lambda(param, body);
    let typed = inf.infer(expr).unwrap();
    assert!(matches!(typed.ty.ty, TypeKind::Function(_, _)));
}

#[test]
fn test_infer_lambda_with_body() {
    let mut inf = Inferrer::new();
    let param = pattern_var(global_name(0));
    let body = resolved_int(42);
    let expr = resolved_lambda(param, body);
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::Function(_, ret) = &typed.ty.ty {
        if let TypeKind::Con(gt) = &ret.ty {
            assert_eq!(gt.name, INT_TYPE);
        }
    } else {
        panic!("expected function type");
    }
}

#[test]
fn test_infer_if_expression() {
    let mut inf = Inferrer::new();
    let cond = resolved_bool(true);
    let then_expr = resolved_int(1);
    let else_expr = resolved_int(2);
    let expr = resolved_if(cond, then_expr, else_expr);
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::Con(gt) = &typed.ty.ty {
        assert_eq!(gt.name, INT_TYPE);
    } else {
        panic!("expected int type");
    }
}

#[test]
fn test_infer_record_lit() {
    let mut inf = Inferrer::new();
    let expr = resolved_record(vec![("x", resolved_int(1)), ("y", resolved_bool(true))]);
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::Record(fields) = &typed.ty.ty {
        assert_eq!(fields.len(), 2);
        assert!(fields.contains_key("x"));
        assert!(fields.contains_key("y"));
    } else {
        panic!("expected record type");
    }
}

#[test]
fn test_infer_field_access() {
    let mut inf = Inferrer::new();
    let record = resolved_record(vec![("x", resolved_int(1))]);
    let expr = resolved_field_access(record, "x");
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::Con(gt) = &typed.ty.ty {
        assert_eq!(gt.name, INT_TYPE);
    } else {
        panic!("expected int type");
    }
}

#[test]
fn test_infer_block_simple() {
    let mut inf = Inferrer::new();
    let expr = resolved_block(vec![], Some(resolved_int(42)));
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::Con(gt) = &typed.ty.ty {
        assert_eq!(gt.name, INT_TYPE);
    } else {
        panic!("expected int type");
    }
}

#[test]
fn test_infer_block_with_binding() {
    let mut inf = Inferrer::new();
    let stmt = ResolvedStatement {
        pattern: pattern_var(global_name(0)),
        value: Box::new(resolved_int(1)),
        value_type: None,
        type_params: vec![],
        span: span(),
    };
    let expr = resolved_block(vec![stmt], Some(resolved_var(global_name(0))));
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::Con(gt) = &typed.ty.ty {
        assert_eq!(gt.name, INT_TYPE);
    } else {
        panic!("expected int type");
    }
}

// Error case tests

#[test]
fn test_error_type_mismatch() {
    let mut inf = Inferrer::new();
    let cond = resolved_bool(true);
    let then_expr = resolved_int(1);
    let else_expr = resolved_bool(false);
    let expr = resolved_if(cond, then_expr, else_expr);
    let result = inf.infer(expr);
    assert!(matches!(result, Err(TypeError::Mismatch(_, _, _))));
}

#[test]
fn test_error_if_condition_not_bool() {
    let mut inf = Inferrer::new();
    let cond = resolved_int(1);
    let then_expr = resolved_int(2);
    let else_expr = resolved_int(3);
    let expr = resolved_if(cond, then_expr, else_expr);
    let result = inf.infer(expr);
    assert!(matches!(result, Err(TypeError::Mismatch(_, _, _))));
}

#[test]
fn test_error_unbound_variable() {
    let mut inf = Inferrer::new();
    let expr = resolved_var(global_name(999));
    let result = inf.infer(expr);
    assert!(matches!(result, Err(TypeError::UnboundVariable(_, _))));
}

#[test]
fn test_error_field_access_non_record() {
    let mut inf = Inferrer::new();
    let expr = resolved_field_access(resolved_int(1), "x");
    let result = inf.infer(expr);
    assert!(matches!(
        result,
        Err(TypeError::FieldAccessOnNonRecord(_, _))
    ));
}

#[test]
fn test_error_record_field_mismatch_in_unify() {
    let mut inf = Inferrer::new();
    let stmt = ResolvedStatement {
        pattern: pattern_record(vec![("x", pattern_var(global_name(0)))]),
        value: Box::new(resolved_record(vec![("y", resolved_int(1))])),
        value_type: None,
        type_params: vec![],
        span: span(),
    };
    let expr = resolved_block(vec![stmt], Some(resolved_unit()));
    let result = inf.infer(expr);
    assert!(matches!(
        result,
        Err(TypeError::RecordFieldMismatch(_, _, _))
    ));
}

// Type alias tests

#[test]
fn test_register_alias() {
    let mut inf = Inferrer::new();
    let alias = ResolvedTypeAlias {
        name: global_type(100),
        type_params: vec![],
        body: annotation_var(GlobalType {
            krate: None,
            name: INT_TYPE,
        }),
    };
    assert!(inf.register_alias(alias).is_ok());
}

#[test]
fn test_alias_expansion_zero_args() {
    let mut inf = Inferrer::new();
    let alias = ResolvedTypeAlias {
        name: global_type(100),
        type_params: vec![],
        body: annotation_var(GlobalType {
            krate: None,
            name: INT_TYPE,
        }),
    };
    inf.register_alias(alias).unwrap();
    let annot = annotation_alias(global_type(100));
    let ty = inf.instantiate_annotation(&annot).unwrap();
    if let TypeKind::Con(gt) = &ty.ty {
        assert_eq!(gt.name, INT_TYPE);
    } else {
        panic!("expected int type");
    }
}

#[test]
fn test_alias_with_type_params() {
    let mut inf = Inferrer::new();
    let alias = ResolvedTypeAlias {
        name: global_type(100),
        type_params: vec![global_type(200)],
        body: annotation_var(global_type(200)),
    };
    inf.register_alias(alias).unwrap();
    let annot = annotation_alias(global_type(100));
    let ty = inf.instantiate_annotation(&annot).unwrap();
    assert!(matches!(ty.ty, TypeKind::AliasHead(_, _)));
}

#[test]
fn test_alias_full_application() {
    let mut inf = Inferrer::new();
    let alias = ResolvedTypeAlias {
        name: global_type(100),
        type_params: vec![global_type(200)],
        body: annotation_var(global_type(200)),
    };
    inf.register_alias(alias).unwrap();
    let annot = annotation_app(
        annotation_alias(global_type(100)),
        annotation_var(GlobalType {
            krate: None,
            name: INT_TYPE,
        }),
    );
    let ty = inf.instantiate_annotation(&annot).unwrap();
    if let TypeKind::Con(gt) = &ty.ty {
        assert_eq!(gt.name, INT_TYPE);
    } else {
        panic!("expected int type after full alias application");
    }
}

#[test]
fn test_alias_cycle_detection() {
    let mut inf = Inferrer::new();
    let alias = ResolvedTypeAlias {
        name: global_type(100),
        type_params: vec![],
        body: annotation_alias(global_type(100)),
    };
    inf.register_alias(alias).unwrap();
    let annot = annotation_alias(global_type(100));
    let result = inf.instantiate_annotation(&annot);
    assert!(matches!(result, Err(TypeError::AliasCycle(_, _))));
}

#[test]
fn test_alias_indirect_cycle() {
    let mut inf = Inferrer::new();
    let alias1 = ResolvedTypeAlias {
        name: global_type(100),
        type_params: vec![],
        body: annotation_alias(global_type(101)),
    };
    let alias2 = ResolvedTypeAlias {
        name: global_type(101),
        type_params: vec![],
        body: annotation_alias(global_type(100)),
    };
    inf.register_alias(alias1).unwrap();
    inf.register_alias(alias2).unwrap();
    let annot = annotation_alias(global_type(100));
    let result = inf.instantiate_annotation(&annot);
    assert!(matches!(result, Err(TypeError::AliasCycle(_, _))));
}

// Custom type and scheme tests

#[test]
fn test_register_custom_type() {
    let mut inf = Inferrer::new();
    let scheme = make_scheme(vec![], make_int());
    inf.register_custom_type(global_name(0), scheme.clone());
    let retrieved = inf.get_custom_scheme(&global_name(0));
    assert!(retrieved.is_some());
}

#[test]
fn test_infer_var_from_custom_scheme() {
    let mut inf = Inferrer::new();
    let scheme = make_scheme(vec![], make_int());
    inf.register_custom_type(global_name(0), scheme);
    let env: Environment = [(
        global_name(0),
        TypeScheme {
            vars: vec![],
            ty: make_int(),
        },
    )]
    .into_iter()
    .collect();
    let expr = resolved_var(global_name(0));
    let typed = inf.infer_type(&env, expr).unwrap();
    if let TypeKind::Con(gt) = &typed.ty.ty {
        assert_eq!(gt.name, INT_TYPE);
    } else {
        panic!("expected int type");
    }
}

#[test]
fn test_infer_polymorphic_var() {
    let mut inf = Inferrer::new();
    let tv = make_type_var(0);
    let scheme = make_scheme(
        vec![(0, Rc::new(Kind::Star))],
        make_function(tv.clone(), tv),
    );
    let env: Environment = [(global_name(0), scheme)].into_iter().collect();
    let expr = resolved_var(global_name(0));
    let typed = inf.infer_type(&env, expr).unwrap();
    assert!(matches!(typed.ty.ty, TypeKind::Function(_, _)));
}

// Annotation tests

#[test]
fn test_instantiate_annotation_var() {
    let mut inf = Inferrer::new();
    let annot = annotation_var(GlobalType {
        krate: None,
        name: INT_TYPE,
    });
    let ty = inf.instantiate_annotation(&annot).unwrap();
    if let TypeKind::Con(gt) = &ty.ty {
        assert_eq!(gt.name, INT_TYPE);
    } else {
        panic!("expected int type");
    }
}

#[test]
fn test_instantiate_annotation_lambda() {
    let mut inf = Inferrer::new();
    let annot = annotation_lambda(
        annotation_var(GlobalType {
            krate: None,
            name: INT_TYPE,
        }),
        annotation_var(GlobalType {
            krate: None,
            name: BOOL_TYPE,
        }),
    );
    let ty = inf.instantiate_annotation(&annot).unwrap();
    if let TypeKind::Function(arg, ret) = &ty.ty {
        if let TypeKind::Con(gt) = &arg.ty {
            assert_eq!(gt.name, INT_TYPE);
        }
        if let TypeKind::Con(gt) = &ret.ty {
            assert_eq!(gt.name, BOOL_TYPE);
        }
    } else {
        panic!("expected function type");
    }
}

#[test]
fn test_instantiate_annotation_app() {
    let mut inf = Inferrer::new();
    let annot = annotation_app(
        annotation_var(GlobalType {
            krate: None,
            name: LIST_TYPE,
        }),
        annotation_var(GlobalType {
            krate: None,
            name: INT_TYPE,
        }),
    );
    let ty = inf.instantiate_annotation(&annot).unwrap();
    assert!(matches!(ty.ty, TypeKind::App(_, _)));
}

// Additional edge case tests

#[test]
fn test_unify_record_types_with_vars() {
    let mut inf = Inferrer::new();
    let tv = Type::new(inf.new_type(), Rc::new(Kind::Star));
    let r1 = make_record(vec![("x", tv.clone())]);
    let r2 = make_record(vec![("x", make_int())]);
    assert!(inf.unify(&r1, &r2, span()).is_ok());
    let applied = inf.apply_subst(&tv);
    assert!(matches!(applied.ty, TypeKind::Con(_)));
}

#[test]
fn test_infer_nested_pairs() {
    let mut inf = Inferrer::new();
    let inner = resolved_pair(resolved_int(1), resolved_bool(true));
    let outer = resolved_pair(inner, resolved_string("hello"));
    let typed = inf.infer(outer).unwrap();
    if let TypeKind::Pair(a, b) = &typed.ty.ty {
        assert!(matches!(a.ty, TypeKind::Pair(_, _)));
        if let TypeKind::Con(gt) = &b.ty {
            assert_eq!(gt.name, STRING_TYPE);
        }
    } else {
        panic!("expected pair type");
    }
}

#[test]
fn test_infer_nested_lambdas() {
    let mut inf = Inferrer::new();
    let inner_lambda = resolved_lambda(pattern_var(global_name(1)), resolved_var(global_name(1)));
    let outer_lambda = resolved_lambda(pattern_var(global_name(0)), inner_lambda);
    let typed = inf.infer(outer_lambda).unwrap();
    if let TypeKind::Function(_, ret) = &typed.ty.ty {
        assert!(matches!(ret.ty, TypeKind::Function(_, _)));
    } else {
        panic!("expected function type");
    }
}

#[test]
fn test_infer_application_propagates_types() {
    let mut inf = Inferrer::new();
    let identity = resolved_lambda(pattern_var(global_name(0)), resolved_var(global_name(0)));
    let app = resolved_app(identity, resolved_int(42));
    let typed = inf.infer(app).unwrap();
    if let TypeKind::Con(gt) = &typed.ty.ty {
        assert_eq!(gt.name, INT_TYPE);
    } else {
        panic!("expected int type");
    }
}

#[test]
fn test_infer_cons_list_of_lists() {
    let mut inf = Inferrer::new();
    let inner_list = resolved_cons(resolved_int(1), resolved_empty_list());
    let outer = resolved_cons(inner_list, resolved_empty_list());
    let typed = inf.infer(outer).unwrap();
    if let TypeKind::App(con, elem) = &typed.ty.ty {
        if let TypeKind::Con(gt) = &con.ty {
            assert_eq!(gt.name, LIST_TYPE);
        }
        assert!(matches!(elem.ty, TypeKind::App(_, _)));
    } else {
        panic!("expected list type");
    }
}

#[test]
fn test_generalize_preserves_concrete_parts() {
    let inf = Inferrer::new();
    let env = Environment::new();
    let tv = make_type_var(0);
    let func = make_function(make_int(), tv);
    let scheme = inf.generalize(&env, &func);
    assert_eq!(scheme.vars.len(), 1);
    if let TypeKind::Function(arg, _) = &scheme.ty.ty {
        assert!(matches!(arg.ty, TypeKind::Con(_)));
    }
}

#[test]
fn test_block_empty_returns_unit() {
    let mut inf = Inferrer::new();
    let expr = resolved_block(vec![], None);
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::Con(gt) = &typed.ty.ty {
        assert_eq!(gt.name, UNIT_TYPE);
    } else {
        panic!("expected unit type");
    }
}

#[test]
fn test_multiple_bindings_in_block() {
    let mut inf = Inferrer::new();
    let stmt1 = ResolvedStatement {
        pattern: pattern_var(global_name(0)),
        value: Box::new(resolved_int(1)),
        value_type: None,
        type_params: vec![],
        span: span(),
    };
    let stmt2 = ResolvedStatement {
        pattern: pattern_var(global_name(1)),
        value: Box::new(resolved_bool(true)),
        value_type: None,
        type_params: vec![],
        span: span(),
    };
    let result = resolved_pair(resolved_var(global_name(0)), resolved_var(global_name(1)));
    let expr = resolved_block(vec![stmt1, stmt2], Some(result));
    let typed = inf.infer(expr).unwrap();
    if let TypeKind::Pair(a, b) = &typed.ty.ty {
        if let TypeKind::Con(gt) = &a.ty {
            assert_eq!(gt.name, INT_TYPE);
        }
        if let TypeKind::Con(gt) = &b.ty {
            assert_eq!(gt.name, BOOL_TYPE);
        }
    } else {
        panic!("expected pair type");
    }
}
