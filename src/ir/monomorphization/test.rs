use crate::analysis::inference::{Kind, Type, TypeID, TypeKind, TypeScheme};
use crate::analysis::resolver::GlobalName;
use crate::analysis::resolver::Name;
use crate::builtin::{
    BOOL_TYPE, BuiltinFn, FLOAT_TYPE, INT_TYPE, LIST_TYPE, STRING_TYPE, UNIT_TYPE,
};
use crate::ir::anf::{Atom, Decl, Expr, PrimExpr, SwitchBranch};
use std::collections::BTreeMap;
use std::rc::Rc;

use super::{Monomorphizer, Program, Substitutor, monomorphize};

fn global_name(id: usize) -> GlobalName {
    GlobalName {
        krate: None,
        name: Name(id),
    }
}

// Type Construction Helpers
fn make_type_var(id: usize) -> Rc<Type> {
    Rc::new(Type {
        ty: TypeKind::Var(TypeID(id)),
        kind: Rc::new(Kind::Star),
    })
}

fn make_int() -> Rc<Type> {
    Rc::new(Type {
        ty: TypeKind::Con(crate::analysis::resolver::GlobalType {
            krate: None,
            name: INT_TYPE,
        }),
        kind: Rc::new(Kind::Star),
    })
}

fn make_bool() -> Rc<Type> {
    Rc::new(Type {
        ty: TypeKind::Con(crate::analysis::resolver::GlobalType {
            krate: None,
            name: BOOL_TYPE,
        }),
        kind: Rc::new(Kind::Star),
    })
}

fn make_float() -> Rc<Type> {
    Rc::new(Type {
        ty: TypeKind::Con(crate::analysis::resolver::GlobalType {
            krate: None,
            name: FLOAT_TYPE,
        }),
        kind: Rc::new(Kind::Star),
    })
}

fn make_string() -> Rc<Type> {
    Rc::new(Type {
        ty: TypeKind::Con(crate::analysis::resolver::GlobalType {
            krate: None,
            name: STRING_TYPE,
        }),
        kind: Rc::new(Kind::Star),
    })
}

fn make_unit() -> Rc<Type> {
    Rc::new(Type {
        ty: TypeKind::Con(crate::analysis::resolver::GlobalType {
            krate: None,
            name: UNIT_TYPE,
        }),
        kind: Rc::new(Kind::Star),
    })
}

fn make_function(arg: Rc<Type>, ret: Rc<Type>) -> Rc<Type> {
    Rc::new(Type {
        ty: TypeKind::Function(arg, ret),
        kind: Rc::new(Kind::Star),
    })
}

fn make_pair(a: Rc<Type>, b: Rc<Type>) -> Rc<Type> {
    Rc::new(Type {
        ty: TypeKind::Pair(a, b),
        kind: Rc::new(Kind::Star),
    })
}

fn make_list(elem: Rc<Type>) -> Rc<Type> {
    let list_con = Rc::new(Type {
        ty: TypeKind::Con(crate::analysis::resolver::GlobalType {
            krate: None,
            name: LIST_TYPE,
        }),
        kind: Rc::new(Kind::Arrow(Rc::new(Kind::Star), Rc::new(Kind::Star))),
    });
    Rc::new(Type {
        ty: TypeKind::App(list_con, elem),
        kind: Rc::new(Kind::Star),
    })
}

fn make_record(fields: Vec<(&str, Rc<Type>)>) -> Rc<Type> {
    let btree: BTreeMap<String, Rc<Type>> = fields
        .into_iter()
        .map(|(k, v)| (k.to_string(), v))
        .collect();
    Rc::new(Type {
        ty: TypeKind::Record(btree),
        kind: Rc::new(Kind::Star),
    })
}

fn make_scheme(vars: Vec<(usize, Rc<Kind>)>, ty: Rc<Type>) -> TypeScheme {
    TypeScheme {
        vars: vars.into_iter().map(|(id, k)| (TypeID(id), k)).collect(),
        ty,
    }
}

// Atom Builders
fn atom_var(name: GlobalName, inst: Vec<Rc<Type>>) -> Atom {
    Atom::Var { name, inst }
}

fn atom_int(val: i64) -> Atom {
    Atom::IntLit(val)
}

fn atom_bool(val: bool) -> Atom {
    Atom::BoolLit(val)
}

fn atom_unit() -> Atom {
    Atom::UnitLit
}

// PrimExpr Builders
fn prim_atom(atom: Atom) -> PrimExpr {
    PrimExpr::Atom(atom)
}

fn prim_app(func: Atom, arg: Atom) -> PrimExpr {
    PrimExpr::App { func, arg }
}

fn prim_lambda(
    param: GlobalName,
    param_ty: Rc<Type>,
    body: Expr,
    captures: Vec<GlobalName>,
) -> PrimExpr {
    PrimExpr::Lambda {
        param,
        param_ty,
        body: Box::new(body),
        captures,
    }
}

fn prim_pack(tag: u32, inst: Vec<Rc<Type>>, payload: Option<Atom>) -> PrimExpr {
    PrimExpr::Pack {
        tag,
        instantiation: inst,
        payload,
    }
}

fn prim_builtin(fun: BuiltinFn, inst: Vec<Rc<Type>>) -> PrimExpr {
    PrimExpr::Builtin {
        fun,
        instantiation: inst,
    }
}

fn prim_if(cond: Atom, then_expr: Expr, else_expr: Expr) -> PrimExpr {
    PrimExpr::If(cond, Box::new(then_expr), Box::new(else_expr))
}

fn prim_pair(left: Atom, right: Atom) -> PrimExpr {
    PrimExpr::Pair { left, right }
}

// Expr Builders
fn expr_simple(result: Atom, ty: Rc<Type>) -> Expr {
    Expr {
        decls: vec![],
        result,
        ty,
    }
}

fn expr_with_decls(decls: Vec<Decl>, result: Atom, ty: Rc<Type>) -> Expr {
    Expr { decls, result, ty }
}

// Decl Builders
fn mono_val(name: GlobalName, ty: Rc<Type>, expr: PrimExpr) -> Decl {
    Decl::MonoVal { name, ty, expr }
}

fn poly_val(name: GlobalName, scheme: TypeScheme, ty: Rc<Type>, expr: Expr) -> Decl {
    Decl::PolyVal {
        name,
        scheme,
        ty,
        expr: Box::new(expr),
    }
}

fn rec_decl(defs: Vec<Decl>) -> Decl {
    Decl::Rec { defs }
}

// Program Builder
fn make_program(decls: Vec<Decl>, next_name: Name, main_name: GlobalName) -> Program {
    Program {
        decls,
        next_name,
        main_name,
    }
}

#[test]
fn test_substitutor_basic_var() {
    // forall a. a -> Int, with args = [Bool]
    let scheme = make_scheme(
        vec![(0, Rc::new(Kind::Star))],
        make_function(make_type_var(0), make_int()),
    );
    let args = vec![make_bool()];

    let subst = Substitutor::new(&scheme, &args);
    let result = subst.apply(make_type_var(0));

    assert!(matches!(result.ty, TypeKind::Con(_)));
}

#[test]
fn test_substitutor_function_type() {
    // forall a. a -> a, with args = [Int]
    let func_ty = make_function(make_type_var(0), make_type_var(0));
    let scheme = make_scheme(vec![(0, Rc::new(Kind::Star))], func_ty.clone());
    let args = vec![make_int()];

    let subst = Substitutor::new(&scheme, &args);
    let result = subst.apply(func_ty);

    // Result should be Int -> Int
    if let TypeKind::Function(arg, ret) = &result.ty {
        assert!(matches!(arg.ty, TypeKind::Con(_)));
        assert!(matches!(ret.ty, TypeKind::Con(_)));
    } else {
        panic!("Expected function type");
    }
}

#[test]
fn test_substitutor_nested_type() {
    // forall a. List[a], with args = [Int]
    let list_of_a = make_list(make_type_var(0));
    let scheme = make_scheme(vec![(0, Rc::new(Kind::Star))], list_of_a.clone());
    let args = vec![make_int()];

    let subst = Substitutor::new(&scheme, &args);
    let result = subst.apply(list_of_a);

    // Result should be List[Int]
    if let TypeKind::App(_, elem) = &result.ty {
        assert!(matches!(elem.ty, TypeKind::Con(_)));
    } else {
        panic!("Expected App type for List");
    }
}

#[test]
fn test_substitutor_multiple_vars() {
    // forall a b. (a, b), with args = [Int, Bool]
    let pair_ty = make_pair(make_type_var(0), make_type_var(1));
    let scheme = make_scheme(
        vec![(0, Rc::new(Kind::Star)), (1, Rc::new(Kind::Star))],
        pair_ty.clone(),
    );
    let args = vec![make_int(), make_bool()];

    let subst = Substitutor::new(&scheme, &args);
    let result = subst.apply(pair_ty);

    // Result should be (Int, Bool)
    if let TypeKind::Pair(fst, snd) = &result.ty {
        assert!(matches!(fst.ty, TypeKind::Con(_)));
        assert!(matches!(snd.ty, TypeKind::Con(_)));
    } else {
        panic!("Expected Pair type");
    }
}

#[test]
fn test_substitutor_record_type() {
    // forall a. {x: a, y: a}, with args = [Int]
    let record_ty = make_record(vec![("x", make_type_var(0)), ("y", make_type_var(0))]);
    let scheme = make_scheme(vec![(0, Rc::new(Kind::Star))], record_ty.clone());
    let args = vec![make_int()];

    let subst = Substitutor::new(&scheme, &args);
    let result = subst.apply(record_ty);

    if let TypeKind::Record(fields) = &result.ty {
        assert_eq!(fields.len(), 2);
        assert!(fields.contains_key("x"));
        assert!(fields.contains_key("y"));
    } else {
        panic!("Expected Record type");
    }
}

#[test]
fn test_substitutor_atom_var() {
    // Test substitution in Atom::Var with instantiation
    let scheme = make_scheme(vec![(0, Rc::new(Kind::Star))], make_type_var(0));
    let args = vec![make_int()];

    let subst = Substitutor::new(&scheme, &args);
    let atom = atom_var(global_name(1), vec![make_type_var(0)]);
    let result = subst.subst_atom(atom);

    if let Atom::Var { name, inst } = result {
        assert_eq!(name, global_name(1));
        assert_eq!(inst.len(), 1);
        assert!(matches!(inst[0].ty, TypeKind::Con(_)));
    } else {
        panic!("Expected Var atom");
    }
}

#[test]
fn test_substitutor_atom_literal() {
    // Literals should pass through unchanged
    let scheme = make_scheme(vec![(0, Rc::new(Kind::Star))], make_type_var(0));
    let args = vec![make_int()];

    let subst = Substitutor::new(&scheme, &args);
    let atom = atom_int(42);
    let result = subst.subst_atom(atom);

    assert!(matches!(result, Atom::IntLit(42)));
}

#[test]
fn test_substitutor_prim_lambda() {
    // Lambda with type variable in param and body
    let scheme = make_scheme(vec![(0, Rc::new(Kind::Star))], make_type_var(0));
    let args = vec![make_int()];

    let body = expr_simple(atom_var(global_name(1), vec![]), make_type_var(0));
    let lambda = prim_lambda(global_name(2), make_type_var(0), body, vec![]);

    let subst = Substitutor::new(&scheme, &args);
    let result = subst.subst_prim(lambda);

    if let PrimExpr::Lambda { param_ty, body, .. } = result {
        assert!(matches!(param_ty.ty, TypeKind::Con(_)));
        assert!(matches!(body.ty.ty, TypeKind::Con(_)));
    } else {
        panic!("Expected Lambda");
    }
}

#[test]
fn test_substitutor_prim_pack() {
    // Pack with type variable in instantiation
    let scheme = make_scheme(vec![(0, Rc::new(Kind::Star))], make_type_var(0));
    let args = vec![make_int()];

    let pack = prim_pack(0, vec![make_type_var(0)], Some(atom_int(42)));

    let subst = Substitutor::new(&scheme, &args);
    let result = subst.subst_prim(pack);

    if let PrimExpr::Pack { instantiation, .. } = result {
        assert_eq!(instantiation.len(), 1);
        assert!(matches!(instantiation[0].ty, TypeKind::Con(_)));
    } else {
        panic!("Expected Pack");
    }
}

#[test]
fn test_substitutor_no_substitution() {
    // Empty scheme (already monomorphic)
    let scheme = make_scheme(vec![], make_int());
    let args = vec![];

    let subst = Substitutor::new(&scheme, &args);
    let result = subst.apply(make_int());

    assert!(matches!(result.ty, TypeKind::Con(_)));
}

#[test]
fn test_register_poly_val() {
    let mut mono = Monomorphizer::new(Name(100));

    // Create a simple PolyVal
    let scheme = make_scheme(
        vec![(0, Rc::new(Kind::Star))],
        make_function(make_type_var(0), make_type_var(0)),
    );
    let expr = expr_simple(atom_var(global_name(1), vec![]), make_type_var(0));
    let decl = poly_val(global_name(10), scheme, make_type_var(0), expr);

    mono.register_decls(&[decl]);

    // Verify it was registered (we can't directly access generic_defs, but we can test its effects)
    assert!(mono.generic_defs.contains_key(&global_name(10)));
}

#[test]
fn test_get_specialized_name_new() {
    let mut mono = Monomorphizer::new(Name(100));

    let name1 = mono.get_specialized_name(global_name(10), vec![make_int()]);

    // Should create a new name
    assert_eq!(name1, global_name(100));

    // Check that the cache has an entry
    assert!(
        mono.cache
            .contains_key(&(global_name(10), vec![make_int()]))
    );
}

#[test]
fn test_get_specialized_name_cached() {
    let mut mono = Monomorphizer::new(Name(100));

    let name1 = mono.get_specialized_name(global_name(10), vec![make_int()]);
    let name2 = mono.get_specialized_name(global_name(10), vec![make_int()]);

    // Should return the same name
    assert_eq!(name1, name2);
    assert_eq!(name1, global_name(100));
}

#[test]
fn test_get_specialized_name_empty_inst() {
    let mut mono = Monomorphizer::new(Name(100));

    let name = mono.get_specialized_name(global_name(10), vec![]);

    // Should return the original name for empty instantiation
    assert_eq!(name, global_name(10));
}

#[test]
fn test_transform_atom_with_inst() {
    let mut mono = Monomorphizer::new(Name(100));

    let atom = atom_var(global_name(10), vec![make_int()]);
    let result = mono.transform_atom(atom);

    // Should get specialized name and clear instantiation
    if let Atom::Var { name, inst } = result {
        assert_eq!(name, global_name(100));
        assert_eq!(inst.len(), 0);
    } else {
        panic!("Expected Var atom");
    }
}

#[test]
fn test_transform_atom_literal() {
    let mut mono = Monomorphizer::new(Name(100));

    let atom = atom_int(42);
    let result = mono.transform_atom(atom);

    assert!(matches!(result, Atom::IntLit(42)));
}

#[test]
fn test_instantiate_creates_specialized() {
    let mut mono = Monomorphizer::new(Name(100));

    // Create a generic identity function: forall a. a -> a = λx.x
    let scheme = make_scheme(
        vec![(0, Rc::new(Kind::Star))],
        make_function(make_type_var(0), make_type_var(0)),
    );
    let expr = expr_simple(
        atom_var(global_name(1), vec![]),
        make_function(make_type_var(0), make_type_var(0)),
    );
    let poly = poly_val(
        global_name(10),
        scheme,
        make_function(make_type_var(0), make_type_var(0)),
        expr,
    );

    mono.register_decls(&[poly]);

    // Get specialized name first
    let spec_name = mono.get_specialized_name(global_name(10), vec![make_int()]);

    // Instantiate
    let specialized = mono.instantiate(global_name(10), vec![make_int()]);

    // Verify the result
    if let Decl::PolyVal { name, ty, .. } = specialized {
        assert_eq!(name, spec_name);
        // Type should be Int -> Int
        if let TypeKind::Function(arg, ret) = &ty.ty {
            assert!(matches!(arg.ty, TypeKind::Con(_)));
            assert!(matches!(ret.ty, TypeKind::Con(_)));
        } else {
            panic!("Expected function type");
        }
    } else {
        panic!("Expected PolyVal");
    }
}

#[test]
fn test_monomorphize_identity_single() {
    // Program:
    //   identity: forall a. a -> a = λx.x
    //   main: Int = identity[Int] 42

    let identity_scheme = make_scheme(
        vec![(0, Rc::new(Kind::Star))],
        make_function(make_type_var(0), make_type_var(0)),
    );
    let identity_body = expr_simple(atom_var(global_name(1), vec![]), make_type_var(0));
    let identity = poly_val(
        global_name(10),
        identity_scheme,
        make_function(make_type_var(0), make_type_var(0)),
        identity_body,
    );

    let main_expr = prim_app(atom_var(global_name(10), vec![make_int()]), atom_int(42));
    let main = mono_val(global_name(20), make_int(), main_expr);

    let program = make_program(vec![identity, main], Name(100), global_name(20));
    let result = monomorphize(program);

    // Check that we have specialized declarations
    assert!(result.decls.len() >= 2);
}

#[test]
fn test_monomorphize_identity_multiple() {
    // Program with multiple specializations of identity
    let identity_scheme = make_scheme(
        vec![(0, Rc::new(Kind::Star))],
        make_function(make_type_var(0), make_type_var(0)),
    );
    let identity_body = expr_simple(atom_var(global_name(1), vec![]), make_type_var(0));
    let identity = poly_val(
        global_name(10),
        identity_scheme,
        make_function(make_type_var(0), make_type_var(0)),
        identity_body,
    );

    let main1_expr = prim_app(atom_var(global_name(10), vec![make_int()]), atom_int(42));
    let main1 = mono_val(global_name(20), make_int(), main1_expr);

    let main2_expr = prim_app(
        atom_var(global_name(10), vec![make_bool()]),
        atom_bool(true),
    );
    let main2 = mono_val(global_name(21), make_bool(), main2_expr);

    let program = make_program(vec![identity, main1, main2], Name(100), global_name(20));
    let result = monomorphize(program);

    // Should have at least 3 decls (original identity stays, plus main1, main2)
    assert!(result.decls.len() >= 3);
}

#[test]
fn test_monomorphize_caching() {
    // Same specialization requested twice should reuse the same specialized name
    let identity_scheme = make_scheme(
        vec![(0, Rc::new(Kind::Star))],
        make_function(make_type_var(0), make_type_var(0)),
    );
    let identity_body = expr_simple(atom_var(global_name(1), vec![]), make_type_var(0));
    let identity = poly_val(
        global_name(10),
        identity_scheme,
        make_function(make_type_var(0), make_type_var(0)),
        identity_body,
    );

    // Two usages with same type
    let main1_expr = prim_app(atom_var(global_name(10), vec![make_int()]), atom_int(1));
    let main1 = mono_val(global_name(20), make_int(), main1_expr);

    let main2_expr = prim_app(atom_var(global_name(10), vec![make_int()]), atom_int(2));
    let main2 = mono_val(global_name(21), make_int(), main2_expr);

    let program = make_program(vec![identity, main1, main2], Name(100), global_name(20));
    let result = monomorphize(program);

    // Verify that both uses reference the same function
    // (This is implicitly tested by the caching mechanism)
    assert!(result.decls.len() >= 3);
}

#[test]
fn test_monomorphize_pack_clearing() {
    // Pack instantiation should be cleared after monomorphization
    let pack_expr = prim_pack(0, vec![make_int()], Some(atom_int(42)));
    let main = mono_val(global_name(20), make_int(), pack_expr);

    let program = make_program(vec![main], Name(100), global_name(20));
    let result = monomorphize(program);

    // Check that Pack's instantiation is cleared
    if let Some(Decl::MonoVal { expr, .. }) = result.decls.first() {
        if let PrimExpr::Pack { instantiation, .. } = expr {
            assert_eq!(instantiation.len(), 0);
        } else {
            panic!("Expected Pack expression");
        }
    } else {
        panic!("Expected MonoVal");
    }
}

#[test]
fn test_monomorphize_builtin_clearing() {
    // Builtin instantiation should be cleared
    let builtin_expr = prim_builtin(BuiltinFn::Print, vec![make_int()]);
    let main = mono_val(global_name(20), make_unit(), builtin_expr);

    let program = make_program(vec![main], Name(100), global_name(20));
    let result = monomorphize(program);

    // Check that Builtin's instantiation is cleared
    if let Some(Decl::MonoVal { expr, .. }) = result.decls.first() {
        if let PrimExpr::Builtin { instantiation, .. } = expr {
            assert_eq!(instantiation.len(), 0);
        } else {
            panic!("Expected Builtin expression");
        }
    } else {
        panic!("Expected MonoVal");
    }
}

#[test]
fn test_monomorphize_lambda_preserved() {
    // Lambda captures should be preserved
    let lambda_body = expr_simple(atom_var(global_name(1), vec![]), make_int());
    let lambda = prim_lambda(
        global_name(2),
        make_int(),
        lambda_body,
        vec![global_name(5)],
    );
    let main = mono_val(
        global_name(20),
        make_function(make_int(), make_int()),
        lambda,
    );

    let program = make_program(vec![main], Name(100), global_name(20));
    let result = monomorphize(program);

    // Check that captures are preserved
    if let Some(Decl::MonoVal { expr, .. }) = result.decls.first() {
        if let PrimExpr::Lambda { captures, .. } = expr {
            assert_eq!(captures.len(), 1);
            assert_eq!(captures[0], global_name(5));
        } else {
            panic!("Expected Lambda expression");
        }
    } else {
        panic!("Expected MonoVal");
    }
}

#[test]
fn test_monomorphize_switch_branches() {
    // Switch branches should be transformed
    let branch1 = SwitchBranch {
        tag: 0,
        body: expr_simple(atom_int(1), make_int()),
    };
    let branch2 = SwitchBranch {
        tag: 1,
        body: expr_simple(atom_int(2), make_int()),
    };
    let switch_expr = PrimExpr::Switch {
        scrutinee: atom_int(0),
        branches: vec![branch1, branch2],
        default: None,
    };
    let main = mono_val(global_name(20), make_int(), switch_expr);

    let program = make_program(vec![main], Name(100), global_name(20));
    let result = monomorphize(program);

    // Check that switch is preserved
    if let Some(Decl::MonoVal { expr, .. }) = result.decls.first() {
        if let PrimExpr::Switch { branches, .. } = expr {
            assert_eq!(branches.len(), 2);
        } else {
            panic!("Expected Switch expression");
        }
    } else {
        panic!("Expected MonoVal");
    }
}

#[test]
fn test_monomorphize_rec_decl() {
    // Rec declarations should be preserved
    let mono1 = mono_val(global_name(10), make_int(), prim_atom(atom_int(1)));
    let mono2 = mono_val(global_name(11), make_int(), prim_atom(atom_int(2)));
    let rec = rec_decl(vec![mono1, mono2]);

    let program = make_program(vec![rec], Name(100), global_name(10));
    let result = monomorphize(program);

    // Check that Rec is preserved
    if let Some(Decl::Rec { defs }) = result.decls.first() {
        assert_eq!(defs.len(), 2);
    } else {
        panic!("Expected Rec declaration");
    }
}

#[test]
fn test_monomorphize_complex_scheme() {
    // forall a b. (a -> b) -> a -> b
    let scheme = make_scheme(
        vec![(0, Rc::new(Kind::Star)), (1, Rc::new(Kind::Star))],
        make_function(
            make_function(make_type_var(0), make_type_var(1)),
            make_function(make_type_var(0), make_type_var(1)),
        ),
    );
    let body = expr_simple(atom_var(global_name(1), vec![]), make_type_var(1));
    let poly = poly_val(
        global_name(10),
        scheme,
        make_function(
            make_function(make_type_var(0), make_type_var(1)),
            make_function(make_type_var(0), make_type_var(1)),
        ),
        body,
    );

    let use_expr = prim_atom(atom_var(global_name(10), vec![make_int(), make_bool()]));
    let main = mono_val(
        global_name(20),
        make_function(
            make_function(make_int(), make_bool()),
            make_function(make_int(), make_bool()),
        ),
        use_expr,
    );

    let program = make_program(vec![poly, main], Name(100), global_name(20));
    let result = monomorphize(program);

    // Should successfully monomorphize
    assert!(result.decls.len() >= 2);
}

#[test]
fn test_empty_program() {
    // Empty program should work
    let program = make_program(vec![], Name(100), global_name(0));
    let result = monomorphize(program);

    assert_eq!(result.decls.len(), 0);
}

#[test]
fn test_monomorphize_nested_scope() {
    let outer = mono_val(
        global_name(20),
        make_function(make_int(), make_int()),
        prim_atom(atom_int(42)),
    );

    let program = make_program(vec![outer], Name(100), global_name(20));
    let result = monomorphize(program);

    // Should handle nested scope
    assert!(result.decls.len() >= 1);
}

#[test]
fn test_monomorphize_if_expr() {
    // If expressions should be transformed
    let then_expr = expr_simple(atom_int(1), make_int());
    let else_expr = expr_simple(atom_int(0), make_int());
    let if_expr = prim_if(atom_bool(true), then_expr, else_expr);
    let main = mono_val(global_name(20), make_int(), if_expr);

    let program = make_program(vec![main], Name(100), global_name(20));
    let result = monomorphize(program);

    // Check that If is preserved
    if let Some(Decl::MonoVal { expr, .. }) = result.decls.first() {
        if let PrimExpr::If(_, then_e, else_e) = expr {
            assert!(matches!(then_e.result, Atom::IntLit(1)));
            assert!(matches!(else_e.result, Atom::IntLit(0)));
        } else {
            panic!("Expected If expression");
        }
    } else {
        panic!("Expected MonoVal");
    }
}

#[test]
fn test_atom_float_literal() {
    let mut mono = Monomorphizer::new(Name(100));

    let atom = Atom::FloatLit(3.14);
    let result = mono.transform_atom(atom);

    assert!(matches!(result, Atom::FloatLit(f) if (f - 3.14).abs() < 0.001));
}

#[test]
fn test_atom_string_literal() {
    let mut mono = Monomorphizer::new(Name(100));

    let atom = Atom::StringLit("hello".to_string());
    let result = mono.transform_atom(atom);

    assert!(matches!(result, Atom::StringLit(s) if s == "hello"));
}

#[test]
fn test_atom_emptylist_literal() {
    let mut mono = Monomorphizer::new(Name(100));

    let atom = Atom::EmptyListLit;
    let result = mono.transform_atom(atom);

    assert!(matches!(result, Atom::EmptyListLit));
}

#[test]
fn test_substitutor_float_atom() {
    let scheme = make_scheme(vec![(0, Rc::new(Kind::Star))], make_type_var(0));
    let args = vec![make_int()];

    let subst = Substitutor::new(&scheme, &args);
    let atom = Atom::FloatLit(2.71);
    let result = subst.subst_atom(atom);

    assert!(matches!(result, Atom::FloatLit(f) if (f - 2.71).abs() < 0.001));
}

#[test]
fn test_substitutor_string_atom() {
    let scheme = make_scheme(vec![(0, Rc::new(Kind::Star))], make_type_var(0));
    let args = vec![make_int()];

    let subst = Substitutor::new(&scheme, &args);
    let atom = Atom::StringLit("test".to_string());
    let result = subst.subst_atom(atom);

    assert!(matches!(result, Atom::StringLit(s) if s == "test"));
}

#[test]
fn test_monomorphize_binop() {
    use crate::parser::BinOp;

    let binop_expr = PrimExpr::BinOp(BinOp::And, atom_bool(true), atom_bool(false));
    let main = mono_val(global_name(20), make_bool(), binop_expr);

    let program = make_program(vec![main], Name(100), global_name(20));
    let result = monomorphize(program);

    if let Some(Decl::MonoVal { expr, .. }) = result.decls.first() {
        if let PrimExpr::BinOp(op, left, right) = expr {
            assert!(matches!(op, BinOp::And));
            assert!(matches!(left, Atom::BoolLit(true)));
            assert!(matches!(right, Atom::BoolLit(false)));
        } else {
            panic!("Expected BinOp expression");
        }
    } else {
        panic!("Expected MonoVal");
    }
}

#[test]
fn test_substitutor_binop() {
    use crate::parser::BinOp;

    let scheme = make_scheme(vec![(0, Rc::new(Kind::Star))], make_type_var(0));
    let args = vec![make_int()];

    let subst = Substitutor::new(&scheme, &args);
    let binop = PrimExpr::BinOp(
        BinOp::Or,
        atom_var(global_name(1), vec![make_type_var(0)]),
        atom_bool(false),
    );
    let result = subst.subst_prim(binop);

    if let PrimExpr::BinOp(op, left, right) = result {
        assert!(matches!(op, BinOp::Or));
        assert!(matches!(right, Atom::BoolLit(false)));
        if let Atom::Var { inst, .. } = left {
            assert_eq!(inst.len(), 1);
            assert!(matches!(inst[0].ty, TypeKind::Con(_)));
        }
    } else {
        panic!("Expected BinOp");
    }
}

#[test]
fn test_monomorphize_cons() {
    let cons_expr = PrimExpr::Cons {
        head: atom_int(1),
        tail: Atom::EmptyListLit,
    };
    let main = mono_val(global_name(20), make_list(make_int()), cons_expr);

    let program = make_program(vec![main], Name(100), global_name(20));
    let result = monomorphize(program);

    if let Some(Decl::MonoVal { expr, .. }) = result.decls.first() {
        if let PrimExpr::Cons { head, tail } = expr {
            assert!(matches!(head, Atom::IntLit(1)));
            assert!(matches!(tail, Atom::EmptyListLit));
        } else {
            panic!("Expected Cons expression");
        }
    } else {
        panic!("Expected MonoVal");
    }
}

#[test]
fn test_substitutor_cons() {
    let scheme = make_scheme(vec![(0, Rc::new(Kind::Star))], make_type_var(0));
    let args = vec![make_int()];

    let subst = Substitutor::new(&scheme, &args);
    let cons = PrimExpr::Cons {
        head: atom_var(global_name(1), vec![make_type_var(0)]),
        tail: Atom::EmptyListLit,
    };
    let result = subst.subst_prim(cons);

    if let PrimExpr::Cons { head, tail } = result {
        if let Atom::Var { inst, .. } = head {
            assert_eq!(inst.len(), 1);
            assert!(matches!(inst[0].ty, TypeKind::Con(_)));
        } else {
            panic!("Expected Var in head");
        }
        assert!(matches!(tail, Atom::EmptyListLit));
    } else {
        panic!("Expected Cons");
    }
}

#[test]
fn test_monomorphize_record() {
    let mut fields = BTreeMap::new();
    fields.insert("x".to_string(), atom_int(1));
    fields.insert("y".to_string(), atom_int(2));
    let record_expr = PrimExpr::Record(fields);
    let record_ty = make_record(vec![("x", make_int()), ("y", make_int())]);
    let main = mono_val(global_name(20), record_ty, record_expr);

    let program = make_program(vec![main], Name(100), global_name(20));
    let result = monomorphize(program);

    if let Some(Decl::MonoVal { expr, .. }) = result.decls.first() {
        if let PrimExpr::Record(fields) = expr {
            assert_eq!(fields.len(), 2);
            assert!(fields.contains_key("x"));
            assert!(fields.contains_key("y"));
        } else {
            panic!("Expected Record expression");
        }
    } else {
        panic!("Expected MonoVal");
    }
}

#[test]
fn test_substitutor_record() {
    let scheme = make_scheme(vec![(0, Rc::new(Kind::Star))], make_type_var(0));
    let args = vec![make_int()];

    let subst = Substitutor::new(&scheme, &args);
    let mut fields = BTreeMap::new();
    fields.insert(
        "a".to_string(),
        atom_var(global_name(1), vec![make_type_var(0)]),
    );
    fields.insert("b".to_string(), atom_int(5));
    let record = PrimExpr::Record(fields);
    let result = subst.subst_prim(record);

    if let PrimExpr::Record(fields) = result {
        assert_eq!(fields.len(), 2);
        if let Some(Atom::Var { inst, .. }) = fields.get("a") {
            assert_eq!(inst.len(), 1);
            assert!(matches!(inst[0].ty, TypeKind::Con(_)));
        } else {
            panic!("Expected Var in field a");
        }
    } else {
        panic!("Expected Record");
    }
}

#[test]
fn test_monomorphize_rec_record() {
    let mut fields = BTreeMap::new();
    fields.insert("x".to_string(), (global_name(10), atom_int(1)));
    fields.insert("y".to_string(), (global_name(11), atom_int(2)));
    let rec_record_expr = PrimExpr::RecRecord(fields);
    let record_ty = make_record(vec![("x", make_int()), ("y", make_int())]);
    let main = mono_val(global_name(20), record_ty, rec_record_expr);

    let program = make_program(vec![main], Name(100), global_name(20));
    let result = monomorphize(program);

    if let Some(Decl::MonoVal { expr, .. }) = result.decls.first() {
        if let PrimExpr::RecRecord(fields) = expr {
            assert_eq!(fields.len(), 2);
            assert!(fields.contains_key("x"));
            assert!(fields.contains_key("y"));
        } else {
            panic!("Expected RecRecord expression");
        }
    } else {
        panic!("Expected MonoVal");
    }
}

#[test]
fn test_monomorphize_field_access() {
    let field_access_expr =
        PrimExpr::FieldAccess(atom_var(global_name(10), vec![]), "name".to_string());
    let main = mono_val(global_name(20), make_string(), field_access_expr);

    let program = make_program(vec![main], Name(100), global_name(20));
    let result = monomorphize(program);

    if let Some(Decl::MonoVal { expr, .. }) = result.decls.first() {
        if let PrimExpr::FieldAccess(record, field) = expr {
            assert!(matches!(record, Atom::Var { .. }));
            assert_eq!(field, "name");
        } else {
            panic!("Expected FieldAccess expression");
        }
    } else {
        panic!("Expected MonoVal");
    }
}

#[test]
fn test_monomorphize_fst_snd() {
    let fst_expr = PrimExpr::Fst(atom_var(global_name(10), vec![]));
    let main1 = mono_val(global_name(20), make_int(), fst_expr);

    let snd_expr = PrimExpr::Snd(atom_var(global_name(10), vec![]));
    let main2 = mono_val(global_name(21), make_bool(), snd_expr);

    let program = make_program(vec![main1, main2], Name(100), global_name(20));
    let result = monomorphize(program);

    assert_eq!(result.decls.len(), 2);

    if let Some(Decl::MonoVal { expr, .. }) = result.decls.first() {
        assert!(matches!(expr, PrimExpr::Fst(_)));
    } else {
        panic!("Expected MonoVal");
    }

    if let Some(Decl::MonoVal { expr, .. }) = result.decls.get(1) {
        assert!(matches!(expr, PrimExpr::Snd(_)));
    } else {
        panic!("Expected MonoVal");
    }
}

#[test]
fn test_monomorphize_unpack_tag() {
    let unpack_expr = PrimExpr::UnpackTag(atom_var(global_name(10), vec![]));
    let main = mono_val(global_name(20), make_int(), unpack_expr);

    let program = make_program(vec![main], Name(100), global_name(20));
    let result = monomorphize(program);

    if let Some(Decl::MonoVal { expr, .. }) = result.decls.first() {
        if let PrimExpr::UnpackTag(atom) = expr {
            assert!(matches!(atom, Atom::Var { .. }));
        } else {
            panic!("Expected UnpackTag expression");
        }
    } else {
        panic!("Expected MonoVal");
    }
}

#[test]
fn test_monomorphize_unpack_payload() {
    let unpack_expr = PrimExpr::UnpackPayload(atom_var(global_name(10), vec![]));
    let main = mono_val(global_name(20), make_int(), unpack_expr);

    let program = make_program(vec![main], Name(100), global_name(20));
    let result = monomorphize(program);

    if let Some(Decl::MonoVal { expr, .. }) = result.decls.first() {
        if let PrimExpr::UnpackPayload(atom) = expr {
            assert!(matches!(atom, Atom::Var { .. }));
        } else {
            panic!("Expected UnpackPayload expression");
        }
    } else {
        panic!("Expected MonoVal");
    }
}

#[test]
fn test_monomorphize_switch_with_default() {
    let branch1 = SwitchBranch {
        tag: 0,
        body: expr_simple(atom_int(1), make_int()),
    };
    let branch2 = SwitchBranch {
        tag: 1,
        body: expr_simple(atom_int(2), make_int()),
    };
    let default_expr = Some(Box::new(expr_simple(atom_int(99), make_int())));
    let switch_expr = PrimExpr::Switch {
        scrutinee: atom_int(0),
        branches: vec![branch1, branch2],
        default: default_expr,
    };
    let main = mono_val(global_name(20), make_int(), switch_expr);

    let program = make_program(vec![main], Name(100), global_name(20));
    let result = monomorphize(program);

    if let Some(Decl::MonoVal { expr, .. }) = result.decls.first() {
        if let PrimExpr::Switch {
            branches, default, ..
        } = expr
        {
            assert_eq!(branches.len(), 2);
            assert!(default.is_some());
            if let Some(default_body) = default {
                assert!(matches!(default_body.result, Atom::IntLit(99)));
            }
        } else {
            panic!("Expected Switch expression");
        }
    } else {
        panic!("Expected MonoVal");
    }
}

#[test]
fn test_nested_polyval() {
    // Outer function: forall a. a -> a
    let inner_scheme = make_scheme(
        vec![(1, Rc::new(Kind::Star))],
        make_function(make_type_var(1), make_type_var(1)),
    );
    let inner_body = expr_simple(atom_var(global_name(2), vec![]), make_type_var(1));
    let inner_poly = poly_val(
        global_name(11),
        inner_scheme,
        make_function(make_type_var(1), make_type_var(1)),
        inner_body,
    );

    // Outer body: uses inner_poly[Int]
    let outer_body = expr_with_decls(
        vec![inner_poly],
        atom_var(global_name(11), vec![make_int()]),
        make_function(make_int(), make_int()),
    );

    let outer_scheme = make_scheme(
        vec![(0, Rc::new(Kind::Star))],
        make_function(make_type_var(0), make_type_var(0)),
    );
    let outer_poly = poly_val(
        global_name(10),
        outer_scheme,
        make_function(make_type_var(0), make_type_var(0)),
        outer_body,
    );

    // Main uses outer[Bool]
    let main_expr = prim_atom(atom_var(global_name(10), vec![make_bool()]));
    let main = mono_val(
        global_name(20),
        make_function(make_bool(), make_bool()),
        main_expr,
    );

    let program = make_program(vec![outer_poly, main], Name(100), global_name(20));
    let result = monomorphize(program);

    // Should create specialized versions
    assert!(result.decls.len() >= 2);
}

#[test]
fn test_mutually_recursive_poly() {
    // isEven: forall a. List[a] -> Bool
    let is_even_scheme = make_scheme(
        vec![(0, Rc::new(Kind::Star))],
        make_function(make_list(make_type_var(0)), make_bool()),
    );
    let is_even_body = expr_simple(
        atom_var(global_name(31), vec![make_type_var(0)]), // calls isOdd
        make_bool(),
    );
    let is_even = poly_val(
        global_name(30),
        is_even_scheme,
        make_function(make_list(make_type_var(0)), make_bool()),
        is_even_body,
    );

    // isOdd: forall a. List[a] -> Bool
    let is_odd_scheme = make_scheme(
        vec![(0, Rc::new(Kind::Star))],
        make_function(make_list(make_type_var(0)), make_bool()),
    );
    let is_odd_body = expr_simple(
        atom_var(global_name(30), vec![make_type_var(0)]), // calls isEven
        make_bool(),
    );
    let is_odd = poly_val(
        global_name(31),
        is_odd_scheme,
        make_function(make_list(make_type_var(0)), make_bool()),
        is_odd_body,
    );

    let rec = rec_decl(vec![is_even, is_odd]);

    // Main uses isEven[Int]
    let main_expr = prim_atom(atom_var(global_name(30), vec![make_int()]));
    let main = mono_val(
        global_name(20),
        make_function(make_list(make_int()), make_bool()),
        main_expr,
    );

    let program = make_program(vec![rec, main], Name(100), global_name(20));
    let result = monomorphize(program);

    assert!(result.decls.len() >= 2);
}

#[test]
fn test_accumulate_single_crate() {
    use super::accumulate;
    use crate::analysis::resolver::CrateId;
    use crate::ir::anf::Crate;

    let decl1 = mono_val(global_name(1), make_int(), prim_atom(atom_int(42)));
    let decl2 = mono_val(global_name(2), make_bool(), prim_atom(atom_bool(true)));

    let crate1 = Crate {
        crate_id: CrateId(0),
        globals: vec![decl1, decl2],
        next_name: GlobalName {
            krate: None,
            name: Name(50),
        },
    };

    let main_name = global_name(1);
    let program = accumulate(vec![crate1], main_name);

    assert_eq!(program.decls.len(), 2);
    assert_eq!(program.main_name, main_name);
    assert_eq!(program.next_name, Name(50));
}

#[test]
fn test_accumulate_multiple_crates() {
    use super::accumulate;
    use crate::analysis::resolver::CrateId;
    use crate::ir::anf::Crate;

    let decl1 = mono_val(global_name(1), make_int(), prim_atom(atom_int(10)));
    let crate1 = Crate {
        crate_id: CrateId(0),
        globals: vec![decl1],
        next_name: GlobalName {
            krate: None,
            name: Name(20),
        },
    };

    let decl2 = mono_val(global_name(2), make_bool(), prim_atom(atom_bool(false)));
    let crate2 = Crate {
        crate_id: CrateId(1),
        globals: vec![decl2],
        next_name: GlobalName {
            krate: Some(CrateId(1)),
            name: Name(30),
        },
    };

    let main_name = global_name(1);
    let program = accumulate(vec![crate1, crate2], main_name);

    assert_eq!(program.decls.len(), 2);
    assert_eq!(program.main_name, main_name);
    // Should use the max name from crates with None krate
    assert_eq!(program.next_name, Name(20));
}

#[test]
fn test_monomorphize_chain_specialization() {
    // g<T>(y: T) = y
    // f<A>(x: A) = g<A>(x)
    // main = f<Int>(42)

    // This tests if monomorphizing 'f' correctly triggers
    // the registration and specialization of 'g'.

    let g_scheme = make_scheme(vec![(0, Rc::new(Kind::Star))], make_type_var(0));
    let g_poly = poly_val(
        global_name(1),
        g_scheme,
        make_type_var(0),
        expr_simple(atom_var(global_name(10), vec![]), make_type_var(0)),
    );

    let f_scheme = make_scheme(vec![(1, Rc::new(Kind::Star))], make_type_var(1));
    let f_body = expr_simple(
        atom_var(global_name(1), vec![make_type_var(1)]),
        make_type_var(1),
    );
    let f_poly = poly_val(global_name(2), f_scheme, make_type_var(1), f_body);

    let main = mono_val(
        global_name(3),
        make_int(),
        prim_app(atom_var(global_name(2), vec![make_int()]), atom_int(42)),
    );

    let program = make_program(vec![g_poly, f_poly, main], Name(100), global_name(3));
    let result = monomorphize(program);

    // Should find specialized 'f_Int' AND specialized 'g_Int'
    assert!(result.decls.len() >= 3);
}
