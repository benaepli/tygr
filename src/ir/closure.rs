use crate::analysis::inference::{
    Type, TypeID, TypeKind, Typed, TypedGroup, TypedKind, TypedPattern, TypedPatternKind,
};
use crate::analysis::resolver::{Name, TypeName};
use crate::builtin::BuiltinFn;
use crate::parser::BinOp;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Program {
    pub clusters: Vec<Cluster>,
}

#[derive(Debug, Clone)]
pub enum Cluster {
    Recursive(Vec<Definition>),
    NonRecursive(Definition),
}

#[derive(Debug, Clone)]
pub enum Definition {
    Struct(StructDef),
    Function(FuncDef),
    Global(GlobalDef),
}

#[derive(Debug, Clone)]
pub struct StructDef {
    pub name: TypeName,
    pub type_params: Vec<TypeID>,
    pub fields: Vec<(Name, Rc<Type>)>,
}

#[derive(Debug, Clone)]
pub struct FuncDef {
    pub name: Name,
    pub type_params: Vec<TypeID>,
    pub param: Name,
    pub env_param: Name,
    pub env_struct: TypeName,
    pub body: Expr,
    pub ret_ty: Rc<Type>,
}

#[derive(Debug, Clone)]
pub struct GlobalDef {
    pub name: Name,
    pub ty: Rc<Type>,
    pub val: Expr,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Rc<Type>,
}

#[derive(Debug, Clone)]
pub struct Stmt {
    pub pattern: Pattern,
    pub value: Box<Expr>,
}

#[derive(Debug, Clone)]
pub struct MatchBranch {
    pub pattern: Pattern,
    pub body: Box<Expr>,
}

#[derive(Debug, Clone)]
pub struct Pattern {
    pub kind: PatternKind,
    pub ty: Rc<Type>,
}

#[derive(Debug, Clone)]
pub enum PatternKind {
    Var(Name),
    Unit,
    Pair(Box<Pattern>, Box<Pattern>),
    Wildcard,
    Cons(Box<Pattern>, Box<Pattern>),
    EmptyList,
    Record(BTreeMap<String, Pattern>),
    Constructor(TypeName, Name, Option<Box<Pattern>>),
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Local(Name),
    Global(Name),
    EnvAccess {
        field: Name,
    },
    MakeClosure {
        fn_ref: Name,
        env_struct: TypeName,
        captures: Vec<(Name, Expr)>,
    },
    CallClosure {
        closure: Box<Expr>,
        arg: Box<Expr>,
    },

    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<MatchBranch>),
    Block(Vec<Stmt>, Option<Box<Expr>>),

    UnitLit,
    PairLit(Box<Expr>, Box<Expr>),
    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StringLit(String),
    EmptyListLit,
    RecordLit(BTreeMap<String, Expr>),

    Cons(Box<Expr>, Box<Expr>),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    RecRecord(BTreeMap<String, (Name, Expr)>),
    FieldAccess(Box<Expr>, String),

    Builtin(BuiltinFn),
    Constructor {
        variant: TypeName,
        ctor: Name,
        nullary: bool,
    },
}

fn collect_free_type_vars(ty: &Type, set: &mut BTreeSet<TypeID>) {
    match &ty.ty {
        TypeKind::Var(id) => {
            set.insert(*id);
        }
        TypeKind::App(lhs, rhs) => {
            collect_free_type_vars(lhs, set);
            collect_free_type_vars(rhs, set);
        }
        TypeKind::Function(arg, ret) => {
            collect_free_type_vars(arg, set);
            collect_free_type_vars(ret, set);
        }
        TypeKind::Pair(a, b) => {
            collect_free_type_vars(a, set);
            collect_free_type_vars(b, set);
        }
        TypeKind::Record(fields) => {
            for t in fields.values() {
                collect_free_type_vars(t, set);
            }
        }
        TypeKind::Con(_) => {}
    }
}

fn compute_closure_type_params(
    captures: &[(Name, Rc<Type>)],
    param_ty: &Type,
    ret_ty: &Type,
) -> Vec<TypeID> {
    let mut type_vars = BTreeSet::new();
    for (_name, ty) in captures {
        collect_free_type_vars(ty, &mut type_vars);
    }
    collect_free_type_vars(param_ty, &mut type_vars);
    collect_free_type_vars(ret_ty, &mut type_vars);
    type_vars.into_iter().collect()
}

#[derive(Debug, Clone)]
enum VarSource {
    Local(Name, Rc<Type>),
    Env { field: Name, ty: Rc<Type> },
}

pub struct Converter {
    definitions: Vec<Definition>,
    counter: Name,
    type_counter: TypeName,
    globals: HashMap<Name, Rc<Type>>,
}

impl Converter {
    pub fn new(base: Name, base_type: TypeName) -> Self {
        Self {
            definitions: Vec::new(),
            counter: base,
            type_counter: base_type,
            globals: HashMap::new(),
        }
    }

    fn next_name(&mut self) -> Name {
        let n = self.counter;
        self.counter.0 += 1;
        n
    }

    fn next_type(&mut self) -> TypeName {
        let n = self.type_counter;
        self.type_counter.0 += 1;
        n
    }

    pub fn convert_program(&mut self, groups: Vec<TypedGroup>) -> Program {
        let mut clusters = Vec::new();

        for group in groups {
            match group {
                TypedGroup::NonRecursive(def) => {
                    self.globals.insert(def.name.0, def.ty.clone());
                    let empty_scope = HashMap::new();
                    let converted_expr = self.convert_expr(*def.expr, &empty_scope);
                    let global_def = GlobalDef {
                        name: def.name.0,
                        ty: def.ty.clone(),
                        val: converted_expr,
                    };
                    clusters.push(Cluster::NonRecursive(Definition::Global(global_def)));
                }
                TypedGroup::Recursive(defs) => {
                    for def in &defs {
                        self.globals.insert(def.name.0, def.ty.clone());
                    }

                    let mut converted_defs = Vec::new();
                    for def in defs {
                        let empty_scope = HashMap::new();
                        let converted_expr = self.convert_expr(*def.expr, &empty_scope);

                        let global_def = GlobalDef {
                            name: def.name.0,
                            ty: def.ty.clone(),
                            val: converted_expr,
                        };
                        converted_defs.push(Definition::Global(global_def));
                    }
                    clusters.push(Cluster::Recursive(converted_defs));
                }
            }
        }
        Program { clusters }
    }

    fn convert_pattern(&self, pat: TypedPattern) -> Pattern {
        let ty = pat.ty.clone();
        let kind = match pat.kind {
            TypedPatternKind::Var { name } => PatternKind::Var(name),
            TypedPatternKind::Wildcard => PatternKind::Wildcard,
            TypedPatternKind::Unit => PatternKind::Unit,
            TypedPatternKind::Pair(p1, p2) => PatternKind::Pair(
                Box::new(self.convert_pattern(*p1)),
                Box::new(self.convert_pattern(*p2)),
            ),
            TypedPatternKind::Cons(p1, p2) => PatternKind::Cons(
                Box::new(self.convert_pattern(*p1)),
                Box::new(self.convert_pattern(*p2)),
            ),
            TypedPatternKind::EmptyList => PatternKind::EmptyList,
            TypedPatternKind::Record(fields) => {
                let mut new_fields = BTreeMap::new();
                for (k, v) in fields {
                    new_fields.insert(k, self.convert_pattern(v));
                }
                PatternKind::Record(new_fields)
            }
            TypedPatternKind::Constructor(tn, n, p) => {
                PatternKind::Constructor(tn, n, p.map(|p| Box::new(self.convert_pattern(*p))))
            }
        };
        Pattern { kind, ty }
    }

    fn populate_scope_from_pattern_locals(
        &self,
        pat: &TypedPattern,
        scope: &mut HashMap<Name, VarSource>,
    ) {
        match &pat.kind {
            TypedPatternKind::Var { name } => {
                scope.insert(*name, VarSource::Local(*name, pat.ty.clone()));
            }
            TypedPatternKind::Pair(p1, p2) | TypedPatternKind::Cons(p1, p2) => {
                self.populate_scope_from_pattern_locals(p1, scope);
                self.populate_scope_from_pattern_locals(p2, scope);
            }
            TypedPatternKind::Constructor(_, _, p) => {
                if let Some(p) = p {
                    self.populate_scope_from_pattern_locals(p, scope)
                }
            }
            TypedPatternKind::Record(fields) => {
                for p in fields.values() {
                    self.populate_scope_from_pattern_locals(p, scope);
                }
            }
            _ => {}
        }
    }

    fn convert_expr(&mut self, expr: Typed, scope: &HashMap<Name, VarSource>) -> Expr {
        let ty = expr.ty.clone();
        match expr.kind {
            TypedKind::IntLit(i) => Expr {
                kind: ExprKind::IntLit(i),
                ty,
            },
            TypedKind::FloatLit(f) => Expr {
                kind: ExprKind::FloatLit(f),
                ty,
            },
            TypedKind::BoolLit(b) => Expr {
                kind: ExprKind::BoolLit(b),
                ty,
            },
            TypedKind::StringLit(s) => Expr {
                kind: ExprKind::StringLit(s),
                ty,
            },
            TypedKind::UnitLit => Expr {
                kind: ExprKind::UnitLit,
                ty,
            },
            TypedKind::EmptyListLit => Expr {
                kind: ExprKind::EmptyListLit,
                ty,
            },
            TypedKind::Var(name) => {
                let kind = match scope.get(&name) {
                    Some(VarSource::Local(n, _)) => ExprKind::Local(*n),
                    Some(VarSource::Env { field, .. }) => ExprKind::EnvAccess { field: *field },
                    None => {
                        if self.globals.contains_key(&name) {
                            ExprKind::Global(name)
                        } else {
                            panic!("Variable {:?} not found in scope or globals", name);
                        }
                    }
                };
                Expr { kind, ty }
            }
            TypedKind::Lambda {
                param,
                body,
                captures,
            } => {
                let mut sorted_captures: Vec<_> = captures.into_iter().collect();
                sorted_captures.sort_by(|a, b| a.0.cmp(&b.0));

                let mut env_fields = Vec::new();
                let mut env_init_exprs = Vec::new();
                let mut inner_scope = HashMap::new();

                for cap_name in sorted_captures {
                    if self.globals.contains_key(&cap_name) {
                        continue;
                    }
                    let (source_expr_kind, cap_ty) = match scope.get(&cap_name) {
                        Some(VarSource::Local(n, t)) => (ExprKind::Local(*n), t.clone()),
                        Some(VarSource::Env { field, ty }) => {
                            (ExprKind::EnvAccess { field: *field }, ty.clone())
                        }
                        _ => panic!("variable not registered!"),
                    };

                    let field_name = self.next_name();

                    env_fields.push((field_name, cap_ty.clone()));
                    env_init_exprs.push((
                        field_name,
                        Expr {
                            kind: source_expr_kind,
                            ty: cap_ty.clone(),
                        },
                    ));
                    inner_scope.insert(
                        cap_name,
                        VarSource::Env {
                            field: field_name,
                            ty: cap_ty,
                        },
                    );
                }

                let fn_name = self.next_name();
                let env_struct_name = self.next_type();
                let env_param_name = self.next_name();
                let arg_param_name = self.next_name();

                self.populate_scope_from_pattern_locals(&param, &mut inner_scope);

                let converted_body_expr = self.convert_expr(*body, &inner_scope);

                let ret_ty = match &ty.ty {
                    TypeKind::Function(_, r) => r.clone(),
                    _ => ty.clone(),
                };

                let body_wrapper = Expr {
                    kind: ExprKind::Match(
                        Box::new(Expr {
                            kind: ExprKind::Local(arg_param_name),
                            ty: param.ty.clone(),
                        }),
                        vec![MatchBranch {
                            pattern: self.convert_pattern(param.clone()),
                            body: Box::new(converted_body_expr),
                        }],
                    ),
                    ty: ret_ty.clone(),
                };

                let type_params = compute_closure_type_params(&env_fields, &param.ty, &ret_ty);

                self.definitions.push(Definition::Struct(StructDef {
                    name: env_struct_name,
                    type_params: type_params.clone(),
                    fields: env_fields,
                }));

                self.definitions.push(Definition::Function(FuncDef {
                    name: fn_name,
                    type_params,
                    param: arg_param_name,
                    env_param: env_param_name,
                    env_struct: env_struct_name,
                    body: body_wrapper,
                    ret_ty,
                }));

                Expr {
                    kind: ExprKind::MakeClosure {
                        fn_ref: fn_name,
                        env_struct: env_struct_name,
                        captures: env_init_exprs,
                    },
                    ty,
                }
            }

            TypedKind::App(fun, arg) => {
                let fun_expr = self.convert_expr(*fun, scope);
                let arg_expr = self.convert_expr(*arg, scope);
                Expr {
                    kind: ExprKind::CallClosure {
                        closure: Box::new(fun_expr),
                        arg: Box::new(arg_expr),
                    },
                    ty,
                }
            }
            TypedKind::If(cond, cons, alt) => {
                let c = self.convert_expr(*cond, scope);
                let t = self.convert_expr(*cons, scope);
                let e = self.convert_expr(*alt, scope);
                Expr {
                    kind: ExprKind::If(Box::new(c), Box::new(t), Box::new(e)),
                    ty,
                }
            }
            TypedKind::Block(stmts, tail) => {
                let mut block_scope = scope.clone();
                let mut new_stmts = Vec::new();

                for stmt in stmts {
                    let val = self.convert_expr(*stmt.value, &block_scope);
                    self.populate_scope_from_pattern_locals(&stmt.pattern, &mut block_scope);

                    new_stmts.push(Stmt {
                        pattern: self.convert_pattern(stmt.pattern),
                        value: Box::new(val),
                    });
                }

                let new_tail = tail.map(|t| Box::new(self.convert_expr(*t, &block_scope)));
                Expr {
                    kind: ExprKind::Block(new_stmts, new_tail),
                    ty,
                }
            }
            TypedKind::Match(target, branches) => {
                let c_target = self.convert_expr(*target, scope);
                let mut c_branches = Vec::new();

                for branch in branches {
                    let mut branch_scope = scope.clone();
                    self.populate_scope_from_pattern_locals(&branch.pattern, &mut branch_scope);

                    c_branches.push(MatchBranch {
                        pattern: self.convert_pattern(branch.pattern),
                        body: Box::new(self.convert_expr(*branch.expr, &branch_scope)),
                    });
                }
                Expr {
                    kind: ExprKind::Match(Box::new(c_target), c_branches),
                    ty,
                }
            }
            TypedKind::PairLit(a, b) => Expr {
                kind: ExprKind::PairLit(
                    Box::new(self.convert_expr(*a, scope)),
                    Box::new(self.convert_expr(*b, scope)),
                ),
                ty,
            },
            TypedKind::Cons(h, t) => Expr {
                kind: ExprKind::Cons(
                    Box::new(self.convert_expr(*h, scope)),
                    Box::new(self.convert_expr(*t, scope)),
                ),
                ty,
            },
            TypedKind::BinOp(op, l, r) => Expr {
                kind: ExprKind::BinOp(
                    op,
                    Box::new(self.convert_expr(*l, scope)),
                    Box::new(self.convert_expr(*r, scope)),
                ),
                ty,
            },
            TypedKind::Builtin(b) => Expr {
                kind: ExprKind::Builtin(b),
                ty,
            },
            TypedKind::Constructor {
                variant,
                ctor,
                nullary,
            } => Expr {
                kind: ExprKind::Constructor {
                    variant,
                    ctor,
                    nullary,
                },
                ty,
            },
            TypedKind::RecordLit(fields) => {
                let mut new_fields = BTreeMap::new();
                for (k, v) in fields {
                    new_fields.insert(k, self.convert_expr(v, scope));
                }
                Expr {
                    kind: ExprKind::RecordLit(new_fields),
                    ty,
                }
            }
            TypedKind::RecRecord(fields) => {
                let mut new_fields = BTreeMap::new();
                for (label, (name, expr)) in fields {
                    new_fields.insert(label, (name, self.convert_expr(expr, scope)));
                }
                Expr {
                    kind: ExprKind::RecRecord(new_fields),
                    ty,
                }
            }

            TypedKind::FieldAccess(expr, field) => {
                let converted_expr = self.convert_expr(*expr, scope);
                Expr {
                    kind: ExprKind::FieldAccess(Box::new(converted_expr), field),
                    ty,
                }
            }
        }
    }
}
