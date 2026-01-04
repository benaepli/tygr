use crate::analysis::inference::{Kind, Type, TypeID, TypeKind};
use crate::analysis::resolver::{GlobalName, GlobalType};
use crate::builtin::BuiltinFn;
use crate::ir::closure::{
    Cluster as ClosureCluster, Definition as ClosureDef, Expr as ClosureExpr,
    ExprKind as ClosureExprKind, Pattern as ClosurePattern, PatternKind as ClosurePatternKind,
    Program as ClosureProgram, Stmt as ClosureStmt,
};
use crate::parser::BinOp;
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Program {
    pub clusters: Vec<Cluster>,
    pub structs: Vec<StructDef>,
    pub functions: Vec<FuncDef>,
    pub globals: Vec<GlobalDef>,
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
    pub name: GlobalType,
    pub type_params: Vec<TypeID>,
    pub fields: Vec<(GlobalName, Rc<Type>)>,
}

#[derive(Debug, Clone)]
pub struct FuncDef {
    pub name: GlobalName,
    pub type_params: Vec<TypeID>,
    pub param: GlobalName,
    pub env_param: GlobalName,
    pub env_struct: GlobalType,
    pub body: Expr,
    pub ret_ty: Rc<Type>,
}

#[derive(Debug, Clone)]
pub struct GlobalDef {
    pub name: GlobalName,
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
    Var(GlobalName),
    Unit,
    Pair(Box<Pattern>, Box<Pattern>),
    Wildcard,
    Cons(Box<Pattern>, Box<Pattern>),
    EmptyList,
    Record(BTreeMap<String, Pattern>),
    Tagged {
        tag: u32,
        payload: Option<Box<Pattern>>,
    },
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Local(GlobalName),
    Global(GlobalName),
    EnvAccess {
        field: GlobalName,
    },
    MakeClosure {
        fn_ref: GlobalName,
        env_struct: GlobalType,
        captures: Vec<(GlobalName, Expr)>,
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
    RecRecord(BTreeMap<String, (GlobalName, Expr)>),
    FieldAccess(Box<Expr>, String),
    Builtin(BuiltinFn),

    Pack {
        tag: u32,
        payload: Option<Box<Expr>>,
    },
}

struct TagMap {
    mapping: BTreeMap<(GlobalType, GlobalName), u32>,
}

impl TagMap {
    fn new() -> Self {
        Self {
            mapping: BTreeMap::new(),
        }
    }

    fn insert(&mut self, type_name: GlobalType, ctor_name: GlobalName, tag: u32) {
        self.mapping.insert((type_name, ctor_name), tag);
    }

    fn get(&self, type_name: GlobalType, ctor_name: GlobalName) -> u32 {
        *self
            .mapping
            .get(&(type_name, ctor_name))
            .expect("Constructor tag not found")
    }
}

pub struct Converter {
    tag_map: TagMap,
    generated_funcs: Vec<FuncDef>,

    // Mapping from constructor name to the name of the generated helper function
    ctor_helpers: HashMap<(GlobalType, GlobalName), GlobalName>,
    name_counter: GlobalName,
}

impl Converter {
    pub fn new(base_name: GlobalName) -> Self {
        Self {
            tag_map: TagMap::new(),
            generated_funcs: Vec::new(),
            ctor_helpers: HashMap::new(),
            name_counter: base_name,
        }
    }

    fn next_name(&mut self) -> GlobalName {
        let n = self.name_counter;
        self.name_counter.name.0 += 1;
        n
    }

    pub fn convert_program(&mut self, prog: ClosureProgram) -> Program {
        let mut new_clusters = Vec::new();
        for variant in &prog.variants {
            for (index, ctor) in variant.constructors.iter().enumerate() {
                let tag = index as u32;
                self.tag_map.insert(variant.name, ctor.name, tag);

                if let Some(payload_ty) = &ctor.payload {
                    let helper_name = self.next_name();
                    self.ctor_helpers
                        .insert((variant.name, ctor.name), helper_name);

                    let param_name = self.next_name();
                    let env_param_name = self.next_name();

                    let mut ret_ty = Rc::new(Type {
                        ty: TypeKind::Con(variant.name),
                        kind: Rc::new(Kind::Star),
                    });

                    for param_id in &variant.type_params {
                        let param_ty = Rc::new(Type {
                            ty: TypeKind::Var(*param_id),
                            kind: Rc::new(Kind::Star),
                        });
                        ret_ty = Rc::new(Type {
                            ty: TypeKind::App(ret_ty, param_ty),
                            kind: Rc::new(Kind::Star),
                        });
                    }

                    let body_expr = Expr {
                        kind: ExprKind::Pack {
                            tag,
                            payload: Some(Box::new(Expr {
                                kind: ExprKind::Local(param_name),
                                ty: payload_ty.clone(),
                            })),
                        },
                        ty: ret_ty.clone(),
                    };

                    let func_def = FuncDef {
                        name: helper_name,
                        type_params: variant.type_params.clone(),
                        param: param_name,
                        env_param: env_param_name,
                        env_struct: variant.name,
                        body: body_expr,
                        ret_ty,
                    };

                    self.generated_funcs.push(func_def);
                    for func in self.generated_funcs.drain(..) {
                        new_clusters.push(Cluster::NonRecursive(Definition::Function(func)));
                    }
                }
            }
        }

        for cluster in prog.clusters {
            match cluster {
                ClosureCluster::NonRecursive(def) => {
                    let new_def = self.convert_definition(def);
                    new_clusters.push(Cluster::NonRecursive(new_def));
                }
                ClosureCluster::Recursive(defs) => {
                    let new_defs = defs
                        .into_iter()
                        .map(|d| self.convert_definition(d))
                        .collect();
                    new_clusters.push(Cluster::Recursive(new_defs));
                }
            }
        }

        Program {
            clusters: new_clusters,
            structs: Vec::new(),
            functions: Vec::new(),
            globals: Vec::new(),
        }
    }

    fn convert_definition(&mut self, def: ClosureDef) -> Definition {
        match def {
            ClosureDef::Struct(s) => Definition::Struct(StructDef {
                name: s.name,
                type_params: s.type_params,
                fields: s.fields,
            }),
            ClosureDef::Function(f) => Definition::Function(FuncDef {
                name: f.name,
                type_params: f.type_params,
                param: f.param,
                env_param: f.env_param,
                env_struct: f.env_struct,
                body: self.convert_expr(f.body),
                ret_ty: f.ret_ty,
            }),
            ClosureDef::Global(g) => Definition::Global(GlobalDef {
                name: g.name,
                ty: g.ty,
                val: self.convert_expr(g.val),
            }),
        }
    }

    fn convert_stmt(&mut self, stmt: ClosureStmt) -> Stmt {
        Stmt {
            pattern: self.convert_pattern(stmt.pattern),
            value: Box::new(self.convert_expr(*stmt.value)),
        }
    }

    fn convert_pattern(&mut self, pat: ClosurePattern) -> Pattern {
        let kind = match pat.kind {
            ClosurePatternKind::Var(n) => PatternKind::Var(n),
            ClosurePatternKind::Unit => PatternKind::Unit,
            ClosurePatternKind::Wildcard => PatternKind::Wildcard,
            ClosurePatternKind::EmptyList => PatternKind::EmptyList,
            ClosurePatternKind::Pair(p1, p2) => PatternKind::Pair(
                Box::new(self.convert_pattern(*p1)),
                Box::new(self.convert_pattern(*p2)),
            ),
            ClosurePatternKind::Cons(p1, p2) => PatternKind::Cons(
                Box::new(self.convert_pattern(*p1)),
                Box::new(self.convert_pattern(*p2)),
            ),
            ClosurePatternKind::Record(fields) => {
                let new_fields = fields
                    .into_iter()
                    .map(|(k, v)| (k, self.convert_pattern(v)))
                    .collect();
                PatternKind::Record(new_fields)
            }
            ClosurePatternKind::Constructor(type_name, ctor_name, sub_pat) => {
                let tag = self.tag_map.get(type_name, ctor_name);
                PatternKind::Tagged {
                    tag,
                    payload: sub_pat.map(|p| Box::new(self.convert_pattern(*p))),
                }
            }
        };
        Pattern { kind, ty: pat.ty }
    }

    fn convert_expr(&mut self, expr: ClosureExpr) -> Expr {
        let new_kind = match expr.kind {
            ClosureExprKind::Local(n) => ExprKind::Local(n),
            ClosureExprKind::Global(n) => ExprKind::Global(n),
            ClosureExprKind::EnvAccess { field } => ExprKind::EnvAccess { field },
            ClosureExprKind::UnitLit => ExprKind::UnitLit,
            ClosureExprKind::IntLit(i) => ExprKind::IntLit(i),
            ClosureExprKind::FloatLit(f) => ExprKind::FloatLit(f),
            ClosureExprKind::BoolLit(b) => ExprKind::BoolLit(b),
            ClosureExprKind::StringLit(s) => ExprKind::StringLit(s),
            ClosureExprKind::EmptyListLit => ExprKind::EmptyListLit,

            ClosureExprKind::Constructor {
                variant,
                ctor,
                nullary,
            } => {
                let tag = self.tag_map.get(variant, ctor);
                if nullary {
                    ExprKind::Pack { tag, payload: None }
                } else {
                    let helper = self
                        .ctor_helpers
                        .get(&(variant, ctor))
                        .expect("Helper should exist for non-nullary ctor");
                    ExprKind::Global(*helper)
                }
            }

            ClosureExprKind::Match(target, branches) => {
                let new_branches = branches
                    .into_iter()
                    .map(|b| MatchBranch {
                        pattern: self.convert_pattern(b.pattern),
                        body: Box::new(self.convert_expr(*b.body)),
                    })
                    .collect();
                ExprKind::Match(Box::new(self.convert_expr(*target)), new_branches)
            }

            ClosureExprKind::Block(stmts, tail) => {
                let new_stmts = stmts.into_iter().map(|s| self.convert_stmt(s)).collect();
                let new_tail = tail.map(|t| Box::new(self.convert_expr(*t)));
                ExprKind::Block(new_stmts, new_tail)
            }

            ClosureExprKind::MakeClosure {
                fn_ref,
                env_struct,
                captures,
            } => {
                let new_captures = captures
                    .into_iter()
                    .map(|(n, e)| (n, self.convert_expr(e)))
                    .collect();
                ExprKind::MakeClosure {
                    fn_ref,
                    env_struct,
                    captures: new_captures,
                }
            }

            ClosureExprKind::CallClosure { closure, arg } => ExprKind::CallClosure {
                closure: Box::new(self.convert_expr(*closure)),
                arg: Box::new(self.convert_expr(*arg)),
            },

            ClosureExprKind::If(c, t, e) => ExprKind::If(
                Box::new(self.convert_expr(*c)),
                Box::new(self.convert_expr(*t)),
                Box::new(self.convert_expr(*e)),
            ),

            ClosureExprKind::PairLit(a, b) => ExprKind::PairLit(
                Box::new(self.convert_expr(*a)),
                Box::new(self.convert_expr(*b)),
            ),
            ClosureExprKind::Cons(h, t) => ExprKind::Cons(
                Box::new(self.convert_expr(*h)),
                Box::new(self.convert_expr(*t)),
            ),
            ClosureExprKind::BinOp(op, l, r) => ExprKind::BinOp(
                op,
                Box::new(self.convert_expr(*l)),
                Box::new(self.convert_expr(*r)),
            ),
            ClosureExprKind::RecordLit(fields) => {
                let new_fields = fields
                    .into_iter()
                    .map(|(k, v)| (k, self.convert_expr(v)))
                    .collect();
                ExprKind::RecordLit(new_fields)
            }
            ClosureExprKind::RecRecord(fields) => {
                let new_fields = fields
                    .into_iter()
                    .map(|(k, (n, v))| (k, (n, self.convert_expr(v))))
                    .collect();
                ExprKind::RecRecord(new_fields)
            }
            ClosureExprKind::FieldAccess(e, f) => {
                ExprKind::FieldAccess(Box::new(self.convert_expr(*e)), f)
            }
            ClosureExprKind::Builtin(b) => ExprKind::Builtin(b),
        };

        Expr {
            kind: new_kind,
            ty: expr.ty,
        }
    }
}
