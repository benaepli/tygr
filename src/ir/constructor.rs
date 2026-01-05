use crate::analysis::inference::{
    Type, TypeKind, TypeScheme, Typed, TypedCrate, TypedDefinition, TypedGroup, TypedKind,
    TypedPattern, TypedPatternKind,
};
use crate::analysis::resolver::{CrateId, GlobalName};
use crate::builtin::BuiltinFn;
use crate::ir::direct::closure::VariantDef;
use crate::ir::tags::TagMap;
use crate::parser::BinOp;
use std::collections::{BTreeMap, HashSet};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Crate {
    pub crate_id: CrateId,
    pub groups: Vec<Cluster>,
    pub variants: Vec<VariantDef>,
    pub next_name: GlobalName,
}

#[derive(Debug, Clone)]
pub enum Cluster {
    Recursive(Vec<Def>),
    NonRecursive(Def),
}

#[derive(Debug, Clone)]
pub struct Def {
    pub name: GlobalName,
    pub expr: Expr,
    pub ty: Rc<Type>,
    pub scheme: TypeScheme,
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
    pub bindings: Vec<(GlobalName, TypeScheme)>,
    pub scheme: TypeScheme,
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
    Var {
        name: GlobalName,
        instantiation: Vec<Rc<Type>>,
    },
    Lambda {
        param: GlobalName,
        body: Box<Expr>,
        captures: HashSet<GlobalName>,
    },
    App(Box<Expr>, Box<Expr>),
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
    Builtin {
        fun: BuiltinFn,
        instantiation: Vec<Rc<Type>>,
    },
    Pack {
        tag: u32,
        payload: Option<Box<Expr>>,
        instantiation: Vec<Rc<Type>>,
    },
}

struct Converter {
    tag_map: TagMap,
    current_name: GlobalName,
}

impl Converter {
    pub fn new(variants: &[VariantDef], base_id: GlobalName) -> Self {
        let mut tag_map = TagMap::new();
        for variant in variants {
            for (index, ctor) in variant.constructors.iter().enumerate() {
                tag_map.insert(variant.name, ctor.name, index as u32);
            }
        }
        Self {
            tag_map,
            current_name: base_id,
        }
    }

    fn new_name(&mut self) -> GlobalName {
        let id = self.current_name;
        self.current_name.name.0 += 1;
        id
    }

    pub fn convert_crate(&mut self, typed: TypedCrate) -> Crate {
        let groups = typed
            .groups
            .into_iter()
            .map(|g| self.convert_group(g))
            .collect();
        Crate {
            crate_id: typed.crate_id,
            groups,
            variants: typed.variants,
            next_name: self.current_name,
        }
    }

    fn convert_group(&mut self, group: TypedGroup) -> Cluster {
        match group {
            TypedGroup::NonRecursive(def) => Cluster::NonRecursive(self.convert_def(def)),
            TypedGroup::Recursive(defs) => {
                Cluster::Recursive(defs.into_iter().map(|d| self.convert_def(d)).collect())
            }
        }
    }

    fn convert_def(&mut self, def: TypedDefinition) -> Def {
        Def {
            name: def.name.0,
            expr: self.convert_expr(*def.expr),
            ty: def.ty,
            scheme: def.scheme,
        }
    }

    pub fn convert_expr(&mut self, typed: Typed) -> Expr {
        let kind = match typed.kind {
            TypedKind::Var {
                name,
                instantiation,
            } => ExprKind::Var {
                name,
                instantiation,
            },
            TypedKind::Lambda {
                param,
                body,
                captures,
            } => {
                if let TypedPatternKind::Var { name } = param.kind {
                    ExprKind::Lambda {
                        param: name,
                        body: Box::new(self.convert_expr(*body)),
                        captures,
                    }
                } else {
                    let param_name = self.new_name();
                    let body_ty = body.ty.clone();
                    let pattern = self.convert_pattern(param);
                    let body = self.convert_expr(*body);
                    ExprKind::Lambda {
                        param: param_name,
                        body: Box::new(Expr {
                            kind: ExprKind::Match(
                                Box::new(Expr {
                                    kind: ExprKind::Var {
                                        name: param_name,
                                        instantiation: vec![],
                                    },
                                    ty: pattern.ty.clone(),
                                }),
                                vec![MatchBranch {
                                    pattern,
                                    body: Box::new(body),
                                }],
                            ),
                            ty: body_ty,
                        }),
                        captures,
                    }
                }
            }
            TypedKind::App(fun, arg) => {
                if let TypedKind::Constructor {
                    variant,
                    ctor,
                    instantiation,
                    ..
                } = fun.kind
                {
                    // Optimization: App(Ctor, Arg) -> Pack { tag, payload: Some(Arg) }
                    let tag = self.tag_map.get(variant, ctor);
                    ExprKind::Pack {
                        tag,
                        payload: Some(Box::new(self.convert_expr(*arg))),
                        instantiation,
                    }
                } else {
                    ExprKind::App(
                        Box::new(self.convert_expr(*fun)),
                        Box::new(self.convert_expr(*arg)),
                    )
                }
            }
            TypedKind::If(cond, then, els) => ExprKind::If(
                Box::new(self.convert_expr(*cond)),
                Box::new(self.convert_expr(*then)),
                Box::new(self.convert_expr(*els)),
            ),
            TypedKind::Match(scrutinee, branches) => {
                let new_branches = branches
                    .into_iter()
                    .map(|b| MatchBranch {
                        pattern: self.convert_pattern(b.pattern),
                        body: Box::new(self.convert_expr(*b.expr)),
                    })
                    .collect();
                ExprKind::Match(Box::new(self.convert_expr(*scrutinee)), new_branches)
            }
            TypedKind::Block(stmts, expr) => {
                let stmts = stmts
                    .into_iter()
                    .map(|s| Stmt {
                        pattern: self.convert_pattern(s.pattern),
                        value: Box::new(self.convert_expr(*s.value)),
                        bindings: s.bindings,
                        scheme: s.scheme,
                    })
                    .collect();
                let expr = expr.map(|e| Box::new(self.convert_expr(*e)));
                ExprKind::Block(stmts, expr)
            }
            TypedKind::Cons(head, tail) => ExprKind::Cons(
                Box::new(self.convert_expr(*head)),
                Box::new(self.convert_expr(*tail)),
            ),

            TypedKind::UnitLit => ExprKind::UnitLit,
            TypedKind::PairLit(a, b) => ExprKind::PairLit(
                Box::new(self.convert_expr(*a)),
                Box::new(self.convert_expr(*b)),
            ),
            TypedKind::IntLit(n) => ExprKind::IntLit(n),
            TypedKind::FloatLit(n) => ExprKind::FloatLit(n),
            TypedKind::BoolLit(b) => ExprKind::BoolLit(b),
            TypedKind::StringLit(s) => ExprKind::StringLit(s),
            TypedKind::EmptyListLit => ExprKind::EmptyListLit,
            TypedKind::RecordLit(fields) => {
                let fields = fields
                    .into_iter()
                    .map(|(name, e)| (name, self.convert_expr(e)))
                    .collect();
                ExprKind::RecordLit(fields)
            }

            TypedKind::BinOp(op, lhs, rhs) => ExprKind::BinOp(
                op,
                Box::new(self.convert_expr(*lhs)),
                Box::new(self.convert_expr(*rhs)),
            ),
            TypedKind::RecRecord(fields) => {
                let fields = fields
                    .into_iter()
                    .map(|(name, (gn, e))| (name, (gn, self.convert_expr(e))))
                    .collect();
                ExprKind::RecRecord(fields)
            }
            TypedKind::FieldAccess(expr, field) => {
                ExprKind::FieldAccess(Box::new(self.convert_expr(*expr)), field)
            }

            TypedKind::Builtin { fun, instantiation } => ExprKind::Builtin { fun, instantiation },
            TypedKind::Constructor {
                variant,
                ctor,
                nullary,
                instantiation,
            } => {
                let tag = self.tag_map.get(variant, ctor);
                if nullary {
                    ExprKind::Pack {
                        tag,
                        payload: None,
                        instantiation,
                    }
                } else {
                    let (arg_ty, ret_ty) = match &typed.ty.as_ref().ty {
                        TypeKind::Function(arg, ret) => (arg.clone(), ret.clone()),
                        _ => panic!("Non-nullary constructor must have a function type!"),
                    };

                    let param_name = self.new_name();

                    ExprKind::Lambda {
                        param: param_name,
                        captures: HashSet::new(),
                        body: Box::new(Expr {
                            kind: ExprKind::Pack {
                                tag,
                                payload: Some(Box::new(Expr {
                                    kind: ExprKind::Var {
                                        name: param_name,
                                        instantiation: vec![],
                                    },
                                    ty: arg_ty,
                                })),
                                instantiation,
                            },
                            ty: ret_ty,
                        }),
                    }
                }
            }
        };

        Expr { kind, ty: typed.ty }
    }

    fn convert_pattern(&mut self, pat: TypedPattern) -> Pattern {
        let kind = match pat.kind {
            TypedPatternKind::Var { name } => PatternKind::Var(name),
            TypedPatternKind::Unit => PatternKind::Unit,
            TypedPatternKind::Pair(a, b) => PatternKind::Pair(
                Box::new(self.convert_pattern(*a)),
                Box::new(self.convert_pattern(*b)),
            ),
            TypedPatternKind::Wildcard => PatternKind::Wildcard,
            TypedPatternKind::Cons(head, tail) => PatternKind::Cons(
                Box::new(self.convert_pattern(*head)),
                Box::new(self.convert_pattern(*tail)),
            ),
            TypedPatternKind::EmptyList => PatternKind::EmptyList,
            TypedPatternKind::Record(fields) => {
                let fields = fields
                    .into_iter()
                    .map(|(name, p)| (name, self.convert_pattern(p)))
                    .collect();
                PatternKind::Record(fields)
            }
            TypedPatternKind::Constructor(v, c, sub) => PatternKind::Tagged {
                tag: self.tag_map.get(v, c),
                payload: sub.map(|p| Box::new(self.convert_pattern(*p))),
            },
        };
        Pattern { kind, ty: pat.ty }
    }
}

/// Convert a TypedCrate to constructor IR.
pub fn convert(typed: TypedCrate, base_id: GlobalName) -> Crate {
    let mut converter = Converter::new(&typed.variants, base_id);
    converter.convert_crate(typed)
}
