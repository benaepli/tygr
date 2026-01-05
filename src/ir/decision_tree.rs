use crate::analysis::inference::{Type, TypeKind, TypeScheme};
use crate::analysis::resolver::{CrateId, GlobalName};
use crate::builtin::{BuiltinFn, INT_TYPE};
use crate::ir::constructor::PatternKind;
use crate::ir::direct::closure::VariantDef;
use crate::ir::{constructor, pattern};
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
pub struct SwitchBranch {
    pub tag: u32,
    pub body: Box<Expr>,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Let {
        name: GlobalName,
        scheme: TypeScheme,
        val: Box<Expr>,
        body: Box<Expr>,
    },
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
    Switch {
        scrutinee: Box<Expr>,
        branches: Vec<SwitchBranch>,
        default: Option<Box<Expr>>,
    },

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
    Fst(Box<Expr>),
    Snd(Box<Expr>),
    Builtin {
        fun: BuiltinFn,
        instantiation: Vec<Rc<Type>>,
    },
    Pack {
        tag: u32,
        payload: Option<Box<Expr>>,
        instantiation: Vec<Rc<Type>>,
    },
    UnpackTag(Box<Expr>),
    UnpackPayload(Box<Expr>),
}

/// The context for lowering patterns.
struct MatchCompiler {
    current_name: GlobalName,
}

#[derive(Clone)]
struct Row {
    patterns: Vec<constructor::Pattern>,
    body: Expr,
    // Bindings accumulated during simplification (name, expr_to_bind)
    bindings: Vec<(GlobalName, Expr)>,
}

impl MatchCompiler {
    fn new(base_name: GlobalName) -> Self {
        Self {
            current_name: base_name,
        }
    }

    fn new_name(&mut self) -> GlobalName {
        let id = self.current_name;
        self.current_name.name.0 += 1;
        id
    }

    fn lower_cluster(&mut self, c: pattern::Cluster) -> Cluster {
        match c {
            pattern::Cluster::NonRecursive(d) => Cluster::NonRecursive(self.lower_def(d)),
            pattern::Cluster::Recursive(ds) => {
                Cluster::Recursive(ds.into_iter().map(|d| self.lower_def(d)).collect())
            }
        }
    }

    fn lower_def(&mut self, d: pattern::Def) -> Def {
        Def {
            name: d.name,
            expr: self.lower_expr(d.expr),
            ty: d.ty,
            scheme: d.scheme,
        }
    }

    fn lower_expr(&mut self, e: pattern::Expr) -> Expr {
        let ty = e.ty.clone();
        let kind = match e.kind {
            pattern::ExprKind::Match(scrutinee, branches) => {
                return self.compile_match(*scrutinee, branches, ty);
            }

            pattern::ExprKind::Let {
                name,
                scheme,
                val,
                body,
            } => ExprKind::Let {
                name,
                scheme,
                val: Box::new(self.lower_expr(*val)),
                body: Box::new(self.lower_expr(*body)),
            },
            pattern::ExprKind::Lambda {
                param,
                body,
                captures,
            } => ExprKind::Lambda {
                param,
                body: Box::new(self.lower_expr(*body)),
                captures,
            },
            pattern::ExprKind::App(f, a) => {
                ExprKind::App(Box::new(self.lower_expr(*f)), Box::new(self.lower_expr(*a)))
            }
            pattern::ExprKind::If(cond, t, f) => ExprKind::If(
                Box::new(self.lower_expr(*cond)),
                Box::new(self.lower_expr(*t)),
                Box::new(self.lower_expr(*f)),
            ),
            pattern::ExprKind::PairLit(a, b) => {
                ExprKind::PairLit(Box::new(self.lower_expr(*a)), Box::new(self.lower_expr(*b)))
            }
            pattern::ExprKind::Cons(h, t) => {
                ExprKind::Cons(Box::new(self.lower_expr(*h)), Box::new(self.lower_expr(*t)))
            }
            pattern::ExprKind::RecordLit(fields) => {
                let fields = fields
                    .into_iter()
                    .map(|(k, v)| (k, self.lower_expr(v)))
                    .collect();
                ExprKind::RecordLit(fields)
            }
            pattern::ExprKind::Pack {
                tag,
                payload,
                instantiation,
            } => ExprKind::Pack {
                tag,
                payload: payload.map(|p| Box::new(self.lower_expr(*p))),
                instantiation,
            },
            pattern::ExprKind::Var {
                name,
                instantiation,
            } => ExprKind::Var {
                name,
                instantiation,
            },
            pattern::ExprKind::IntLit(i) => ExprKind::IntLit(i),
            pattern::ExprKind::BoolLit(b) => ExprKind::BoolLit(b),
            pattern::ExprKind::UnitLit => ExprKind::UnitLit,
            pattern::ExprKind::FloatLit(f) => ExprKind::FloatLit(f),
            pattern::ExprKind::StringLit(s) => ExprKind::StringLit(s),
            pattern::ExprKind::EmptyListLit => ExprKind::EmptyListLit,
            pattern::ExprKind::Builtin { fun, instantiation } => {
                ExprKind::Builtin { fun, instantiation }
            }
            pattern::ExprKind::FieldAccess(e, field) => {
                ExprKind::FieldAccess(Box::new(self.lower_expr(*e)), field)
            }
            pattern::ExprKind::BinOp(op, l, r) => ExprKind::BinOp(
                op,
                Box::new(self.lower_expr(*l)),
                Box::new(self.lower_expr(*r)),
            ),
            pattern::ExprKind::RecRecord(fields) => {
                let fields = fields
                    .into_iter()
                    .map(|(k, (n, v))| (k, (n, self.lower_expr(v))))
                    .collect();
                ExprKind::RecRecord(fields)
            }
        };

        Expr { kind, ty }
    }

    fn compile_match(
        &mut self,
        scrutinee: pattern::Expr,
        branches: Vec<pattern::MatchBranch>,
        ty: Rc<Type>,
    ) -> Expr {
        let scrutinee_expr = self.lower_expr(scrutinee);

        // Create a fresh variable for the scrutinee to ensure we can reference it
        // multiple times in the decision tree without re-evaluating.
        let root_name = self.new_name();
        let root_var = Expr {
            kind: ExprKind::Var {
                name: root_name,
                instantiation: vec![],
            },
            ty: scrutinee_expr.ty.clone(),
        };

        let scrutinee_scheme = branches
            .first()
            .and_then(|b| b.scrutinee_scheme.clone())
            .unwrap_or_else(|| TypeScheme {
                vars: vec![],
                ty: scrutinee_expr.ty.clone(),
            });

        // Each row starts with 1 pattern (the original branch pattern)
        let matrix = branches
            .into_iter()
            .map(|b| Row {
                patterns: vec![b.pattern],
                body: self.lower_expr(*b.body),
                bindings: Vec::new(),
            })
            .collect();

        // Compile the matrix into a decision tree
        let match_body = self.compile_matrix(vec![root_var], matrix, ty.clone());
        Expr {
            kind: ExprKind::Let {
                name: root_name,
                scheme: scrutinee_scheme,
                val: Box::new(scrutinee_expr),
                body: Box::new(match_body),
            },
            ty,
        }
    }

    fn compile_matrix(
        &mut self,
        scrutinees: Vec<Expr>,
        rows: Vec<Row>,
        result_ty: Rc<Type>,
    ) -> Expr {
        if rows.is_empty() {
            todo!() // Exhaustiveness failure
        }

        // If no scrutinees are left, we have successfully matched a row.
        // Return the body of the first matching row (priority), wrapped in its bindings.
        if scrutinees.is_empty() {
            let row = &rows[0];
            let mut body = row.body.clone();
            // Apply bindings in reverse order (inner to outer)
            for (name, val) in row.bindings.iter().rev() {
                body = Expr {
                    kind: ExprKind::Let {
                        name: *name,
                        scheme: TypeScheme {
                            vars: vec![],
                            ty: val.ty.clone(),
                        },
                        val: Box::new(val.clone()),
                        body: Box::new(body),
                    },
                    ty: result_ty.clone(),
                };
            }
            return body;
        }

        let current_scrutinee = scrutinees[0].clone();

        // Check if the first column is purely variables/wildcards
        let first_col_is_vars = rows.iter().all(|r| {
            matches!(
                r.patterns[0].kind,
                PatternKind::Var(_) | PatternKind::Wildcard
            )
        });

        if first_col_is_vars {
            // The first column matches anything. We bind the variable and proceed.
            let next_scrutinees = scrutinees[1..].to_vec();

            let next_rows = rows
                .into_iter()
                .map(|mut r| {
                    let pat = r.patterns.remove(0);
                    if let PatternKind::Var(name) = pat.kind {
                        r.bindings.push((name, current_scrutinee.clone()));
                    }
                    r
                })
                .collect();

            self.compile_matrix(next_scrutinees, next_rows, result_ty)
        } else {
            //  Constructor specialization. We must branch based on the first column.
            self.compile_constructor_switch(scrutinees, rows, result_ty)
        }
    }

    fn compile_constructor_switch(
        &mut self,
        scrutinees: Vec<Expr>,
        rows: Vec<Row>,
        result_ty: Rc<Type>,
    ) -> Expr {
        let current_scrutinee = scrutinees[0].clone();

        // Peek at the first non-variable pattern to decide the strategy (Switch vs If)
        let head_pattern = rows
            .iter()
            .map(|r| &r.patterns[0])
            .find(|p| !matches!(p.kind, PatternKind::Var(_) | PatternKind::Wildcard))
            .expect("Should have at least one constructor if we reached here");

        match head_pattern.kind {
            PatternKind::Tagged { .. } | PatternKind::Cons(..) | PatternKind::EmptyList => {
                // Tag-based switching
                self.emit_tag_switch(current_scrutinee, scrutinees, rows, result_ty)
            }
            PatternKind::Pair(..) => {
                self.specialize_pair(current_scrutinee, scrutinees, rows, result_ty)
            }
            PatternKind::Unit => {
                self.specialize_unit(current_scrutinee, scrutinees, rows, result_ty)
            }
            PatternKind::Record(_) => {
                self.specialize_record(current_scrutinee, scrutinees, rows, result_ty)
            }
            _ => unreachable!("Should have handled all other patterns."),
        }
    }

    fn specialize_pair(
        &mut self,
        scrutinee: Expr,
        all_scrutinees: Vec<Expr>,
        rows: Vec<Row>,
        result_ty: Rc<Type>,
    ) -> Expr {
        let (left_ty, right_ty) = self.get_pair_types(&scrutinee.ty);

        let mut next_scrutinees = Vec::new();
        next_scrutinees.push(Expr {
            kind: ExprKind::Fst(Box::new(scrutinee.clone())),
            ty: left_ty.clone(),
        });
        next_scrutinees.push(Expr {
            kind: ExprKind::Snd(Box::new(scrutinee.clone())),
            ty: right_ty.clone(),
        });
        next_scrutinees.extend(all_scrutinees[1..].iter().cloned());

        let next_rows = rows
            .into_iter()
            .map(|mut r| {
                let pat = r.patterns.remove(0);
                match pat.kind {
                    PatternKind::Pair(a, b) => {
                        r.patterns.insert(0, *b);
                        r.patterns.insert(0, *a);
                    }
                    PatternKind::Var(_) | PatternKind::Wildcard => {
                        if let PatternKind::Var(name) = pat.kind {
                            r.bindings.push((name, scrutinee.clone()));
                        }
                        r.patterns.insert(
                            0,
                            constructor::Pattern {
                                kind: PatternKind::Wildcard,
                                ty: right_ty.clone(),
                            },
                        );
                        r.patterns.insert(
                            0,
                            constructor::Pattern {
                                kind: PatternKind::Wildcard,
                                ty: left_ty.clone(),
                            },
                        );
                    }
                    _ => unreachable!("Type mismatch in tuple specialization"),
                }
                r
            })
            .collect();

        self.compile_matrix(next_scrutinees, next_rows, result_ty)
    }

    fn specialize_unit(
        &mut self,
        scrutinee: Expr,
        all_scrutinees: Vec<Expr>,
        rows: Vec<Row>,
        result_ty: Rc<Type>,
    ) -> Expr {
        let next_scrutinees = all_scrutinees[1..].to_vec();

        let next_rows = rows
            .into_iter()
            .map(|mut r| {
                let pat = r.patterns.remove(0);
                match pat.kind {
                    PatternKind::Unit => {}
                    PatternKind::Var(name) => {
                        r.bindings.push((name, scrutinee.clone()));
                    }
                    PatternKind::Wildcard => {}
                    _ => unreachable!("Type checker should prevent non-unit/var patterns here"),
                }
                r
            })
            .collect();

        self.compile_matrix(next_scrutinees, next_rows, result_ty)
    }

    fn specialize_record(
        &mut self,
        scrutinee: Expr,
        all_scrutinees: Vec<Expr>,
        rows: Vec<Row>,
        result_ty: Rc<Type>,
    ) -> Expr {
        let mut all_fields = std::collections::BTreeSet::new();
        for row in &rows {
            if let PatternKind::Record(fields) = &row.patterns[0].kind {
                for key in fields.keys() {
                    all_fields.insert(key.clone());
                }
            }
        }

        let mut next_scrutinees = Vec::new();
        let mut field_types = BTreeMap::new();

        for field in &all_fields {
            let ty = rows
                .iter()
                .find_map(|r| match &r.patterns[0].kind {
                    PatternKind::Record(fields) => fields.get(field).map(|p| p.ty.clone()),
                    _ => None,
                })
                .expect("Field collected but not found in any pattern?");

            field_types.insert(field.clone(), ty.clone());

            next_scrutinees.push(Expr {
                kind: ExprKind::FieldAccess(Box::new(scrutinee.clone()), field.clone()),
                ty,
            });
        }

        next_scrutinees.extend(all_scrutinees[1..].iter().cloned());

        let next_rows = rows
            .into_iter()
            .map(|mut r| {
                let pat = r.patterns.remove(0);
                match pat.kind {
                    PatternKind::Record(mut fields) => {
                        // Insert sub-patterns in the same order as next_scrutinees
                        for field in all_fields.iter().rev() {
                            let sub_pat =
                                fields
                                    .remove(field)
                                    .unwrap_or_else(|| constructor::Pattern {
                                        kind: PatternKind::Wildcard,
                                        ty: field_types[field].clone(),
                                    });
                            r.patterns.insert(0, sub_pat);
                        }
                    }
                    PatternKind::Var(name) => {
                        r.bindings.push((name, scrutinee.clone()));
                        for field in all_fields.iter().rev() {
                            r.patterns.insert(
                                0,
                                constructor::Pattern {
                                    kind: PatternKind::Wildcard,
                                    ty: field_types[field].clone(),
                                },
                            );
                        }
                    }
                    PatternKind::Wildcard => {
                        for field in all_fields.iter().rev() {
                            r.patterns.insert(
                                0,
                                constructor::Pattern {
                                    kind: PatternKind::Wildcard,
                                    ty: field_types[field].clone(),
                                },
                            );
                        }
                    }
                    _ => unreachable!("Type mismatch in record specialization"),
                }
                r
            })
            .collect();

        self.compile_matrix(next_scrutinees, next_rows, result_ty)
    }

    fn emit_tag_switch(
        &mut self,
        scrutinee: Expr,
        all_scrutinees: Vec<Expr>,
        rows: Vec<Row>,
        result_ty: Rc<Type>,
    ) -> Expr {
        let mut branches = Vec::new();
        let mut seen_tags = HashSet::new();

        // Collect all unique tags in the current column
        for r in &rows {
            match &r.patterns[0].kind {
                PatternKind::Tagged { tag, .. } => {
                    if seen_tags.insert(*tag) {
                        branches.push(*tag);
                    }
                }
                PatternKind::Cons(..) => {
                    if seen_tags.insert(1) {
                        branches.push(1);
                    } // Cons is tag 1
                }
                PatternKind::EmptyList => {
                    if seen_tags.insert(0) {
                        branches.push(0);
                    } // Empty is tag 0
                }
                _ => {}
            }
        }

        let mut switch_branches = Vec::new();
        for tag in branches {
            // Specialize rows for the tag and retrieve the payload type
            let (specialized_rows, payload_ty) =
                self.specialize_rows_by_tag(tag, &rows, &scrutinee);

            let mut next_scrutinees = Vec::new();
            if let Some(ty) = payload_ty {
                // Create UnpackPayload with the correct type
                next_scrutinees.push(Expr {
                    kind: ExprKind::UnpackPayload(Box::new(scrutinee.clone())),
                    ty,
                });
            }
            next_scrutinees.extend(all_scrutinees[1..].iter().cloned());

            let body = self.compile_matrix(next_scrutinees, specialized_rows, result_ty.clone());
            switch_branches.push(SwitchBranch {
                tag,
                body: Box::new(body),
            });
        }

        let default_rows: Vec<Row> = rows
            .iter()
            .filter(|r| {
                matches!(
                    r.patterns[0].kind,
                    PatternKind::Var(_) | PatternKind::Wildcard
                )
            })
            .cloned()
            .collect();

        let default_body = if !default_rows.is_empty() {
            let next_scrutinees = all_scrutinees[1..].to_vec();
            let next_rows = default_rows
                .into_iter()
                .map(|mut r| {
                    let pat = r.patterns.remove(0);
                    if let PatternKind::Var(name) = pat.kind {
                        r.bindings.push((name, scrutinee.clone()));
                    }
                    r
                })
                .collect();
            Some(Box::new(self.compile_matrix(
                next_scrutinees,
                next_rows,
                result_ty.clone(),
            )))
        } else {
            None
        };

        Expr {
            kind: ExprKind::Switch {
                scrutinee: Box::new(Expr {
                    kind: ExprKind::UnpackTag(Box::new(scrutinee)),
                    ty: Type::simple(INT_TYPE),
                }),
                branches: switch_branches,
                default: default_body,
            },
            ty: result_ty,
        }
    }

    fn specialize_rows_by_tag(
        &self,
        target_tag: u32,
        rows: &[Row],
        scrutinee_expr: &Expr,
    ) -> (Vec<Row>, Option<Rc<Type>>) {
        let mut new_rows = Vec::new();
        let mut payload_ty = None;

        // First pass: find the payload type for this tag from the first matching pattern
        for row in rows {
            match &row.patterns[0].kind {
                PatternKind::Tagged { tag, payload, .. } if *tag == target_tag => {
                    payload_ty = payload.as_ref().map(|p| p.ty.clone());
                    break;
                }
                PatternKind::Cons(..) if target_tag == 1 => {
                    let elem_ty = self.get_list_element_type(&row.patterns[0].ty);
                    payload_ty = Some(Type::new(
                        TypeKind::Pair(elem_ty.clone(), row.patterns[0].ty.clone()),
                        row.patterns[0].ty.kind.clone(),
                    ));
                    break;
                }
                _ => {}
            }
        }

        for row in rows {
            match &row.patterns[0].kind {
                PatternKind::Tagged { tag, payload, .. } if *tag == target_tag => {
                    let mut r = row.clone();
                    r.patterns.remove(0);
                    if let Some(p) = payload {
                        r.patterns.insert(0, *p.clone());
                    }
                    new_rows.push(r);
                }
                PatternKind::Cons(h, t) if target_tag == 1 => {
                    let mut r = row.clone();
                    r.patterns.remove(0);
                    r.patterns.insert(
                        0,
                        constructor::Pattern {
                            kind: PatternKind::Pair(h.clone(), t.clone()),
                            ty: payload_ty.as_ref().unwrap().clone(),
                        },
                    );
                    new_rows.push(r);
                }
                PatternKind::EmptyList if target_tag == 0 => {
                    let mut r = row.clone();
                    r.patterns.remove(0);
                    new_rows.push(r);
                }
                PatternKind::Var(_) | PatternKind::Wildcard => {
                    let mut r = row.clone();
                    let pat = r.patterns.remove(0);
                    if let PatternKind::Var(name) = pat.kind {
                        r.bindings.push((name, scrutinee_expr.clone()));
                    }
                    if let Some(ty) = &payload_ty {
                        r.patterns.insert(
                            0,
                            constructor::Pattern {
                                kind: PatternKind::Wildcard,
                                ty: ty.clone(),
                            },
                        );
                    }
                    new_rows.push(r);
                }
                _ => {}
            }
        }
        (new_rows, payload_ty)
    }

    fn get_pair_types(&self, ty: &Rc<Type>) -> (Rc<Type>, Rc<Type>) {
        match &ty.ty {
            TypeKind::Pair(a, b) => (a.clone(), b.clone()),
            _ => panic!("Expected Pair type, found {:?}", ty),
        }
    }

    /// Helper to extract the element type from a List type.
    /// Assumes List<T> is represented as an App(Con(List), T).
    fn get_list_element_type(&self, ty: &Rc<Type>) -> Rc<Type> {
        match &ty.ty {
            TypeKind::App(_, element_ty) => element_ty.clone(),
            _ => panic!("Expected List type, found {:?}", ty),
        }
    }
}

pub fn lower_crate(c: pattern::Crate) -> Crate {
    let mut compiler = MatchCompiler::new(c.next_name);
    let groups = c
        .groups
        .into_iter()
        .map(|g| compiler.lower_cluster(g))
        .collect();

    Crate {
        crate_id: c.crate_id,
        groups,
        variants: c.variants,
        next_name: compiler.current_name,
    }
}
