use crate::analysis::inference::{Kind, Type, TypeID, TypeKind, TypeScheme};
use crate::analysis::resolver::{GlobalName, Name};
use crate::ir::anf::*;
use std::collections::HashMap;
use std::rc::Rc;

pub struct Program {
    pub decls: Vec<Decl>,
    pub next_name: Name, // Now in the global namespace
    pub main_name: GlobalName,
}

pub fn accumulate(crates: Vec<Crate>, main_name: GlobalName) -> Program {
    let mut decls = Vec::new();
    let mut max_name = Name(0);

    for crate_ in crates {
        decls.extend(crate_.globals);

        if crate_.next_name.krate.is_none() {
            max_name = max_name.max(crate_.next_name.name);
        }
    }

    Program {
        decls,
        next_name: max_name,
        main_name,
    }
}

struct Substitutor {
    // Maps the index of a generic type variable to a concrete type
    mapping: HashMap<TypeID, Rc<Type>>,
}

impl Substitutor {
    fn new(scheme: &TypeScheme, args: &[Rc<Type>]) -> Self {
        let mut mapping = HashMap::new();
        // Bind each generic variable ID from the scheme to the provided concrete type
        for ((id, _), ty) in scheme.vars.iter().zip(args.iter()) {
            mapping.insert(*id, ty.clone());
        }
        Self { mapping }
    }

    fn make(ty: TypeKind) -> Rc<Type> {
        Rc::new(Type {
            ty,
            kind: Rc::new(Kind::Star),
        })
    }

    fn apply(&self, ty: Rc<Type>) -> Rc<Type> {
        match &ty.ty {
            TypeKind::Var(id) => {
                // If this is a generic variable we're substituting, return the concrete type
                self.mapping.get(id).cloned().unwrap_or(ty)
            }
            TypeKind::Con(_) => ty,
            TypeKind::App(lhs, rhs) => Self::make(TypeKind::App(
                self.apply(lhs.clone()),
                self.apply(rhs.clone()),
            )),
            TypeKind::AliasHead(alias, args) => Self::make(TypeKind::AliasHead(
                alias.clone(),
                args.iter().map(|arg| self.apply(arg.clone())).collect(),
            )),
            TypeKind::Function(param, ret) => Self::make(TypeKind::Function(
                self.apply(param.clone()),
                self.apply(ret.clone()),
            )),
            TypeKind::Pair(fst, snd) => Self::make(TypeKind::Pair(
                self.apply(fst.clone()),
                self.apply(snd.clone()),
            )),
            TypeKind::Record(fields) => Self::make(TypeKind::Record(
                fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.apply(ty.clone())))
                    .collect(),
            )),
        }
    }

    fn subst_atom(&self, atom: Atom) -> Atom {
        match atom {
            Atom::Var { name, inst } => Atom::Var {
                name,
                inst: inst.into_iter().map(|t| self.apply(t)).collect(),
            },
            _ => atom,
        }
    }

    fn subst_expr(&self, mut expr: Expr) -> Expr {
        expr.ty = self.apply(expr.ty);
        expr.decls = expr.decls.into_iter().map(|d| self.subst_decl(d)).collect();
        expr.result = self.subst_atom(expr.result);
        expr
    }

    fn subst_decl(&self, decl: Decl) -> Decl {
        match decl {
            Decl::MonoVal { name, ty, expr } => Decl::MonoVal {
                name,
                ty: self.apply(ty),
                expr: self.subst_prim(expr),
            },
            Decl::PolyVal {
                name,
                scheme,
                ty,
                expr,
            } => Decl::PolyVal {
                name,
                scheme,
                ty: self.apply(ty),
                expr: Box::new(self.subst_expr(*expr)),
            },
            Decl::Rec { defs } => Decl::Rec {
                defs: defs.into_iter().map(|d| self.subst_decl(d)).collect(),
            },
        }
    }

    fn subst_prim(&self, prim: PrimExpr) -> PrimExpr {
        match prim {
            PrimExpr::Atom(a) => PrimExpr::Atom(self.subst_atom(a)),
            PrimExpr::Pair { left, right } => PrimExpr::Pair {
                left: self.subst_atom(left),
                right: self.subst_atom(right),
            },
            PrimExpr::Record(fields) => PrimExpr::Record(
                fields
                    .into_iter()
                    .map(|(name, atom)| (name, self.subst_atom(atom)))
                    .collect(),
            ),
            PrimExpr::App { func, arg } => PrimExpr::App {
                func: self.subst_atom(func),
                arg: self.subst_atom(arg),
            },
            PrimExpr::Lambda {
                param,
                param_ty,
                body,
                captures,
            } => PrimExpr::Lambda {
                param,
                param_ty: self.apply(param_ty),
                body: Box::new(self.subst_expr(*body)),
                captures,
            },
            PrimExpr::Pack {
                tag,
                instantiation,
                payload,
            } => PrimExpr::Pack {
                tag,
                instantiation: instantiation.into_iter().map(|t| self.apply(t)).collect(),
                payload: payload.map(|a| self.subst_atom(a)),
            },
            PrimExpr::BinOp(op, left, right) => {
                PrimExpr::BinOp(op, self.subst_atom(left), self.subst_atom(right))
            }
            PrimExpr::Switch {
                scrutinee,
                branches,
                default,
            } => PrimExpr::Switch {
                scrutinee: self.subst_atom(scrutinee),
                branches: branches
                    .into_iter()
                    .map(|b| SwitchBranch {
                        tag: b.tag,
                        body: self.subst_expr(b.body),
                    })
                    .collect(),
                default: default.map(|e| Box::new(self.subst_expr(*e))),
            },
            PrimExpr::If(cond, then_expr, else_expr) => PrimExpr::If(
                self.subst_atom(cond),
                Box::new(self.subst_expr(*then_expr)),
                Box::new(self.subst_expr(*else_expr)),
            ),
            PrimExpr::Cons { head, tail } => PrimExpr::Cons {
                head: self.subst_atom(head),
                tail: self.subst_atom(tail),
            },
            PrimExpr::RecRecord(fields) => PrimExpr::RecRecord(
                fields
                    .into_iter()
                    .map(|(name, (gname, atom))| (name, (gname, self.subst_atom(atom))))
                    .collect(),
            ),
            PrimExpr::FieldAccess(record, field) => {
                PrimExpr::FieldAccess(self.subst_atom(record), field)
            }
            PrimExpr::Fst(atom) => PrimExpr::Fst(self.subst_atom(atom)),
            PrimExpr::Snd(atom) => PrimExpr::Snd(self.subst_atom(atom)),
            PrimExpr::Builtin { fun, instantiation } => PrimExpr::Builtin {
                fun,
                instantiation: instantiation.into_iter().map(|t| self.apply(t)).collect(),
            },
            PrimExpr::UnpackTag(atom) => PrimExpr::UnpackTag(self.subst_atom(atom)),
            PrimExpr::UnpackPayload(atom) => PrimExpr::UnpackPayload(self.subst_atom(atom)),
        }
    }
}

struct Monomorphizer {
    // Stores the original generic code for every PolyVal
    generic_defs: HashMap<GlobalName, Decl>,
    // (Original name, type args) -> specialized type
    cache: HashMap<(GlobalName, Vec<Rc<Type>>), GlobalName>,
    // Requests collected while traversing down
    requests: HashMap<GlobalName, Vec<Vec<Rc<Type>>>>,
    current_name: Name,
}

impl Monomorphizer {
    fn new(name: Name) -> Self {
        Self {
            generic_defs: HashMap::new(),
            cache: HashMap::new(),
            requests: HashMap::new(),
            current_name: name,
        }
    }

    fn new_name(&mut self) -> GlobalName {
        let name = self.current_name;
        self.current_name.0 += 1;
        GlobalName { krate: None, name }
    }

    fn register_decls(&mut self, decls: &[Decl]) {
        for decl in decls {
            match decl {
                Decl::PolyVal { name, .. } => {
                    self.generic_defs.insert(*name, decl.clone());
                    if let Decl::PolyVal { expr, .. } = decl {
                        self.register_expr(expr);
                    }
                }
                Decl::Rec { defs } => {
                    self.register_decls(defs);
                }
                Decl::MonoVal { expr, .. } => {
                    self.register_prim(expr);
                }
            }
        }
    }

    fn register_expr(&mut self, expr: &Expr) {
        self.register_decls(&expr.decls);
    }

    fn register_prim(&mut self, prim: &PrimExpr) {
        match prim {
            PrimExpr::Lambda { body, .. } => self.register_expr(body),
            PrimExpr::If(_, then_e, else_e) => {
                self.register_expr(then_e);
                self.register_expr(else_e);
            }
            PrimExpr::Switch {
                branches, default, ..
            } => {
                for branch in branches {
                    self.register_expr(&branch.body);
                }
                if let Some(def) = default {
                    self.register_expr(def);
                }
            }
            // All other PrimExpr variants don't contain nested Expr, so nothing to register
            PrimExpr::Atom(_)
            | PrimExpr::Pair { .. }
            | PrimExpr::Record(_)
            | PrimExpr::App { .. }
            | PrimExpr::Pack { .. }
            | PrimExpr::BinOp(..)
            | PrimExpr::Cons { .. }
            | PrimExpr::RecRecord(_)
            | PrimExpr::FieldAccess(..)
            | PrimExpr::Fst(_)
            | PrimExpr::Snd(_)
            | PrimExpr::Builtin { .. }
            | PrimExpr::UnpackTag(_)
            | PrimExpr::UnpackPayload(_) => {}
        }
    }

    fn get_specialized_name(&mut self, name: GlobalName, inst: Vec<Rc<Type>>) -> GlobalName {
        if inst.is_empty() {
            return name;
        }

        let key = (name, inst.clone());
        if let Some(&specialized) = self.cache.get(&key) {
            return specialized;
        }

        // Create new name, record request
        let new_name = self.new_name();
        self.cache.insert(key.clone(), new_name);
        self.requests.entry(key.0).or_default().push(key.1);
        new_name
    }

    fn transform_atom(&mut self, atom: Atom) -> Atom {
        match atom {
            Atom::Var { name, inst } => {
                let new_name = self.get_specialized_name(name, inst);
                Atom::Var {
                    name: new_name,
                    inst: Vec::new(),
                }
            }
            _ => atom,
        }
    }

    fn instantiate(&mut self, original_name: GlobalName, type_args: Vec<Rc<Type>>) -> Decl {
        let original_decl = self
            .generic_defs
            .get(&original_name)
            .cloned()
            .expect("Definition missing");

        if let Decl::PolyVal {
            name,
            scheme,
            ty,
            expr,
        } = original_decl
        {
            let specialized_name = *self.cache.get(&(name, type_args.clone())).unwrap();
            let subst = Substitutor::new(&scheme, &type_args);

            let specialized_expr = subst.subst_expr(*expr);
            let specialized_ty = subst.apply(ty);

            // Recursively monomorphize the new body
            let final_expr = self.transform_expr(specialized_expr);

            Decl::PolyVal {
                name: specialized_name,
                scheme: TypeScheme {
                    vars: vec![],
                    ty: specialized_ty.clone(),
                },
                ty: specialized_ty,
                expr: Box::new(final_expr),
            }
        } else {
            panic!("Can only instantiate PolyVal");
        }
    }

    fn transform_prim_expr(&mut self, prim: PrimExpr) -> PrimExpr {
        match prim {
            PrimExpr::Atom(a) => PrimExpr::Atom(self.transform_atom(a)),
            PrimExpr::App { func, arg } => PrimExpr::App {
                func: self.transform_atom(func),
                arg: self.transform_atom(arg),
            },
            PrimExpr::Pair { left, right } => PrimExpr::Pair {
                left: self.transform_atom(left),
                right: self.transform_atom(right),
            },
            PrimExpr::Record(fields) => PrimExpr::Record(
                fields
                    .into_iter()
                    .map(|(name, atom)| (name, self.transform_atom(atom)))
                    .collect(),
            ),
            PrimExpr::Lambda {
                param,
                param_ty,
                body,
                captures,
            } => PrimExpr::Lambda {
                param,
                param_ty,
                body: Box::new(self.transform_expr(*body)),
                captures,
            },
            PrimExpr::Pack {
                tag,
                instantiation: _,
                payload,
            } => PrimExpr::Pack {
                tag,
                instantiation: Vec::new(),
                payload: payload.map(|a| self.transform_atom(a)),
            },
            PrimExpr::BinOp(op, left, right) => {
                PrimExpr::BinOp(op, self.transform_atom(left), self.transform_atom(right))
            }
            PrimExpr::Switch {
                scrutinee,
                branches,
                default,
            } => PrimExpr::Switch {
                scrutinee: self.transform_atom(scrutinee),
                branches: branches
                    .into_iter()
                    .map(|b| SwitchBranch {
                        tag: b.tag,
                        body: self.transform_expr(b.body),
                    })
                    .collect(),
                default: default.map(|e| Box::new(self.transform_expr(*e))),
            },
            PrimExpr::If(cond, then_expr, else_expr) => PrimExpr::If(
                self.transform_atom(cond),
                Box::new(self.transform_expr(*then_expr)),
                Box::new(self.transform_expr(*else_expr)),
            ),
            PrimExpr::Cons { head, tail } => PrimExpr::Cons {
                head: self.transform_atom(head),
                tail: self.transform_atom(tail),
            },
            PrimExpr::RecRecord(fields) => PrimExpr::RecRecord(
                fields
                    .into_iter()
                    .map(|(name, (gname, atom))| (name, (gname, self.transform_atom(atom))))
                    .collect(),
            ),
            PrimExpr::FieldAccess(record, field) => {
                PrimExpr::FieldAccess(self.transform_atom(record), field)
            }
            PrimExpr::Fst(atom) => PrimExpr::Fst(self.transform_atom(atom)),
            PrimExpr::Snd(atom) => PrimExpr::Snd(self.transform_atom(atom)),
            PrimExpr::Builtin {
                fun,
                instantiation: _,
            } => PrimExpr::Builtin {
                fun,
                instantiation: Vec::new(),
            },
            PrimExpr::UnpackTag(atom) => PrimExpr::UnpackTag(self.transform_atom(atom)),
            PrimExpr::UnpackPayload(atom) => PrimExpr::UnpackPayload(self.transform_atom(atom)),
        }
    }

    fn transform_decl(&mut self, decl: Decl) -> Decl {
        match decl {
            Decl::MonoVal { name, ty, expr } => {
                let new_prim_expr = self.transform_prim_expr(expr);
                Decl::MonoVal {
                    name,
                    ty,
                    expr: new_prim_expr,
                }
            }
            Decl::PolyVal { .. } => decl,
            Decl::Rec { defs } => {
                let new_defs = defs.into_iter().map(|d| self.transform_decl(d)).collect();
                Decl::Rec { defs: new_defs }
            }
        }
    }

    fn transform_expr(&mut self, mut expr: Expr) -> Expr {
        let mut new_decls = Vec::new();
        let mut local_poly_defs = Vec::new();
        for decl in expr.decls {
            match decl {
                Decl::PolyVal { name, .. } => {
                    self.generic_defs.insert(name, decl.clone());
                    local_poly_defs.push(name);
                }
                Decl::Rec { defs } => {
                    for sub_decl in defs {
                        if let Decl::PolyVal { name, .. } = sub_decl {
                            self.generic_defs.insert(name, sub_decl.clone());
                            local_poly_defs.push(name);
                        }
                    }
                }
                Decl::MonoVal { .. } => {
                    new_decls.push(self.transform_decl(decl));
                }
            }
        }

        expr.result = self.transform_atom(expr.result);

        loop {
            let mut made_progress = false;
            for &def_name in &local_poly_defs {
                if let Some(inst_list) = self.requests.get_mut(&def_name) {
                    if inst_list.is_empty() {
                        continue;
                    }

                    let batch = std::mem::take(inst_list);

                    for args in batch {
                        let specialized_decl = self.instantiate(def_name, args);
                        new_decls.push(specialized_decl);
                        made_progress = true;
                    }
                }
            }

            if !made_progress {
                break;
            }
        }
        expr.decls = new_decls;
        expr
    }
}

pub fn monomorphize(program: Program) -> Program {
    let mut monomorphizer = Monomorphizer::new(program.next_name);
    monomorphizer.register_decls(&program.decls);
    let mut decls = Vec::new();
    for decl in program.decls.into_iter() {
        decls.push(monomorphizer.transform_decl(decl));
    }
    Program {
        decls,
        main_name: program.main_name,
        next_name: monomorphizer.current_name,
    }
}

#[cfg(test)]
mod test;
