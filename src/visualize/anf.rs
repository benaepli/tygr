//! AST Visualizer for the ANF IR.

use crate::analysis::inference::{Type, TypeDisplay, TypeScheme};
use crate::analysis::name_table::NameTable;
use crate::analysis::resolver::GlobalName;
use crate::ir::anf::{Atom, Crate, Decl, Expr, PrimExpr, SwitchBranch};
use crate::ir::monomorphization::Program;
use std::fmt::Write;
use std::rc::Rc;

fn indent_str(indent: usize) -> String {
    "  ".repeat(indent)
}

fn type_str(ty: &Rc<Type>, name_table: &NameTable) -> String {
    TypeDisplay::new(ty.clone(), name_table).to_string()
}

fn scheme_str(scheme: &TypeScheme, name_table: &NameTable) -> String {
    if scheme.vars.is_empty() {
        type_str(&scheme.ty, name_table)
    } else {
        let vars: Vec<String> = scheme
            .vars
            .iter()
            .map(|(id, _)| format!("{}", id))
            .collect();
        format!(
            "forall {}. {}",
            vars.join(" "),
            type_str(&scheme.ty, name_table)
        )
    }
}

fn format_instantiation(instantiation: &[Rc<Type>], name_table: &NameTable) -> String {
    if instantiation.is_empty() {
        String::new()
    } else {
        let types: Vec<String> = instantiation
            .iter()
            .map(|t| type_str(t, name_table))
            .collect();
        format!("[{}]", types.join(", "))
    }
}

pub struct AnfVisualizer<'a> {
    name_table: &'a NameTable,
    indent: usize,
    output: String,
}

impl<'a> AnfVisualizer<'a> {
    pub fn new(name_table: &'a NameTable) -> Self {
        Self {
            name_table,
            indent: 0,
            output: String::new(),
        }
    }

    fn write_line(&mut self, s: &str) {
        let _ = writeln!(self.output, "{}{}", indent_str(self.indent), s);
    }

    fn resolve_name(&self, name: GlobalName) -> String {
        let s = self.name_table.lookup_name(&name);
        if s.starts_with("<name:") && s.ends_with(">") {
            // Extract ID from <name:ID>
            let id_str = &s[6..s.len() - 1];
            format!("_tmp{}", id_str)
        } else {
            s
        }
    }

    pub fn visualize_crate(&mut self, c: &Crate) -> String {
        self.output.clear();
        self.write_line(&format!("Crate [crate_id: {:?}]", c.crate_id));
        self.indent += 1;
        for (i, decl) in c.globals.iter().enumerate() {
            self.write_line(&format!("global decl {}:", i));
            self.indent += 1;
            self.visit_decl(decl);
            self.indent -= 1;
        }
        self.indent -= 1;
        self.output.clone()
    }

    pub fn visualize_program(&mut self, p: &Program) -> String {
        self.output.clear();
        self.write_line("Program (monomorphized)");
        self.indent += 1;
        self.write_line(&format!("main: {}", self.resolve_name(p.main_name)));
        for (i, decl) in p.decls.iter().enumerate() {
            self.write_line(&format!("global decl {}:", i));
            self.indent += 1;
            self.visit_decl(decl);
            self.indent -= 1;
        }
        self.indent -= 1;
        self.output.clone()
    }

    pub fn visualize_expr(&mut self, e: &Expr) -> String {
        self.output.clear();
        self.visit_expr(e);
        self.output.clone()
    }

    fn visit_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::MonoVal { name, ty, expr } => {
                let name_str = self.resolve_name(*name);
                let ty_s = type_str(ty, self.name_table);
                self.write_line(&format!("MonoVal {} : {}", name_str, ty_s));
                self.indent += 1;
                self.visit_prim_expr(expr);
                self.indent -= 1;
            }
            Decl::PolyVal {
                name,
                scheme,
                ty: _,
                expr,
            } => {
                let name_str = self.resolve_name(*name);
                let scheme_s = scheme_str(scheme, self.name_table);
                self.write_line(&format!("PolyVal {} : {}", name_str, scheme_s));
                self.indent += 1;
                self.visit_expr(expr);
                self.indent -= 1;
            }
            Decl::Rec { defs } => {
                self.write_line("Rec:");
                self.indent += 1;
                for def in defs {
                    self.visit_decl(def);
                }
                self.indent -= 1;
            }
        }
    }

    fn visit_expr(&mut self, e: &Expr) {
        let ty_s = type_str(&e.ty, self.name_table);
        self.write_line(&format!("Expr : {}", ty_s));
        self.indent += 1;

        if !e.decls.is_empty() {
            self.write_line("decls:");
            self.indent += 1;
            for decl in &e.decls {
                self.visit_decl(decl);
            }
            self.indent -= 1;
        }

        self.write_line("result:");
        self.indent += 1;
        self.visit_atom(&e.result);
        self.indent -= 1;

        self.indent -= 1;
    }

    fn visit_atom(&mut self, atom: &Atom) {
        match atom {
            Atom::Var { name, inst } => {
                let name_str = self.resolve_name(*name);
                let inst_s = format_instantiation(inst, self.name_table);
                self.write_line(&format!("Var({}){}", name_str, inst_s));
            }
            Atom::IntLit(i) => self.write_line(&format!("IntLit({})", i)),
            Atom::BoolLit(b) => self.write_line(&format!("BoolLit({})", b)),
            Atom::FloatLit(f) => self.write_line(&format!("FloatLit({})", f)),
            Atom::StringLit(s) => self.write_line(&format!("StringLit({:?})", s)),
            Atom::UnitLit => self.write_line("UnitLit"),
            Atom::EmptyListLit => self.write_line("EmptyListLit"),
        }
    }

    fn visit_prim_expr(&mut self, expr: &PrimExpr) {
        match expr {
            PrimExpr::Atom(atom) => {
                self.write_line("Atom:");
                self.indent += 1;
                self.visit_atom(atom);
                self.indent -= 1;
            }
            PrimExpr::Pair { left, right } => {
                self.write_line("Pair:");
                self.indent += 1;
                self.write_line("left:");
                self.indent += 1;
                self.visit_atom(left);
                self.indent -= 1;
                self.write_line("right:");
                self.indent += 1;
                self.visit_atom(right);
                self.indent -= 1;
                self.indent -= 1;
            }
            PrimExpr::Record(fields) => {
                self.write_line("Record:");
                self.indent += 1;
                for (name, atom) in fields {
                    self.write_line(&format!("field '{}':", name));
                    self.indent += 1;
                    self.visit_atom(atom);
                    self.indent -= 1;
                }
                self.indent -= 1;
            }
            PrimExpr::App { func, arg } => {
                self.write_line("App:");
                self.indent += 1;
                self.write_line("func:");
                self.indent += 1;
                self.visit_atom(func);
                self.indent -= 1;
                self.write_line("arg:");
                self.indent += 1;
                self.visit_atom(arg);
                self.indent -= 1;
                self.indent -= 1;
            }
            PrimExpr::Lambda {
                param,
                param_ty,
                body,
                captures,
            } => {
                let param_str = self.resolve_name(*param);
                let ty_s = type_str(param_ty, self.name_table);
                let caps: Vec<_> = captures.iter().map(|n| self.resolve_name(*n)).collect();
                self.write_line(&format!(
                    "Lambda({}) [captures: {}] : param_ty={}",
                    param_str,
                    caps.join(", "),
                    ty_s
                ));
                self.indent += 1;
                self.write_line("body:");
                self.indent += 1;
                self.visit_expr(body);
                self.indent -= 1;
                self.indent -= 1;
            }
            PrimExpr::Pack {
                tag,
                instantiation,
                payload,
            } => {
                let inst_s = format_instantiation(instantiation, self.name_table);
                self.write_line(&format!("Pack(tag={}){}", tag, inst_s));
                if let Some(atom) = payload {
                    self.indent += 1;
                    self.write_line("payload:");
                    self.indent += 1;
                    self.visit_atom(atom);
                    self.indent -= 1;
                    self.indent -= 1;
                }
            }
            PrimExpr::BinOp(op, left, right) => {
                self.write_line(&format!("BinOp({:?}):", op));
                self.indent += 1;
                self.write_line("lhs:");
                self.indent += 1;
                self.visit_atom(left);
                self.indent -= 1;
                self.write_line("rhs:");
                self.indent += 1;
                self.visit_atom(right);
                self.indent -= 1;
                self.indent -= 1;
            }
            PrimExpr::Switch {
                scrutinee,
                branches,
                default,
            } => {
                self.write_line("Switch:");
                self.indent += 1;
                self.write_line("scrutinee:");
                self.indent += 1;
                self.visit_atom(scrutinee);
                self.indent -= 1;
                for branch in branches {
                    self.visit_switch_branch(branch);
                }
                if let Some(def) = default {
                    self.write_line("default:");
                    self.indent += 1;
                    self.visit_expr(def);
                    self.indent -= 1;
                }
                self.indent -= 1;
            }
            PrimExpr::If(cond, then_br, else_br) => {
                self.write_line("If:");
                self.indent += 1;
                self.write_line("cond:");
                self.indent += 1;
                self.visit_atom(cond);
                self.indent -= 1;
                self.write_line("then:");
                self.indent += 1;
                self.visit_expr(then_br);
                self.indent -= 1;
                self.write_line("else:");
                self.indent += 1;
                self.visit_expr(else_br);
                self.indent -= 1;
                self.indent -= 1;
            }
            PrimExpr::Cons { head, tail } => {
                self.write_line("Cons:");
                self.indent += 1;
                self.write_line("head:");
                self.indent += 1;
                self.visit_atom(head);
                self.indent -= 1;
                self.write_line("tail:");
                self.indent += 1;
                self.visit_atom(tail);
                self.indent -= 1;
                self.indent -= 1;
            }
            PrimExpr::RecRecord(fields) => {
                self.write_line("RecRecord:");
                self.indent += 1;
                for (name, (gn, atom)) in fields {
                    let gn_str = self.resolve_name(*gn);
                    self.write_line(&format!("field '{}' (as {}):", name, gn_str));
                    self.indent += 1;
                    self.visit_atom(atom);
                    self.indent -= 1;
                }
                self.indent -= 1;
            }
            PrimExpr::FieldAccess(atom, field) => {
                self.write_line(&format!("FieldAccess(.{}):", field));
                self.indent += 1;
                self.visit_atom(atom);
                self.indent -= 1;
            }
            PrimExpr::Fst(atom) => {
                self.write_line("Fst:");
                self.indent += 1;
                self.visit_atom(atom);
                self.indent -= 1;
            }
            PrimExpr::Snd(atom) => {
                self.write_line("Snd:");
                self.indent += 1;
                self.visit_atom(atom);
                self.indent -= 1;
            }
            PrimExpr::Builtin { fun, instantiation } => {
                let inst_s = format_instantiation(instantiation, self.name_table);
                self.write_line(&format!("Builtin({:?}){}", fun, inst_s));
            }
            PrimExpr::UnpackTag(atom) => {
                self.write_line("UnpackTag:");
                self.indent += 1;
                self.visit_atom(atom);
                self.indent -= 1;
            }
            PrimExpr::UnpackPayload(atom) => {
                self.write_line("UnpackPayload:");
                self.indent += 1;
                self.visit_atom(atom);
                self.indent -= 1;
            }
        }
    }

    fn visit_switch_branch(&mut self, b: &SwitchBranch) {
        self.write_line(&format!("case {}:", b.tag));
        self.indent += 1;
        self.visit_expr(&b.body);
        self.indent -= 1;
    }
}

pub fn visualize_crate(c: &Crate, name_table: &NameTable) -> String {
    let mut v = AnfVisualizer::new(name_table);
    v.visualize_crate(c)
}

pub fn visualize_program(p: &Program, name_table: &NameTable) -> String {
    let mut v = AnfVisualizer::new(name_table);
    v.visualize_program(p)
}
