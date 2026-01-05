//! AST Visualizer for the decision_tree IR.

use crate::analysis::inference::{Type, TypeDisplay, TypeScheme};
use crate::analysis::name_table::NameTable;
use crate::ir::decision_tree::{Cluster, Crate, Def, Expr, ExprKind, SwitchBranch};
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

pub struct DecisionTreeVisualizer<'a> {
    name_table: &'a NameTable,
    indent: usize,
    output: String,
}

impl<'a> DecisionTreeVisualizer<'a> {
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

    pub fn visualize_crate(&mut self, c: &Crate) -> String {
        self.output.clear();
        self.write_line(&format!("Crate [crate_id: {:?}]", c.crate_id));
        self.indent += 1;
        for (i, cluster) in c.groups.iter().enumerate() {
            self.write_line(&format!("cluster {}:", i));
            self.indent += 1;
            self.visit_cluster(cluster);
            self.indent -= 1;
        }
        self.indent -= 1;
        self.output.clone()
    }

    pub fn visualize_cluster(&mut self, c: &Cluster) -> String {
        self.output.clear();
        self.visit_cluster(c);
        self.output.clone()
    }

    pub fn visualize_expr(&mut self, e: &Expr) -> String {
        self.output.clear();
        self.visit_expr(e);
        self.output.clone()
    }

    fn visit_cluster(&mut self, c: &Cluster) {
        match c {
            Cluster::NonRecursive(def) => {
                self.write_line("NonRecursive:");
                self.indent += 1;
                self.visit_def(def);
                self.indent -= 1;
            }
            Cluster::Recursive(defs) => {
                self.write_line("Recursive:");
                self.indent += 1;
                for def in defs {
                    self.visit_def(def);
                }
                self.indent -= 1;
            }
        }
    }

    fn visit_def(&mut self, d: &Def) {
        let name_str = self.name_table.lookup_name(&d.name);
        let scheme_s = scheme_str(&d.scheme, self.name_table);
        self.write_line(&format!("Def '{}' : {}", name_str, scheme_s));
        self.indent += 1;
        self.visit_expr(&d.expr);
        self.indent -= 1;
    }

    fn visit_expr(&mut self, e: &Expr) {
        let ty_s = type_str(&e.ty, self.name_table);
        match &e.kind {
            ExprKind::Let {
                name,
                scheme,
                val,
                body,
            } => {
                let name_str = self.name_table.lookup_name(name);
                let scheme_s = scheme_str(scheme, self.name_table);
                self.write_line(&format!("Let {} : {}", name_str, scheme_s));
                self.indent += 1;
                self.write_line("val:");
                self.indent += 1;
                self.visit_expr(val);
                self.indent -= 1;
                self.write_line("body:");
                self.indent += 1;
                self.visit_expr(body);
                self.indent -= 1;
                self.indent -= 1;
            }
            ExprKind::Var {
                name,
                instantiation,
            } => {
                let name_str = self.name_table.lookup_name(name);
                let inst_s = format_instantiation(instantiation, self.name_table);
                self.write_line(&format!("Var({}){} : {}", name_str, inst_s, ty_s));
            }
            ExprKind::Lambda {
                param,
                body,
                captures,
            } => {
                let param_str = self.name_table.lookup_name(param);
                let caps: Vec<_> = captures
                    .iter()
                    .map(|n| self.name_table.lookup_name(n))
                    .collect();
                self.write_line(&format!(
                    "Lambda({}) [captures: {}] : {}",
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
            ExprKind::App(f, a) => {
                self.write_line(&format!("App : {}", ty_s));
                self.indent += 1;
                self.write_line("func:");
                self.indent += 1;
                self.visit_expr(f);
                self.indent -= 1;
                self.write_line("arg:");
                self.indent += 1;
                self.visit_expr(a);
                self.indent -= 1;
                self.indent -= 1;
            }
            ExprKind::If(c, t, e) => {
                self.write_line(&format!("If : {}", ty_s));
                self.indent += 1;
                self.write_line("cond:");
                self.indent += 1;
                self.visit_expr(c);
                self.indent -= 1;
                self.write_line("then:");
                self.indent += 1;
                self.visit_expr(t);
                self.indent -= 1;
                self.write_line("else:");
                self.indent += 1;
                self.visit_expr(e);
                self.indent -= 1;
                self.indent -= 1;
            }
            ExprKind::Switch {
                scrutinee,
                branches,
                default,
            } => {
                self.write_line(&format!("Switch : {}", ty_s));
                self.indent += 1;
                self.write_line("scrutinee:");
                self.indent += 1;
                self.visit_expr(scrutinee);
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
            ExprKind::UnitLit => {
                self.write_line(&format!("UnitLit : {}", ty_s));
            }
            ExprKind::PairLit(a, b) => {
                self.write_line(&format!("PairLit : {}", ty_s));
                self.indent += 1;
                self.write_line("first:");
                self.indent += 1;
                self.visit_expr(a);
                self.indent -= 1;
                self.write_line("second:");
                self.indent += 1;
                self.visit_expr(b);
                self.indent -= 1;
                self.indent -= 1;
            }
            ExprKind::IntLit(n) => {
                self.write_line(&format!("IntLit({}) : {}", n, ty_s));
            }
            ExprKind::FloatLit(f) => {
                self.write_line(&format!("FloatLit({}) : {}", f, ty_s));
            }
            ExprKind::BoolLit(b) => {
                self.write_line(&format!("BoolLit({}) : {}", b, ty_s));
            }
            ExprKind::StringLit(s) => {
                self.write_line(&format!("StringLit({:?}) : {}", s, ty_s));
            }
            ExprKind::EmptyListLit => {
                self.write_line(&format!("EmptyListLit : {}", ty_s));
            }
            ExprKind::RecordLit(fields) => {
                self.write_line(&format!("RecordLit : {}", ty_s));
                self.indent += 1;
                for (name, expr) in fields {
                    self.write_line(&format!("field '{}':", name));
                    self.indent += 1;
                    self.visit_expr(expr);
                    self.indent -= 1;
                }
                self.indent -= 1;
            }
            ExprKind::Cons(h, t) => {
                self.write_line(&format!("Cons : {}", ty_s));
                self.indent += 1;
                self.write_line("head:");
                self.indent += 1;
                self.visit_expr(h);
                self.indent -= 1;
                self.write_line("tail:");
                self.indent += 1;
                self.visit_expr(t);
                self.indent -= 1;
                self.indent -= 1;
            }
            ExprKind::BinOp(op, l, r) => {
                self.write_line(&format!("BinOp({:?}) : {}", op, ty_s));
                self.indent += 1;
                self.write_line("lhs:");
                self.indent += 1;
                self.visit_expr(l);
                self.indent -= 1;
                self.write_line("rhs:");
                self.indent += 1;
                self.visit_expr(r);
                self.indent -= 1;
                self.indent -= 1;
            }
            ExprKind::RecRecord(fields) => {
                self.write_line(&format!("RecRecord : {}", ty_s));
                self.indent += 1;
                for (name, (gn, expr)) in fields {
                    let gn_str = self.name_table.lookup_name(gn);
                    self.write_line(&format!("field '{}' (as {}):", name, gn_str));
                    self.indent += 1;
                    self.visit_expr(expr);
                    self.indent -= 1;
                }
                self.indent -= 1;
            }
            ExprKind::FieldAccess(expr, field) => {
                self.write_line(&format!("FieldAccess(.{}) : {}", field, ty_s));
                self.indent += 1;
                self.visit_expr(expr);
                self.indent -= 1;
            }
            ExprKind::Fst(expr) => {
                self.write_line(&format!("Fst : {}", ty_s));
                self.indent += 1;
                self.visit_expr(expr);
                self.indent -= 1;
            }
            ExprKind::Snd(expr) => {
                self.write_line(&format!("Snd : {}", ty_s));
                self.indent += 1;
                self.visit_expr(expr);
                self.indent -= 1;
            }
            ExprKind::Builtin { fun, instantiation } => {
                let inst_s = format_instantiation(instantiation, self.name_table);
                self.write_line(&format!("Builtin({:?}){} : {}", fun, inst_s, ty_s));
            }
            ExprKind::Pack {
                tag,
                payload,
                instantiation,
            } => {
                let inst_s = format_instantiation(instantiation, self.name_table);
                self.write_line(&format!("Pack(tag={}){} : {}", tag, inst_s, ty_s));
                if let Some(p) = payload {
                    self.indent += 1;
                    self.write_line("payload:");
                    self.indent += 1;
                    self.visit_expr(p);
                    self.indent -= 1;
                    self.indent -= 1;
                }
            }
            ExprKind::UnpackTag(expr) => {
                self.write_line(&format!("UnpackTag : {}", ty_s));
                self.indent += 1;
                self.visit_expr(expr);
                self.indent -= 1;
            }
            ExprKind::UnpackPayload(expr) => {
                self.write_line(&format!("UnpackPayload : {}", ty_s));
                self.indent += 1;
                self.visit_expr(expr);
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

// Convenience functions

pub fn visualize_crate(c: &Crate, name_table: &NameTable) -> String {
    let mut v = DecisionTreeVisualizer::new(name_table);
    v.visualize_crate(c)
}

pub fn visualize_expr(e: &Expr, name_table: &NameTable) -> String {
    let mut v = DecisionTreeVisualizer::new(name_table);
    v.visualize_expr(e)
}

pub fn visualize_cluster(c: &Cluster, name_table: &NameTable) -> String {
    let mut v = DecisionTreeVisualizer::new(name_table);
    v.visualize_cluster(c)
}
