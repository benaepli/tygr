use crate::analysis::inference::{Type, TypeDisplay, TypeID};
use crate::analysis::name_table::NameTable;
use crate::ir::closure::{
    Cluster, Definition, Expr, ExprKind, FuncDef, GlobalDef, MatchBranch, Pattern, PatternKind,
    Program, Stmt, StructDef,
};
use std::fmt::Write;
use std::rc::Rc;

pub struct ClosureIrVisualizer<'a> {
    name_table: &'a NameTable,
    indent: usize,
    output: String,
}

impl<'a> ClosureIrVisualizer<'a> {
    pub fn new(name_table: &'a NameTable) -> Self {
        Self {
            name_table,
            indent: 0,
            output: String::new(),
        }
    }

    fn indent_str(&self) -> String {
        "  ".repeat(self.indent)
    }

    fn type_str(&self, ty: &Rc<Type>) -> String {
        TypeDisplay::new(ty.clone(), self.name_table).to_string()
    }

    fn type_params_str(&self, params: &[TypeID]) -> String {
        if params.is_empty() {
            String::new()
        } else {
            let vars: Vec<String> = params.iter().map(|id| format!("{}", id)).collect();
            format!("[{}]", vars.join(", "))
        }
    }

    fn write_line(&mut self, s: &str) {
        let _ = writeln!(self.output, "{}{}", self.indent_str(), s);
    }

    pub fn visualize_program(&mut self, program: &Program) -> String {
        self.output.clear();
        self.write_line("Program:");
        self.indent += 1;
        for (i, cluster) in program.clusters.iter().enumerate() {
            self.write_line(&format!("cluster {}:", i));
            self.indent += 1;
            self.visit_cluster(cluster);
            self.indent -= 1;
        }
        self.indent -= 1;
        self.output.clone()
    }

    fn visit_cluster(&mut self, cluster: &Cluster) {
        match cluster {
            Cluster::NonRecursive(def) => {
                self.write_line("NonRecursive:");
                self.indent += 1;
                self.visit_definition(def);
                self.indent -= 1;
            }
            Cluster::Recursive(defs) => {
                self.write_line("Recursive:");
                self.indent += 1;
                for def in defs {
                    self.visit_definition(def);
                }
                self.indent -= 1;
            }
        }
    }

    fn visit_definition(&mut self, def: &Definition) {
        match def {
            Definition::Struct(s) => self.visit_struct_def(s),
            Definition::Function(f) => self.visit_func_def(f),
            Definition::Global(g) => self.visit_global_def(g),
        }
    }

    fn visit_struct_def(&mut self, def: &StructDef) {
        let name = self.name_table.lookup_type_name(&def.name);
        let type_params = self.type_params_str(&def.type_params);
        self.write_line(&format!("Struct '{}'{}", name, type_params));
        self.indent += 1;
        for (field_name, field_ty) in &def.fields {
            let field_name_str = self.name_table.lookup_local_name(field_name);
            let ty_str = self.type_str(field_ty);
            self.write_line(&format!("{} : {}", field_name_str, ty_str));
        }
        self.indent -= 1;
    }

    fn visit_func_def(&mut self, def: &FuncDef) {
        let name = self.name_table.lookup_name(&def.name);
        let type_params = self.type_params_str(&def.type_params);
        let param = self.name_table.lookup_local_name(&def.param);
        let env_param = self.name_table.lookup_local_name(&def.env_param);
        let env_struct = self.name_table.lookup_type_name(&def.env_struct);
        let ret_ty = self.type_str(&def.ret_ty);
        self.write_line(&format!(
            "Function '{}'{} (param: {}, env: {} : {}) -> {}",
            name, type_params, param, env_param, env_struct, ret_ty
        ));
        self.indent += 1;
        self.write_line("body:");
        self.indent += 1;
        self.visit_expr(&def.body);
        self.indent -= 1;
        self.indent -= 1;
    }

    fn visit_global_def(&mut self, def: &GlobalDef) {
        let name = self.name_table.lookup_name(&def.name);
        let ty_str = self.type_str(&def.ty);
        self.write_line(&format!("Global '{}' : {}", name, ty_str));
        self.indent += 1;
        self.visit_expr(&def.val);
        self.indent -= 1;
    }

    fn visit_pattern(&mut self, pat: &Pattern) {
        let ty_str = self.type_str(&pat.ty);
        match &pat.kind {
            PatternKind::Var(name) => {
                let name_str = self.name_table.lookup_local_name(name);
                self.write_line(&format!("Var({}) : {}", name_str, ty_str));
            }
            PatternKind::Unit => {
                self.write_line(&format!("Unit : {}", ty_str));
            }
            PatternKind::Pair(p1, p2) => {
                self.write_line(&format!("Pair : {}", ty_str));
                self.indent += 1;
                self.visit_pattern(p1);
                self.visit_pattern(p2);
                self.indent -= 1;
            }
            PatternKind::Wildcard => {
                self.write_line(&format!("Wildcard : {}", ty_str));
            }
            PatternKind::Cons(head, tail) => {
                self.write_line(&format!("Cons : {}", ty_str));
                self.indent += 1;
                self.write_line("head:");
                self.indent += 1;
                self.visit_pattern(head);
                self.indent -= 1;
                self.write_line("tail:");
                self.indent += 1;
                self.visit_pattern(tail);
                self.indent -= 1;
                self.indent -= 1;
            }
            PatternKind::EmptyList => {
                self.write_line(&format!("EmptyList : {}", ty_str));
            }
            PatternKind::Record(fields) => {
                self.write_line(&format!("Record : {}", ty_str));
                self.indent += 1;
                for (name, field_pat) in fields {
                    self.write_line(&format!("field '{}':", name));
                    self.indent += 1;
                    self.visit_pattern(field_pat);
                    self.indent -= 1;
                }
                self.indent -= 1;
            }
            PatternKind::Constructor(type_name, ctor_name, inner) => {
                let type_str = self.name_table.lookup_type_name(type_name);
                let ctor_str = self.name_table.lookup_name(ctor_name);
                self.write_line(&format!(
                    "Constructor {}::{} : {}",
                    type_str, ctor_str, ty_str
                ));
                if let Some(inner) = inner {
                    self.indent += 1;
                    self.visit_pattern(inner);
                    self.indent -= 1;
                }
            }
        }
    }

    fn visit_stmt(&mut self, stmt: &Stmt) {
        self.write_line("Stmt:");
        self.indent += 1;
        self.write_line("pattern:");
        self.indent += 1;
        self.visit_pattern(&stmt.pattern);
        self.indent -= 1;
        self.write_line("value:");
        self.indent += 1;
        self.visit_expr(&stmt.value);
        self.indent -= 1;
        self.indent -= 1;
    }

    fn visit_expr(&mut self, expr: &Expr) {
        let ty_str = self.type_str(&expr.ty);
        match &expr.kind {
            ExprKind::Local(name) => {
                let name_str = self.name_table.lookup_local_name(name);
                self.write_line(&format!("Local({}) : {}", name_str, ty_str));
            }
            ExprKind::Global(name) => {
                let name_str = self.name_table.lookup_name(name);
                self.write_line(&format!("Global({}) : {}", name_str, ty_str));
            }
            ExprKind::EnvAccess { field } => {
                let field_str = self.name_table.lookup_local_name(field);
                self.write_line(&format!("EnvAccess({}) : {}", field_str, ty_str));
            }
            ExprKind::MakeClosure {
                fn_ref,
                env_struct,
                captures,
            } => {
                let fn_name = self.name_table.lookup_name(fn_ref);
                let env_name = self.name_table.lookup_type_name(env_struct);
                self.write_line(&format!(
                    "MakeClosure(fn: {}, env: {}) : {}",
                    fn_name, env_name, ty_str
                ));
                if !captures.is_empty() {
                    self.indent += 1;
                    self.write_line("captures:");
                    self.indent += 1;
                    for (cap_name, cap_expr) in captures {
                        let cap_name_str = self.name_table.lookup_local_name(cap_name);
                        self.write_line(&format!("{}:", cap_name_str));
                        self.indent += 1;
                        self.visit_expr(cap_expr);
                        self.indent -= 1;
                    }
                    self.indent -= 1;
                    self.indent -= 1;
                }
            }
            ExprKind::CallClosure { closure, arg } => {
                self.write_line(&format!("CallClosure : {}", ty_str));
                self.indent += 1;
                self.write_line("closure:");
                self.indent += 1;
                self.visit_expr(closure);
                self.indent -= 1;
                self.write_line("arg:");
                self.indent += 1;
                self.visit_expr(arg);
                self.indent -= 1;
                self.indent -= 1;
            }
            ExprKind::If(cond, then_branch, else_branch) => {
                self.write_line(&format!("If : {}", ty_str));
                self.indent += 1;
                self.write_line("cond:");
                self.indent += 1;
                self.visit_expr(cond);
                self.indent -= 1;
                self.write_line("then:");
                self.indent += 1;
                self.visit_expr(then_branch);
                self.indent -= 1;
                self.write_line("else:");
                self.indent += 1;
                self.visit_expr(else_branch);
                self.indent -= 1;
                self.indent -= 1;
            }
            ExprKind::Match(scrutinee, branches) => {
                self.write_line(&format!("Match : {}", ty_str));
                self.indent += 1;
                self.write_line("scrutinee:");
                self.indent += 1;
                self.visit_expr(scrutinee);
                self.indent -= 1;
                for (i, branch) in branches.iter().enumerate() {
                    self.write_line(&format!("branch {}:", i));
                    self.indent += 1;
                    self.visit_match_branch(branch);
                    self.indent -= 1;
                }
                self.indent -= 1;
            }
            ExprKind::Block(stmts, result) => {
                self.write_line(&format!("Block : {}", ty_str));
                self.indent += 1;
                for (i, stmt) in stmts.iter().enumerate() {
                    self.write_line(&format!("stmt {}:", i));
                    self.indent += 1;
                    self.visit_stmt(stmt);
                    self.indent -= 1;
                }
                if let Some(result_expr) = result {
                    self.write_line("result:");
                    self.indent += 1;
                    self.visit_expr(result_expr);
                    self.indent -= 1;
                }
                self.indent -= 1;
            }
            ExprKind::UnitLit => {
                self.write_line(&format!("UnitLit : {}", ty_str));
            }
            ExprKind::PairLit(first, second) => {
                self.write_line(&format!("PairLit : {}", ty_str));
                self.indent += 1;
                self.write_line("first:");
                self.indent += 1;
                self.visit_expr(first);
                self.indent -= 1;
                self.write_line("second:");
                self.indent += 1;
                self.visit_expr(second);
                self.indent -= 1;
                self.indent -= 1;
            }
            ExprKind::IntLit(i) => {
                self.write_line(&format!("IntLit({}) : {}", i, ty_str));
            }
            ExprKind::FloatLit(f) => {
                self.write_line(&format!("FloatLit({}) : {}", f, ty_str));
            }
            ExprKind::BoolLit(b) => {
                self.write_line(&format!("BoolLit({}) : {}", b, ty_str));
            }
            ExprKind::StringLit(s) => {
                self.write_line(&format!("StringLit({:?}) : {}", s, ty_str));
            }
            ExprKind::EmptyListLit => {
                self.write_line(&format!("EmptyListLit : {}", ty_str));
            }
            ExprKind::RecordLit(fields) => {
                self.write_line(&format!("RecordLit : {}", ty_str));
                self.indent += 1;
                for (name, field_expr) in fields {
                    self.write_line(&format!("field '{}':", name));
                    self.indent += 1;
                    self.visit_expr(field_expr);
                    self.indent -= 1;
                }
                self.indent -= 1;
            }
            ExprKind::Cons(head, tail) => {
                self.write_line(&format!("Cons : {}", ty_str));
                self.indent += 1;
                self.write_line("head:");
                self.indent += 1;
                self.visit_expr(head);
                self.indent -= 1;
                self.write_line("tail:");
                self.indent += 1;
                self.visit_expr(tail);
                self.indent -= 1;
                self.indent -= 1;
            }
            ExprKind::BinOp(op, lhs, rhs) => {
                self.write_line(&format!("BinOp({:?}) : {}", op, ty_str));
                self.indent += 1;
                self.write_line("lhs:");
                self.indent += 1;
                self.visit_expr(lhs);
                self.indent -= 1;
                self.write_line("rhs:");
                self.indent += 1;
                self.visit_expr(rhs);
                self.indent -= 1;
                self.indent -= 1;
            }
            ExprKind::RecRecord(fields) => {
                self.write_line(&format!("RecRecord : {}", ty_str));
                self.indent += 1;
                for (name, (name_id, field_expr)) in fields {
                    let name_str = self.name_table.lookup_name(name_id);
                    self.write_line(&format!("field '{}' (bound as {}):", name, name_str));
                    self.indent += 1;
                    self.visit_expr(field_expr);
                    self.indent -= 1;
                }
                self.indent -= 1;
            }
            ExprKind::FieldAccess(record, field) => {
                self.write_line(&format!("FieldAccess(.{}) : {}", field, ty_str));
                self.indent += 1;
                self.visit_expr(record);
                self.indent -= 1;
            }
            ExprKind::Builtin(builtin) => {
                self.write_line(&format!("Builtin({:?}) : {}", builtin, ty_str));
            }
            ExprKind::Constructor {
                variant,
                ctor,
                nullary,
            } => {
                let type_str = self.name_table.lookup_type_name(variant);
                let ctor_str = self.name_table.lookup_name(ctor);
                let nullary_str = if *nullary { " (nullary)" } else { "" };
                self.write_line(&format!(
                    "Constructor {}::{}{} : {}",
                    type_str, ctor_str, nullary_str, ty_str
                ));
            }
        }
    }

    fn visit_match_branch(&mut self, branch: &MatchBranch) {
        self.write_line("MatchBranch:");
        self.indent += 1;
        self.write_line("pattern:");
        self.indent += 1;
        self.visit_pattern(&branch.pattern);
        self.indent -= 1;
        self.write_line("body:");
        self.indent += 1;
        self.visit_expr(&branch.body);
        self.indent -= 1;
        self.indent -= 1;
    }
}

pub fn visualize_closure_ir(program: &Program, name_table: &NameTable) -> String {
    let mut visualizer = ClosureIrVisualizer::new(name_table);
    visualizer.visualize_program(program)
}
