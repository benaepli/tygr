use crate::analysis::inference::{
    Type, TypeDisplay, TypeScheme, Typed, TypedDefinition, TypedGroup, TypedKind,
    TypedMatchPattern, TypedPattern, TypedPatternKind, TypedStatement,
};
use crate::analysis::name_table::NameTable;
use std::fmt::Write;

pub struct TypedAstVisualizer<'a> {
    name_table: &'a NameTable,
    indent: usize,
    output: String,
}

impl<'a> TypedAstVisualizer<'a> {
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

    fn type_str(&self, ty: &std::rc::Rc<Type>) -> String {
        TypeDisplay::new(ty.clone(), self.name_table).to_string()
    }

    fn scheme_str(&self, scheme: &TypeScheme) -> String {
        if scheme.vars.is_empty() {
            self.type_str(&scheme.ty)
        } else {
            let vars: Vec<String> = scheme
                .vars
                .iter()
                .map(|(id, _)| format!("{}", id))
                .collect();
            format!("forall {}. {}", vars.join(" "), self.type_str(&scheme.ty))
        }
    }

    fn write_line(&mut self, s: &str) {
        let _ = writeln!(self.output, "{}{}", self.indent_str(), s);
    }

    fn format_instantiation(&self, instantiation: &[std::rc::Rc<Type>]) -> String {
        if instantiation.is_empty() {
            String::new()
        } else {
            let types: Vec<String> = instantiation.iter().map(|t| self.type_str(t)).collect();
            format!("[{}]", types.join(", "))
        }
    }

    pub fn visualize_expr(&mut self, expr: &Typed) -> String {
        self.output.clear();
        self.visit_expr(expr);
        self.output.clone()
    }

    pub fn visualize_statement(&mut self, stmt: &TypedStatement) -> String {
        self.output.clear();
        self.visit_statement(stmt);
        self.output.clone()
    }

    pub fn visualize_group(&mut self, group: &TypedGroup) -> String {
        self.output.clear();
        self.visit_group(group);
        self.output.clone()
    }

    fn visit_group(&mut self, group: &TypedGroup) {
        match group {
            TypedGroup::NonRecursive(def) => {
                self.write_line("NonRecursive:");
                self.indent += 1;
                self.visit_definition(def);
                self.indent -= 1;
            }
            TypedGroup::Recursive(defs) => {
                self.write_line("Recursive:");
                self.indent += 1;
                for def in defs {
                    self.visit_definition(def);
                }
                self.indent -= 1;
            }
        }
    }

    fn visit_definition(&mut self, def: &TypedDefinition) {
        let scheme_str = self.scheme_str(&def.scheme);
        let name_str = self.name_table.lookup_name(&def.name.0);
        self.write_line(&format!("Definition '{}' : {}", name_str, scheme_str));
        self.indent += 1;
        self.visit_expr(&def.expr);
        self.indent -= 1;
    }

    fn visit_statement(&mut self, stmt: &TypedStatement) {
        let scheme_str = self.scheme_str(&stmt.scheme);
        self.write_line(&format!("Statement : {}", scheme_str));
        self.indent += 1;
        self.write_line("pattern:");
        self.indent += 1;
        self.visit_pattern(&stmt.pattern);
        self.indent -= 1;
        if !stmt.bindings.is_empty() {
            self.write_line("bindings:");
            self.indent += 1;
            for (name, scheme) in &stmt.bindings {
                let name_str = self.name_table.lookup_name(name);
                let scheme_str = self.scheme_str(scheme);
                self.write_line(&format!("{} : {}", name_str, scheme_str));
            }
            self.indent -= 1;
        }
        self.write_line("value:");
        self.indent += 1;
        self.visit_expr(&stmt.value);
        self.indent -= 1;
        self.indent -= 1;
    }

    fn visit_pattern(&mut self, pat: &TypedPattern) {
        let ty_str = self.type_str(&pat.ty);
        match &pat.kind {
            TypedPatternKind::Var { name } => {
                let name_str = self.name_table.lookup_name(name);
                self.write_line(&format!("Var({}) : {}", name_str, ty_str));
            }
            TypedPatternKind::Unit => {
                self.write_line(&format!("Unit : {}", ty_str));
            }
            TypedPatternKind::Pair(p1, p2) => {
                self.write_line(&format!("Pair : {}", ty_str));
                self.indent += 1;
                self.visit_pattern(p1);
                self.visit_pattern(p2);
                self.indent -= 1;
            }
            TypedPatternKind::Wildcard => {
                self.write_line(&format!("Wildcard : {}", ty_str));
            }
            TypedPatternKind::Cons(head, tail) => {
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
            TypedPatternKind::EmptyList => {
                self.write_line(&format!("EmptyList : {}", ty_str));
            }
            TypedPatternKind::Record(fields) => {
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
            TypedPatternKind::Constructor(type_name, ctor_name, inner) => {
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

    fn visit_expr(&mut self, expr: &Typed) {
        let ty_str = self.type_str(&expr.ty);
        match &expr.kind {
            TypedKind::Var {
                name,
                instantiation,
            } => {
                let name_str = self.name_table.lookup_name(name);
                let inst_str = self.format_instantiation(instantiation);
                self.write_line(&format!("Var({}){} : {}", name_str, inst_str, ty_str));
            }
            TypedKind::Lambda {
                param,
                body,
                captures,
            } => {
                let captures_str: Vec<_> = captures
                    .iter()
                    .map(|n| self.name_table.lookup_name(n))
                    .collect();
                self.write_line(&format!(
                    "Lambda [captures: {}] : {}",
                    captures_str.join(", "),
                    ty_str
                ));
                self.indent += 1;
                self.write_line("param:");
                self.indent += 1;
                self.visit_pattern(param);
                self.indent -= 1;
                self.write_line("body:");
                self.indent += 1;
                self.visit_expr(body);
                self.indent -= 1;
                self.indent -= 1;
            }
            TypedKind::App(func, arg) => {
                self.write_line(&format!("App : {}", ty_str));
                self.indent += 1;
                self.write_line("func:");
                self.indent += 1;
                self.visit_expr(func);
                self.indent -= 1;
                self.write_line("arg:");
                self.indent += 1;
                self.visit_expr(arg);
                self.indent -= 1;
                self.indent -= 1;
            }
            TypedKind::If(cond, then_branch, else_branch) => {
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
            TypedKind::Match(scrutinee, branches) => {
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
            TypedKind::Block(stmts, result) => {
                self.write_line(&format!("Block : {}", ty_str));
                self.indent += 1;
                for (i, stmt) in stmts.iter().enumerate() {
                    self.write_line(&format!("stmt {}:", i));
                    self.indent += 1;
                    self.visit_statement(stmt);
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
            TypedKind::Cons(head, tail) => {
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
            TypedKind::UnitLit => {
                self.write_line(&format!("UnitLit : {}", ty_str));
            }
            TypedKind::PairLit(first, second) => {
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
            TypedKind::IntLit(i) => {
                self.write_line(&format!("IntLit({}) : {}", i, ty_str));
            }
            TypedKind::FloatLit(f) => {
                self.write_line(&format!("FloatLit({}) : {}", f, ty_str));
            }
            TypedKind::BoolLit(b) => {
                self.write_line(&format!("BoolLit({}) : {}", b, ty_str));
            }
            TypedKind::StringLit(s) => {
                self.write_line(&format!("StringLit({:?}) : {}", s, ty_str));
            }
            TypedKind::EmptyListLit => {
                self.write_line(&format!("EmptyListLit : {}", ty_str));
            }
            TypedKind::RecordLit(fields) => {
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
            TypedKind::BinOp(op, lhs, rhs) => {
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
            TypedKind::RecRecord(fields) => {
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
            TypedKind::FieldAccess(record, field) => {
                self.write_line(&format!("FieldAccess(.{}) : {}", field, ty_str));
                self.indent += 1;
                self.visit_expr(record);
                self.indent -= 1;
            }
            TypedKind::Builtin {
                fun: builtin,
                instantiation,
            } => {
                let inst_str = self.format_instantiation(instantiation);
                self.write_line(&format!("Builtin({:?}){} : {}", builtin, inst_str, ty_str));
            }
            TypedKind::Constructor {
                variant,
                ctor,
                nullary,
                instantiation,
            } => {
                let type_str = self.name_table.lookup_type_name(variant);
                let ctor_str = self.name_table.lookup_name(ctor);
                let nullary_str = if *nullary { " (nullary)" } else { "" };
                let inst_str = self.format_instantiation(instantiation);
                self.write_line(&format!(
                    "Constructor {}::{}{}{} : {}",
                    type_str, ctor_str, nullary_str, inst_str, ty_str
                ));
            }
        }
    }

    fn visit_match_branch(&mut self, branch: &TypedMatchPattern) {
        let ty_str = self.type_str(&branch.ty);
        self.write_line(&format!("MatchBranch : {}", ty_str));
        self.indent += 1;
        self.write_line("pattern:");
        self.indent += 1;
        self.visit_pattern(&branch.pattern);
        self.indent -= 1;
        self.write_line("expr:");
        self.indent += 1;
        self.visit_expr(&branch.expr);
        self.indent -= 1;
        self.indent -= 1;
    }
}

pub fn visualize_typed_ast(expr: &Typed, name_table: &NameTable) -> String {
    let mut visualizer = TypedAstVisualizer::new(name_table);
    visualizer.visualize_expr(expr)
}

pub fn visualize_typed_statement(stmt: &TypedStatement, name_table: &NameTable) -> String {
    let mut visualizer = TypedAstVisualizer::new(name_table);
    visualizer.visualize_statement(stmt)
}

pub fn visualize_typed_group(group: &TypedGroup, name_table: &NameTable) -> String {
    let mut visualizer = TypedAstVisualizer::new(name_table);
    visualizer.visualize_group(group)
}
