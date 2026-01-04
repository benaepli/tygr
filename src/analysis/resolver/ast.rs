use crate::analysis::resolver::ResolutionError;
use crate::builtin::BuiltinFn;
use crate::driver::{DfsScope, ModuleId};
use crate::parser::{BinOp, Definition, Path, PathBase, Span, TypeAlias, Variant, Visibility};
use js_sys::WebAssembly::Global;
use petgraph::graph::DiGraph;
use petgraph::prelude::NodeIndex;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub struct Name(pub usize);

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize, PartialOrd, Ord,
)]
pub struct TypeName(pub usize);

impl fmt::Display for TypeName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedConstructor {
    pub name: GlobalName,
    pub annotation: Option<ResolvedAnnotation>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedVariant {
    pub name: GlobalType,
    pub type_params: Vec<GlobalType>,
    pub constructors: HashMap<GlobalName, ResolvedConstructor>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ResolvedDefinition {
    pub name: (GlobalName, String),
    pub expr: Box<Resolved>,
    pub type_params: Vec<GlobalType>,
    pub annotation: Option<ResolvedAnnotation>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ResolvedValueDefinition {
    Constructor(TypeName),
    Definition(ResolvedDefinition),
}

pub type GlobalType = (Option<CrateId>, TypeName);
pub type GlobalName = (Option<CrateId>, Name);

#[derive(Debug, Clone, PartialEq)]
pub enum ResolvedPatternKind {
    Var(GlobalName),
    Unit,
    Pair(Box<ResolvedPattern>, Box<ResolvedPattern>),
    Wildcard,
    Cons(Box<ResolvedPattern>, Box<ResolvedPattern>),
    EmptyList,
    Record(HashMap<String, ResolvedPattern>),
    Constructor(GlobalType, GlobalName, Option<Box<ResolvedPattern>>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedPattern {
    pub kind: ResolvedPatternKind,
    pub span: Span,
}

impl ResolvedPattern {
    pub fn new(kind: ResolvedPatternKind, span: Span) -> Self {
        ResolvedPattern { kind, span }
    }
}

#[derive(Debug, Clone)]
pub struct ResolvedMatchBranch {
    pub pattern: ResolvedPattern,
    pub expr: Box<Resolved>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Resolved {
    pub kind: ResolvedKind,
    pub span: Span,
}

impl Resolved {
    pub fn new(kind: ResolvedKind, span: Span) -> Self {
        Resolved { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ResolvedAnnotationKind {
    Var(GlobalType),
    Alias(GlobalType),
    App(Box<ResolvedAnnotation>, Box<ResolvedAnnotation>),
    Pair(Box<ResolvedAnnotation>, Box<ResolvedAnnotation>),
    Lambda(Box<ResolvedAnnotation>, Box<ResolvedAnnotation>),
    Record(HashMap<String, ResolvedAnnotation>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedAnnotation {
    pub kind: ResolvedAnnotationKind,
    pub span: Span,
}

impl ResolvedAnnotation {
    pub fn new(kind: ResolvedAnnotationKind, span: Span) -> Self {
        ResolvedAnnotation { kind, span }
    }
}

#[derive(Debug, Clone)]
pub struct ResolvedStatement {
    pub pattern: ResolvedPattern,
    pub value: Box<Resolved>,
    pub value_type: Option<ResolvedAnnotation>,
    pub type_params: Vec<TypeName>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ResolvedKind {
    Var(GlobalName),
    Lambda {
        param: ResolvedPattern,
        body: Box<Resolved>,
        captures: HashSet<GlobalName>,
        param_type: Option<ResolvedAnnotation>,
    },
    App(Box<Resolved>, Box<Resolved>),
    If(Box<Resolved>, Box<Resolved>, Box<Resolved>),
    Match(Box<Resolved>, Vec<ResolvedMatchBranch>),
    Block(Vec<ResolvedStatement>, Option<Box<Resolved>>),
    Cons(Box<Resolved>, Box<Resolved>),

    UnitLit,
    PairLit(Box<Resolved>, Box<Resolved>),
    IntLit(i64),
    FloatLit(f64),
    BoolLit(bool),
    StringLit(String),
    EmptyListLit,
    RecordLit(HashMap<String, Resolved>),

    BinOp(BinOp, Box<Resolved>, Box<Resolved>),
    RecRecord(HashMap<String, (GlobalName, Resolved)>),
    FieldAccess(Box<Resolved>, String),

    Builtin(BuiltinFn),
    Constructor(GlobalType, GlobalName),
}

impl ResolvedKind {
    pub fn is_syntactic_value(&self) -> bool {
        match self {
            ResolvedKind::Var(_)
            | ResolvedKind::Lambda { .. }
            | ResolvedKind::IntLit(_)
            | ResolvedKind::FloatLit(_)
            | ResolvedKind::BoolLit(_)
            | ResolvedKind::StringLit(_)
            | ResolvedKind::UnitLit
            | ResolvedKind::EmptyListLit
            | ResolvedKind::Constructor(_, _) => true,

            ResolvedKind::PairLit(a, b) => {
                a.kind.is_syntactic_value() && b.kind.is_syntactic_value()
            }
            ResolvedKind::Cons(h, t) => h.kind.is_syntactic_value() && t.kind.is_syntactic_value(),
            ResolvedKind::RecordLit(fields) => fields.values().all(|v| v.kind.is_syntactic_value()),

            ResolvedKind::App(_, _)
            | ResolvedKind::If(_, _, _)
            | ResolvedKind::Match(_, _)
            | ResolvedKind::Block(_, _)
            | ResolvedKind::BinOp(_, _, _)
            | ResolvedKind::Builtin(_)
            | ResolvedKind::FieldAccess(_, _) => false,
            ResolvedKind::RecRecord(_) => true,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ResolvedTypeAlias {
    pub name: GlobalType,
    pub type_params: Vec<GlobalType>,
    pub body: ResolvedAnnotation,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedModuleData {
    pub id: ModuleId,
    pub parent: Option<ModuleId>,

    pub definitions: HashMap<String, (CrateId, Name, Visibility)>,
    pub types: HashMap<String, (CrateId, TypeName, Visibility)>,
    pub modules: HashMap<String, (CrateId, ModuleId, Visibility)>,

    pub scope: DfsScope,
}

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize, PartialOrd, Ord,
)]
pub struct CrateId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Resolution {
    Def(CrateId, Name),
    Type(CrateId, TypeName),
    Module(CrateId, ModuleId),
}

pub struct CrateGraph {
    pub graph: DiGraph<CrateDefMap, String>, // Edges contain the dependency alias
    pub index_map: HashMap<NodeIndex, String>, // The canonical names of crates
}

impl CrateGraph {
    pub fn new() -> Self {
        Self {
            graph: DiGraph::new(),
            index_map: HashMap::new(),
        }
    }

    pub fn add_crate(&mut self, name: &str, data: CrateDefMap) -> CrateId {
        let idx = self.graph.add_node(data);
        self.index_map.insert(idx, name.to_string());
        CrateId(idx.index())
    }

    pub fn add_dependency(&mut self, from: CrateId, to: CrateId, alias: String) {
        self.graph
            .add_edge(NodeIndex::new(from.0), NodeIndex::new(to.0), alias);
    }
}

#[derive(Debug, Clone)]
pub enum ResolvedTypeDefinition {
    Variant(ResolvedVariant),
    Alias(ResolvedTypeAlias),
}

pub type ExternPrelude = HashMap<String, CrateId>;

#[derive(Debug, Clone)]
pub struct UnresolvedImport {
    pub module_id: ModuleId,
    pub path: Path,
    pub alias: Option<String>,
    pub vis: Visibility,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct CrateDefMap {
    pub crate_id: CrateId,
    pub modules: HashMap<ModuleId, ResolvedModuleData>,
    pub root: ModuleId,

    pub extern_prelude: ExternPrelude,

    pub definitions: HashMap<Name, ResolvedDefinition>,
    pub types: HashMap<TypeName, ResolvedTypeDefinition>,

    pub defs_to_resolve: HashMap<Name, (Definition, ModuleId)>,
    pub variants_to_resolve: HashMap<TypeName, (Variant, ModuleId)>,
    pub aliases_to_resolve: HashMap<TypeName, (TypeAlias, ModuleId)>,
    pub unresolved_imports: Vec<UnresolvedImport>,
}

pub enum Namespace {
    Type,
    Value,
}

#[derive(Debug, Clone, Default)]
pub struct World {
    crates: HashMap<CrateId, CrateDefMap>,
}

impl World {
    pub fn resolve(
        &self,
        start_crate: CrateId,
        start_module: ModuleId,
        mut path: Path,
        target_namespace: Namespace,
    ) -> Result<Resolution, ResolutionError> {
        let mut current_crate = start_crate;
        let mut current_module = start_module;
        match path.base {
            Some(PathBase::Crate) => {
                current_module = self.crates[&current_crate].root;
            }
            Some(PathBase::Super(n)) => {
                for _ in 0..n {
                    let mod_data = &self.crates[&current_crate].modules[&current_module];
                    if let Some(parent) = mod_data.parent {
                        current_module = parent;
                    } else {
                        todo!()
                    }
                }
            }
            None => {
                if let Some(extern_crate_id) = self.crates[&current_crate]
                    .extern_prelude
                    .get(path.segments.get(0).expect("path must have one segment"))
                {
                    current_crate = *extern_crate_id;
                    current_module = self.crates[extern_crate_id].root;
                    path.segments.remove(0);
                }
            }
        }

        let segment_count = path.segments.len();
        for (index, segment_name) in path.segments.iter().enumerate() {
            let is_last_segment = index == segment_count - 1;
            let mod_data = &self.crates[&current_crate].modules[&current_module];
            if is_last_segment {
                match target_namespace {
                    Namespace::Value => {
                        if let Some((c, id, vis)) = mod_data.definitions.get(segment_name) {
                            self.check_visibility(
                                vis,
                                *c,
                                current_module,
                                start_crate,
                                start_module,
                            )?;
                            return Ok(Resolution::Def(*c, *id));
                        }
                    }
                    Namespace::Type => {
                        if let Some((c, id, vis)) = mod_data.types.get(segment_name) {
                            self.check_visibility(
                                vis,
                                *c,
                                current_module,
                                start_crate,
                                start_module,
                            )?;
                            return Ok(Resolution::Type(*c, *id));
                        }
                    }
                }
                todo!()
            } else {
                if let Some((next_crate, next_mod_id, vis)) = mod_data.modules.get(segment_name) {
                    self.check_visibility(
                        vis,
                        *next_crate,
                        *next_mod_id,
                        start_crate,
                        start_module,
                    )?;
                    current_crate = *next_crate;
                    current_module = *next_mod_id;
                } else {
                    todo!()
                }
            }
        }

        todo!()
    }

    fn check_visibility(
        &self,
        vis: &Visibility,
        def_crate: CrateId,
        def_module: ModuleId,
        user_crate: CrateId,
        user_module: ModuleId,
    ) -> Result<(), ResolutionError> {
        match vis {
            Visibility::Public => Ok(()),
            Visibility::Private => {
                if def_crate != user_crate {
                    todo!()
                }
                let def_scope = self.crates[&def_crate].modules[&def_module].scope;
                let user_scope = self.crates[&user_crate].modules[&user_module].scope;

                if def_scope.entry <= user_scope.entry && def_scope.exit >= user_scope.exit {
                    Ok(())
                } else {
                    todo!()
                }
            }
        }
    }
}
