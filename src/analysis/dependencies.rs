use crate::analysis::resolver::{GlobalName, Resolved, ResolvedDefinition, ResolvedKind};
use petgraph::algo::tarjan_scc;
use petgraph::graph::DiGraph;
use std::collections::{HashMap, HashSet};

pub fn is_self_recursive(def: &ResolvedDefinition) -> bool {
    get_dependencies(&def.expr).contains(&def.name.0)
}

pub fn reorder_definitions(defs: Vec<ResolvedDefinition>) -> Vec<Vec<ResolvedDefinition>> {
    let scc_indices = compute_sccs(&defs);
    let mut defs_opts: Vec<Option<ResolvedDefinition>> = defs.into_iter().map(Some).collect();

    scc_indices
        .into_iter()
        .map(|group_indices| {
            group_indices
                .into_iter()
                .map(|index| {
                    defs_opts[index]
                        .take()
                        .expect("Definition matched more than once or index out of bounds")
                })
                .collect()
        })
        .collect()
}

/// Computes the Strongly Connected Components (SCCs) of the given definitions.
///
/// Returns a list of groups, where each group contains the indices of the definitions
/// in that component. The groups are returned in reverse topological order,
/// meaning dependencies appear before the definitions that use them.
pub fn compute_sccs(defs: &[ResolvedDefinition]) -> Vec<Vec<usize>> {
    let mut graph = DiGraph::<usize, ()>::new();
    let mut name_to_node = HashMap::new();

    // Create a node for every definition
    for (index, def) in defs.iter().enumerate() {
        let node = graph.add_node(index);
        name_to_node.insert(def.name.0, node);
    }

    // Edge A -> B means A depends on B.
    for (_, def) in defs.iter().enumerate() {
        let source_node = name_to_node[&def.name.0];
        let dependencies = get_dependencies(&def.expr);

        for dep_name in dependencies {
            if let Some(&target_node) = name_to_node.get(&dep_name) {
                graph.add_edge(source_node, target_node, ());
            }
        }
    }
    let sccs = tarjan_scc(&graph);
    sccs.into_iter()
        .map(|component| {
            component
                .into_iter()
                .map(|node| *graph.node_weight(node).unwrap())
                .collect()
        })
        .collect()
}

/// Recursively finds all free variables (dependencies) in a resolved expression.
fn get_dependencies(expr: &Resolved) -> HashSet<GlobalName> {
    match &expr.kind {
        ResolvedKind::Var(name) => {
            let mut set = HashSet::new();
            set.insert(*name);
            set
        }
        ResolvedKind::Lambda { body, .. } => get_dependencies(body),
        ResolvedKind::App(f, a)
        | ResolvedKind::BinOp(_, f, a)
        | ResolvedKind::Cons(f, a)
        | ResolvedKind::PairLit(f, a) => {
            let mut set = get_dependencies(f);
            set.extend(get_dependencies(a));
            set
        }
        ResolvedKind::If(c, t, e) => {
            let mut set = get_dependencies(c);
            set.extend(get_dependencies(t));
            set.extend(get_dependencies(e));
            set
        }
        ResolvedKind::Match(head, branches) => {
            let mut set = get_dependencies(head);
            for branch in branches {
                set.extend(get_dependencies(&branch.expr));
            }
            set
        }
        ResolvedKind::Block(stmts, tail) => {
            let mut set = HashSet::new();
            for stmt in stmts {
                set.extend(get_dependencies(&stmt.value));
            }
            if let Some(t) = tail {
                set.extend(get_dependencies(t));
            }
            set
        }
        ResolvedKind::RecordLit(fields) => {
            let mut set = HashSet::new();
            for expr in fields.values() {
                set.extend(get_dependencies(expr));
            }
            set
        }
        ResolvedKind::FieldAccess(expr, _) => get_dependencies(expr),
        ResolvedKind::RecRecord(fields) => {
            let mut set = HashSet::new();
            for (_, expr) in fields.values() {
                set.extend(get_dependencies(expr));
            }
            set
        }
        ResolvedKind::IntLit(_)
        | ResolvedKind::FloatLit(_)
        | ResolvedKind::BoolLit(_)
        | ResolvedKind::StringLit(_)
        | ResolvedKind::UnitLit
        | ResolvedKind::EmptyListLit
        | ResolvedKind::Builtin(_)
        | ResolvedKind::Constructor(_, _) => HashSet::new(),
    }
}
