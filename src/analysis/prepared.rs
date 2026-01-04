//! Prepared crate representation for type inference.
//!
//! This module provides the intermediate representation between name resolution
//! and type inference. Definitions are grouped and ordered by dependency.

use crate::analysis::resolver::{
    CrateId, GlobalType, ResolvedDefinition, ResolvedTypeAlias, ResolvedVariant,
};

/// A type-level definition (alias or variant) ready for inference.
#[derive(Debug, Clone)]
pub enum PreparedTypeDefinition {
    Alias(ResolvedTypeAlias),
    Variant(ResolvedVariant),
}

impl PreparedTypeDefinition {
    /// Get the GlobalType name of this type definition.
    pub fn name(&self) -> GlobalType {
        match self {
            PreparedTypeDefinition::Alias(a) => a.name,
            PreparedTypeDefinition::Variant(v) => v.name,
        }
    }
}

/// A crate prepared for type inference, with all definitions ordered by dependency.
#[derive(Debug, Clone)]
pub struct PreparedCrate {
    pub crate_id: CrateId,
    /// Type definitions (aliases + variants), SCC-ordered so dependencies come first.
    pub type_groups: Vec<Vec<PreparedTypeDefinition>>,
    /// Value definitions, SCC-ordered so dependencies come first.
    pub definition_groups: Vec<Vec<ResolvedDefinition>>,
}
