use crate::analysis::resolver::{CrateId, GlobalName, GlobalType, Name, TypeName};
use std::collections::HashMap;
use std::sync::Arc;

/// Lookup table for preserving original names within a single crate.
/// Used to display human-readable names in error messages instead of numeric IDs.
#[derive(Clone, Debug, Default)]
pub struct LocalNameTable {
    name_to_string: Arc<HashMap<Name, String>>,
    type_name_to_string: Arc<HashMap<TypeName, String>>,
}

impl LocalNameTable {
    /// Create a LocalNameTable from pre-populated maps
    pub fn with_maps(
        name_map: HashMap<Name, String>,
        type_name_map: HashMap<TypeName, String>,
    ) -> Self {
        LocalNameTable {
            name_to_string: Arc::new(name_map),
            type_name_to_string: Arc::new(type_name_map),
        }
    }

    /// Look up the original name for a Name ID.
    /// Returns a fallback string if not found.
    pub fn lookup_name(&self, name: &Name) -> String {
        self.name_to_string
            .get(name)
            .cloned()
            .unwrap_or_else(|| format!("<name:{}>", name.0))
    }

    /// Look up the original name for a TypeName.
    /// Returns a fallback string if not found.
    pub fn lookup_type_name(&self, type_name: &TypeName) -> String {
        self.type_name_to_string
            .get(type_name)
            .cloned()
            .unwrap_or_else(|| format!("<type:{}>", type_name.0))
    }
}

/// Aggregate name table containing local tables for multiple crates.
/// Provides global lookup for names across all loaded crates.
#[derive(Clone, Debug, Default)]
pub struct NameTable {
    tables: HashMap<Option<CrateId>, LocalNameTable>,
}

impl NameTable {
    pub fn new() -> Self {
        Self {
            tables: HashMap::new(),
        }
    }

    pub fn with_global(global_table: LocalNameTable) -> Self {
        let mut tables = HashMap::new();
        tables.insert(None, global_table);
        Self { tables }
    }

    /// Add a local name table for a crate.
    pub fn add(&mut self, crate_id: Option<CrateId>, table: LocalNameTable) {
        self.tables.insert(crate_id, table);
    }

    /// Get the local name table for a crate, if present.
    pub fn get(&self, crate_id: &Option<CrateId>) -> Option<&LocalNameTable> {
        self.tables.get(crate_id)
    }

    /// Look up the original name for a GlobalName.
    /// Returns a fallback string if not found.
    pub fn lookup_name(&self, global_name: &GlobalName) -> String {
        if let Some(local_table) = self.tables.get(&global_name.krate) {
            return local_table.lookup_name(&global_name.name);
        }

        format!("<name:{}>", global_name.name.0)
    }

    /// Look up the original name for a GlobalType.
    /// Returns a fallback string if not found.
    pub fn lookup_type_name(&self, global_type: &GlobalType) -> String {
        if let Some(local_table) = self.tables.get(&global_type.krate) {
            return local_table.lookup_type_name(&global_type.name);
        }
        format!("<type:{}>", global_type.name.0)
    }
}
