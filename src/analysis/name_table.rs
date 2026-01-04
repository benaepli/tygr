use crate::analysis::resolver::{GlobalName, GlobalType, Name, TypeName};
use std::collections::HashMap;
use std::sync::Arc;

/// Lookup table for preserving original names through compilation.
/// Used to display human-readable names in error messages instead of numeric IDs.
#[derive(Clone, Debug)]
pub struct NameTable {
    name_to_string: Arc<HashMap<Name, String>>,
    type_name_to_string: Arc<HashMap<TypeName, String>>,
}

impl NameTable {
    /// Create a NameTable from pre-populated maps
    pub fn with_maps(
        name_map: HashMap<Name, String>,
        type_name_map: HashMap<TypeName, String>,
    ) -> Self {
        NameTable {
            name_to_string: Arc::new(name_map),
            type_name_to_string: Arc::new(type_name_map),
        }
    }

    /// Look up the original name for a Name ID (Local).
    /// Returns a fallback string if not found.
    pub fn lookup_local_name(&self, name: &Name) -> String {
        self.name_to_string
            .get(name)
            .cloned()
            .unwrap_or_else(|| format!("<name:{}>", name.0))
    }

    /// Look up the original name for a TypeName (Local).
    /// Returns a fallback string if not found.
    pub fn lookup_local_type_name(&self, type_name: &TypeName) -> String {
        self.type_name_to_string
            .get(type_name)
            .cloned()
            .unwrap_or_else(|| format!("<type:{}>", type_name.0))
    }

    /// Look up the original name for a GlobalName (crate-aware Name).
    /// Returns a fallback string if not found.
    pub fn lookup_name(&self, global_name: &GlobalName) -> String {
        let (_crate_id, name) = global_name;
        // For now, ignore crate_id and delegate to local lookup
        // Future: could prefix with crate name if crate_id is Some
        self.lookup_local_name(name)
    }

    /// Look up the original name for a GlobalType (crate-aware TypeName).
    /// Returns a fallback string if not found.
    pub fn lookup_type_name(&self, global_type: &GlobalType) -> String {
        let (_crate_id, type_name) = global_type;
        // For now, ignore crate_id and delegate to local lookup
        // Future: could prefix with crate name if crate_id is Some
        self.lookup_local_type_name(type_name)
    }
}
