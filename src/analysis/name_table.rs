use crate::analysis::resolver::{DefID, Name};
use std::collections::HashMap;
use std::sync::Arc;

/// Lookup table for preserving original names through compilation.
/// Used to display human-readable names in error messages instead of numeric IDs.
#[derive(Clone, Debug)]
pub struct NameTable {
    name_to_string: Arc<HashMap<Name, String>>,
    defid_to_string: Arc<HashMap<DefID, String>>,
}

impl NameTable {
    /// Create a NameTable from pre-populated maps
    pub fn with_maps(
        name_map: HashMap<Name, String>,
        defid_map: HashMap<DefID, String>,
    ) -> Self {
        NameTable {
            name_to_string: Arc::new(name_map),
            defid_to_string: Arc::new(defid_map),
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

    /// Look up the original name for a DefID.
    /// Returns a fallback string if not found.
    pub fn lookup_defid(&self, defid: &DefID) -> String {
        self.defid_to_string
            .get(defid)
            .cloned()
            .unwrap_or_else(|| format!("<type:{}>", defid.0))
    }
}
