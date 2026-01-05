use crate::analysis::resolver::{GlobalName, GlobalType};
use std::collections::BTreeMap;

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct TagMap {
    mapping: BTreeMap<(GlobalType, GlobalName), u32>,
}

impl TagMap {
    pub fn new() -> Self {
        Self {
            mapping: BTreeMap::new(),
        }
    }

    pub fn insert(&mut self, type_name: GlobalType, ctor_name: GlobalName, tag: u32) {
        self.mapping.insert((type_name, ctor_name), tag);
    }

    pub fn get(&self, type_name: GlobalType, ctor_name: GlobalName) -> u32 {
        *self
            .mapping
            .get(&(type_name, ctor_name))
            .expect("Constructor tag not found")
    }
}
