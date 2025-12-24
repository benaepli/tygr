use crate::analysis::inference::TypeScheme;
use crate::analysis::resolver::Name;
use crate::interpreter::{Environment, EvalResult, Value};
use std::fmt;
use std::rc::Rc;

/// A unique identifier for custom functions, used to distinguish them at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CustomFnId(pub usize);

impl fmt::Display for CustomFnId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CustomFn({})", self.0)
    }
}


pub trait CustomFn: 'static {
    fn name(&self) -> &str;

    fn arity(&self) -> usize;
    
    fn type_scheme(&self) -> TypeScheme;
    
    fn call(&self, args: &[Rc<Value>], env: &mut Environment) -> EvalResult;
}

/// A registry for custom functions, managing their IDs and lookup.
#[derive(Default)]
pub struct CustomFnRegistry {
    functions: Vec<Rc<dyn CustomFn>>,
    name_to_id: std::collections::HashMap<Name, CustomFnId>,
}

impl CustomFnRegistry {
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
            name_to_id: std::collections::HashMap::new(),
        }
    }
    
    pub fn register(&mut self, name: Name, func: Rc<dyn CustomFn>) -> CustomFnId {
        let id = CustomFnId(self.functions.len());
        self.functions.push(func);
        self.name_to_id.insert(name, id);
        id
    }

    pub fn get(&self, id: CustomFnId) -> Option<&Rc<dyn CustomFn>> {
        self.functions.get(id.0)
    }

    pub fn get_id_by_name(&self, name: &Name) -> Option<CustomFnId> {
        self.name_to_id.get(name).copied()
    }

    pub fn get_by_name(&self, name: &Name) -> Option<&Rc<dyn CustomFn>> {
        self.get_id_by_name(name).and_then(|id| self.get(id))
    }
}

impl fmt::Debug for CustomFnRegistry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CustomFnRegistry")
            .field("count", &self.functions.len())
            .finish()
    }
}
