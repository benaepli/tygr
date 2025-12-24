use crate::analysis::inference::{TypeDisplay, TypeKind, TypedGroup};
use crate::analysis::name_table::NameTable;
use crate::analysis::resolver::Name;
use std::rc::Rc;

#[derive(Debug, thiserror::Error)]
pub enum MainFunctionError {
    #[error("main function not found")]
    NotFound,
    #[error("main function has wrong type: expected Unit -> Unit, found {0}")]
    WrongType(String),
}

pub fn find_and_verify_main(
    groups: &[TypedGroup],
    name_table: &NameTable,
) -> Result<Name, MainFunctionError> {
    let mut main_def = None;

    for group in groups {
        match group {
            TypedGroup::NonRecursive(def) => {
                if def.name.1 == "main" {
                    main_def = Some(def);
                }
            }
            TypedGroup::Recursive(defs) => {
                for def in defs {
                    if def.name.1 == "main" {
                        main_def = Some(def);
                    }
                }
            }
        }
    }

    let def = main_def.ok_or(MainFunctionError::NotFound)?;
    if let TypeKind::Function(arg, ret) = &def.ty.as_ref().ty {
        let is_unit = |t: &Rc<crate::analysis::inference::Type>| matches!(t.as_ref().ty, TypeKind::Con(id) if id == crate::builtin::UNIT_TYPE);

        if is_unit(arg) && is_unit(ret) {
            return Ok(def.name.0);
        }
    }

    let type_display = TypeDisplay::new(def.ty.clone(), name_table).to_string();
    Err(MainFunctionError::WrongType(type_display))
}
