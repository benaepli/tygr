use crate::lexer::TokenKind;
use crate::lexer::{self, LexError};
use crate::parser;
use crate::parser::{Declaration, Span};
use bimap::BiMap;
use chumsky::error::Rich;
use std::collections::HashMap;
use thiserror::Error;
use vfs::VfsPath;

const FILE_EXTENSION: &str = ".tygr";
const RECURSION_LIMIT: usize = 256;

#[derive(Debug, Error)]
pub enum LoadError {
    #[error("Parse errors")]
    ParseErrors {
        file_path: VfsPath,
        errors: Vec<Rich<'static, TokenKind>>,
        module_span: Option<Span>,
    },

    #[error("VFS error: {error}")]
    VfsError {
        file_path: VfsPath,
        #[source]
        error: vfs::VfsError,
        module_span: Option<Span>,
    },

    #[error("I/O error: {error}")]
    IoError {
        file_path: VfsPath,
        #[source]
        error: std::io::Error,
        module_span: Option<Span>,
    },

    #[error("Lex errors")]
    LexErrors {
        file_path: VfsPath,
        errors: Vec<LexError>,
        module_span: Option<Span>,
    },

    #[error("Duplicate module declaration")]
    DuplicateModule {
        file_path: VfsPath,
        path: Vec<String>,
        module_span: Option<Span>,
    },

    #[error("Recursion limit reached")]
    RecursionLimitReached {
        file_path: VfsPath,
        module_span: Option<Span>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(pub usize); // Module IDs are unique within a crate, but not globally

#[derive(Debug, Clone)]
pub struct Crate {
    pub modules: HashMap<ModuleId, ModuleData>,
    pub root_module: ModuleId,
    pub module_paths: BiMap<Vec<String>, ModuleId>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct DfsScope {
    pub entry: u32,
    pub exit: u32,
}

#[derive(Debug, Clone)]
pub struct ModuleData {
    pub id: ModuleId,
    pub parent: Option<ModuleId>,
    pub ast: Vec<Declaration>,
    pub file_path: VfsPath,
    pub scope: DfsScope,
}

#[derive(Debug)]
struct LoadState {
    modules: HashMap<ModuleId, ModuleData>,
    next_id: ModuleId,
    paths: BiMap<Vec<String>, ModuleId>,
    dfs_counter: u32,
}

impl LoadState {
    pub fn new_id(&mut self) -> ModuleId {
        let current = self.next_id;
        self.next_id.0 += 1;
        current
    }
}

impl Default for LoadState {
    fn default() -> Self {
        Self {
            modules: HashMap::new(),
            next_id: ModuleId(0),
            paths: BiMap::new(),
            dfs_counter: 0,
        }
    }
}

fn load_inline_module(
    state: &mut LoadState,
    search_dir: &VfsPath,
    file_path: &VfsPath, // The file containing this inline module
    logical_path: &mut Vec<String>,
    parent: Option<ModuleId>,
    parent_span: Option<Span>,
    ast: Vec<Declaration>,
    depth: usize,
) -> Result<ModuleId, LoadError> {
    if depth >= RECURSION_LIMIT {
        return Err(LoadError::RecursionLimitReached {
            file_path: file_path.clone(),
            module_span: parent_span,
        });
    }

    let id = state.new_id();
    let entry = state.dfs_counter;
    state.dfs_counter += 1;

    for declaration in &ast {
        match declaration {
            Declaration::Module(parser::ModuleDecl {
                name, span, body, ..
            }) => {
                logical_path.push(name.clone());

                if state.paths.contains_left(logical_path) {
                    return Err(LoadError::DuplicateModule {
                        file_path: file_path.clone(),
                        path: logical_path.to_owned(),
                        module_span: Some(*span),
                    });
                }

                let next_directory = search_dir.join(name).map_err(|e| LoadError::VfsError {
                    file_path: file_path.clone(),
                    error: e,
                    module_span: parent_span,
                })?;
                match body {
                    Some(nested_ast) => {
                        load_inline_module(
                            state,
                            &next_directory,
                            file_path,
                            logical_path,
                            Some(id),
                            Some(*span),
                            nested_ast.clone(),
                            depth + 1,
                        )?;
                    }
                    None => {
                        let path = search_dir
                            .join(format!("{}{}", name, FILE_EXTENSION))
                            .map_err(|e| LoadError::VfsError {
                                file_path: file_path.clone(),
                                error: e,
                                module_span: parent_span,
                            })?;

                        load_after_root(
                            state,
                            &next_directory,
                            &path,
                            logical_path,
                            Some(id),
                            Some(*span),
                            depth + 1,
                        )?;
                    }
                }

                logical_path.pop();
            }
            _ => {}
        }
    }

    let exit = state.dfs_counter;
    state.dfs_counter += 1;

    let data = ModuleData {
        id,
        parent,
        ast,
        file_path: file_path.clone(),
        scope: DfsScope { entry, exit },
    };
    state.modules.insert(id, data);
    state.paths.insert(logical_path.clone(), id);
    Ok(id)
}

fn load_after_root(
    state: &mut LoadState,
    search_dir: &VfsPath,
    file_path: &VfsPath,
    logical_path: &mut Vec<String>,
    parent: Option<ModuleId>,
    parent_span: Option<Span>,
    depth: usize,
) -> Result<ModuleId, LoadError> {
    let mut content = String::new();
    let mut reader = file_path.open_file().map_err(|e| LoadError::VfsError {
        file_path: file_path.clone(),
        error: e,
        module_span: parent_span,
    })?;
    reader
        .read_to_string(&mut content)
        .map_err(|e| LoadError::IoError {
            file_path: file_path.clone(),
            error: e,
            module_span: parent_span,
        })?;

    let mut lexer = lexer::Lexer::new(&content);
    let (tokens, lex_errors) = lexer.collect_all();
    if !lex_errors.is_empty() {
        return Err(LoadError::LexErrors {
            file_path: file_path.clone(),
            errors: lex_errors,
            module_span: parent_span,
        });
    }

    let parsed = parser::parse_program(&tokens);
    if parsed.has_errors() {
        let errors = parsed.errors();
        let mut owned = vec![];
        for e in errors {
            owned.push(e.clone().into_owned());
        }

        return Err(LoadError::ParseErrors {
            file_path: file_path.clone(),
            errors: owned,
            module_span: parent_span,
        });
    }

    let ast = parsed
        .into_output()
        .expect("parse result should have output if no errors");

    load_inline_module(
        state,
        search_dir,
        file_path,
        logical_path,
        parent,
        parent_span,
        ast,
        depth,
    )
}

pub fn load_module(root_directory: &VfsPath, root_path: &VfsPath) -> Result<Crate, LoadError> {
    let mut state = LoadState::default();
    let id = load_after_root(
        &mut state,
        root_directory,
        root_path,
        &mut Vec::new(),
        None,
        None,
        0,
    )?;
    Ok(Crate {
        modules: state.modules,
        root_module: id,
        module_paths: state.paths,
    })
}
