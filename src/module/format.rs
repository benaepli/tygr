use crate::analysis::format::{report_resolution_errors, report_type_errors};
use crate::lexer;
use crate::module::{CompileError, CrateCompiler};
use crate::parser;
use codespan_reporting::term::WriteStyle;
use std::io;

/// Reports a CompileError using the integrated FileSources and NameTable.
pub fn report_compile_error(
    writer: &mut impl WriteStyle,
    compiler: &CrateCompiler,
    error: &CompileError,
) -> Result<(), io::Error> {
    let sources = compiler.sources();
    let name_table = compiler.name_table();

    match error {
        CompileError::Load(load_error) => {
            match load_error {
                crate::driver::LoadError::ParseErrors { errors, .. } => {
                    parser::format::report_errors(writer, sources, errors.iter())
                        .map_err(to_io_error)?;
                }
                crate::driver::LoadError::LexErrors { errors, .. } => {
                    lexer::format::report_errors(writer, sources, errors).map_err(to_io_error)?;
                }
                _ => {
                    // Fallback for other load errors that don't have multiple rich errors
                    eprintln!("Load error: {}", load_error);
                }
            }
        }
        CompileError::Resolution(res_error) => {
            report_resolution_errors(writer, sources, std::slice::from_ref(res_error))
                .map_err(to_io_error)?;
        }
        CompileError::Type(type_error) => {
            report_type_errors(
                writer,
                sources,
                std::slice::from_ref(type_error),
                name_table,
            )
            .map_err(to_io_error)?;
        }
        CompileError::Manifest(manifest_error) => {
            eprintln!("Manifest error: {}", manifest_error);
        }
        CompileError::Path(path_error) => {
            eprintln!("Path error: {}", path_error);
        }
        CompileError::DependencyCycle => {
            eprintln!("Dependency cycle detected");
        }
    }

    Ok(())
}

fn to_io_error(e: codespan_reporting::files::Error) -> io::Error {
    io::Error::new(io::ErrorKind::Other, e.to_string())
}
