use crate::parser::SourceId;
use std::collections::HashMap;
use std::ops::Range;

/// A collection of source files for error reporting.
/// Maps SourceId to (filename, source_content) for multi-file diagnostics.
pub struct FileSources {
    files: HashMap<SourceId, (String, String)>,
}

impl FileSources {
    pub fn new() -> Self {
        FileSources {
            files: HashMap::new(),
        }
    }

    /// Add a file with a specific SourceId.
    pub fn add(&mut self, id: SourceId, name: impl Into<String>, source: impl Into<String>) {
        self.files.insert(id, (name.into(), source.into()));
    }

    /// Create a FileSources with a single file using SYNTHETIC SourceId.
    pub fn single(name: impl Into<String>, source: impl Into<String>) -> Self {
        let mut files = Self::new();
        files.add(SourceId::SYNTHETIC, name, source);
        files
    }
}

impl Default for FileSources {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> codespan_reporting::files::Files<'a> for FileSources {
    type FileId = SourceId;
    type Name = &'a str;
    type Source = &'a str;

    fn name(&'a self, id: Self::FileId) -> Result<Self::Name, codespan_reporting::files::Error> {
        self.files
            .get(&id)
            .map(|(name, _)| name.as_str())
            .ok_or(codespan_reporting::files::Error::FileMissing)
    }

    fn source(
        &'a self,
        id: Self::FileId,
    ) -> Result<Self::Source, codespan_reporting::files::Error> {
        self.files
            .get(&id)
            .map(|(_, source)| source.as_str())
            .ok_or(codespan_reporting::files::Error::FileMissing)
    }

    fn line_index(
        &'a self,
        id: Self::FileId,
        byte_index: usize,
    ) -> Result<usize, codespan_reporting::files::Error> {
        let source = self.source(id)?;
        Ok(source[..byte_index].chars().filter(|c| *c == '\n').count())
    }

    fn line_range(
        &'a self,
        id: Self::FileId,
        line_index: usize,
    ) -> Result<Range<usize>, codespan_reporting::files::Error> {
        let source = self.source(id)?;
        let mut line_start = 0;
        let mut current_line = 0;

        for (i, c) in source.char_indices() {
            if current_line == line_index {
                // Found the start of the target line
                let line_end = source[i..]
                    .find('\n')
                    .map(|offset| i + offset)
                    .unwrap_or(source.len());
                return Ok(line_start..line_end);
            }
            if c == '\n' {
                current_line += 1;
                line_start = i + 1;
            }
        }

        // Handle last line without trailing newline
        if current_line == line_index {
            return Ok(line_start..source.len());
        }

        Err(codespan_reporting::files::Error::LineTooLarge {
            given: line_index,
            max: current_line,
        })
    }
}
