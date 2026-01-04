use serde::Deserialize;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use thiserror::Error;

/// A parsed Tygr.toml manifest.
#[derive(Debug, Clone, Deserialize)]
pub struct Manifest {
    pub project: Project,
    #[serde(default)]
    pub dependencies: HashMap<String, String>, // alias -> path
}

/// Project metadata section.
#[derive(Debug, Clone, Deserialize)]
pub struct Project {
    pub name: String,
    #[serde(rename = "type")]
    pub project_type: ProjectType,
}

/// Type of project (binary or library).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ProjectType {
    Binary,
    Lib,
}

/// Errors that can occur during manifest operations.
#[derive(Debug, Error)]
pub enum ManifestError {
    #[error("failed to read manifest: {0}")]
    Io(#[from] std::io::Error),

    #[error("failed to parse manifest: {0}")]
    Parse(#[from] toml::de::Error),

    #[error("manifest not found at {0}")]
    NotFound(PathBuf),

    #[error("dependency `{0}` is a binary, only libraries can be dependencies")]
    BinaryDependency(String),
}

impl Manifest {
    /// Load and parse a manifest from the given path.
    pub fn load(path: &Path) -> Result<Self, ManifestError> {
        if !path.exists() {
            return Err(ManifestError::NotFound(path.to_path_buf()));
        }
        let content = std::fs::read_to_string(path)?;
        let manifest: Manifest = toml::from_str(&content)?;
        Ok(manifest)
    }

    /// Get the crate root file path (src/main.tygr or src/lib.tygr).
    pub fn crate_root(&self, manifest_dir: &Path) -> PathBuf {
        let filename = match self.project_type() {
            ProjectType::Binary => "main.tygr",
            ProjectType::Lib => "lib.tygr",
        };
        manifest_dir.join("src").join(filename)
    }

    /// Get the project type.
    pub fn project_type(&self) -> ProjectType {
        self.project.project_type
    }

    /// Check if this manifest can be used as a dependency (must be a library).
    pub fn is_library(&self) -> bool {
        self.project.project_type == ProjectType::Lib
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_binary_manifest() {
        let toml = r#"
[project]
name = "my_project"
type = "binary"

[dependencies]
foo = "../foo"
bar = "../some_lib"
"#;
        let manifest: Manifest = toml::from_str(toml).unwrap();
        assert_eq!(manifest.project.name, "my_project");
        assert_eq!(manifest.project.project_type, ProjectType::Binary);
        assert_eq!(manifest.dependencies.len(), 2);
        assert_eq!(
            manifest.dependencies.get("foo"),
            Some(&"../foo".to_string())
        );
    }

    #[test]
    fn test_parse_lib_manifest() {
        let toml = r#"
[project]
name = "my_lib"
type = "lib"
"#;
        let manifest: Manifest = toml::from_str(toml).unwrap();
        assert_eq!(manifest.project.name, "my_lib");
        assert_eq!(manifest.project.project_type, ProjectType::Lib);
        assert!(manifest.dependencies.is_empty());
        assert!(manifest.is_library());
    }

    #[test]
    fn test_crate_root() {
        let binary_toml = r#"
[project]
name = "bin"
type = "binary"
"#;
        let lib_toml = r#"
[project]
name = "lib"
type = "lib"
"#;
        let dir = Path::new("/test/project");

        let bin_manifest: Manifest = toml::from_str(binary_toml).unwrap();
        assert_eq!(
            bin_manifest.crate_root(dir),
            PathBuf::from("/test/project/src/main.tygr")
        );

        let lib_manifest: Manifest = toml::from_str(lib_toml).unwrap();
        assert_eq!(
            lib_manifest.crate_root(dir),
            PathBuf::from("/test/project/src/lib.tygr")
        );
    }
}
