//! Versioned file-format contracts shared by `qedrecover` and `qedlift`.
//!
//! Keeping these types outside either command prevents the producer and
//! consumer from evolving independent, merely-compatible representations.

use std::collections::BTreeMap;
use std::fmt;
use std::path::{Path, PathBuf};

use qed_analysis::layout::{AccountField, AccountLayout, FieldKind};
use serde::Deserialize;

pub const QEDMETA_SCHEMA_MAX: u32 = 2;
pub const DESCRIPTOR_SCHEMA_MAX: u32 = 2;

#[derive(Debug)]
pub enum ArtifactError {
    Read {
        path: PathBuf,
        source: std::io::Error,
    },
    Json {
        path: PathBuf,
        source: serde_json::Error,
    },
    Toml {
        path: PathBuf,
        source: toml::de::Error,
    },
    UnsupportedSchema {
        artifact: &'static str,
        path: PathBuf,
        found: u32,
        max: u32,
    },
    InvalidDescriptor {
        path: PathBuf,
        message: String,
    },
}

impl fmt::Display for ArtifactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read { path, source } => write!(f, "{}: {}", path.display(), source),
            Self::Json { path, source } => write!(f, "{}: {}", path.display(), source),
            Self::Toml { path, source } => write!(f, "{}: {}", path.display(), source),
            Self::UnsupportedSchema {
                artifact,
                path,
                found,
                max,
            } => write!(
                f,
                "--{} {}: schema_version {} is newer than this tool understands (max {})",
                artifact,
                path.display(),
                found,
                max
            ),
            Self::InvalidDescriptor { path, message } => {
                write!(f, "--descriptor {}: {}", path.display(), message)
            }
        }
    }
}

impl std::error::Error for ArtifactError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Read { source, .. } => Some(source),
            Self::Json { source, .. } => Some(source),
            Self::Toml { source, .. } => Some(source),
            Self::UnsupportedSchema { .. } | Self::InvalidDescriptor { .. } => None,
        }
    }
}

#[derive(Debug, Deserialize)]
pub struct QedMeta {
    #[serde(default)]
    pub schema_version: u32,
    #[serde(rename = "instruction")]
    pub instructions: Vec<QedMetaInstruction>,
    #[serde(default, rename = "account_layout")]
    pub account_layouts: Vec<QedMetaAccountLayout>,
}

#[derive(Debug, Deserialize)]
pub struct QedMetaAccountLayout {
    pub name: String,
    pub size: usize,
    #[serde(default, rename = "field")]
    pub fields: Vec<QedMetaField>,
}

#[derive(Debug, Deserialize)]
pub struct QedMetaField {
    pub name: String,
    pub offset: usize,
    pub kind: String,
    #[serde(default)]
    pub width_bytes: Option<usize>,
}

#[derive(Debug, Deserialize)]
pub struct QedMetaInstruction {
    pub name: String,
    pub cu_budget: Option<u64>,
    pub discriminator: QedMetaDiscriminator,
    #[serde(default, rename = "account")]
    pub accounts: Vec<QedMetaAccount>,
    #[serde(default)]
    pub recovered: Option<QedMetaRecovered>,
}

#[derive(Debug, Deserialize)]
pub struct QedMetaAccount {
    pub name: String,
    pub layout: Option<String>,
}

#[derive(Debug, Deserialize)]
pub struct QedMetaDiscriminator {
    pub value: i64,
}

#[derive(Debug, Deserialize)]
pub struct QedMetaRecovered {
    pub dispatch_load_pc: usize,
    pub dispatch_jeq_pc: usize,
    pub arm_entry_pc: usize,
}

impl QedMeta {
    pub fn account_layouts(&self) -> Vec<AccountLayout> {
        self.account_layouts
            .iter()
            .map(|layout| AccountLayout {
                name: layout.name.clone(),
                size: layout.size,
                fields: layout
                    .fields
                    .iter()
                    .map(|field| AccountField {
                        name: field.name.clone(),
                        offset: field.offset,
                        kind: field_kind(&field.kind, field.width_bytes),
                    })
                    .collect(),
            })
            .collect()
    }
}

pub fn load_qedmeta(path: &Path) -> Result<QedMeta, ArtifactError> {
    let text = read(path)?;
    let meta: QedMeta = toml::from_str(&text).map_err(|source| ArtifactError::Toml {
        path: path.to_owned(),
        source,
    })?;
    if meta.schema_version > QEDMETA_SCHEMA_MAX {
        return Err(ArtifactError::UnsupportedSchema {
            artifact: "qedmeta",
            path: path.to_owned(),
            found: meta.schema_version,
            max: QEDMETA_SCHEMA_MAX,
        });
    }
    Ok(meta)
}

#[derive(Debug, Deserialize)]
pub struct RefinementDescriptor {
    #[serde(default)]
    pub schema_version: u32,
    pub account: String,
    #[serde(default)]
    pub handler: Option<String>,
    pub mutated: String,
    pub op: DescriptorOp,
    #[serde(default)]
    pub layout: Vec<DescriptorField>,
}

#[derive(Debug, Deserialize)]
pub struct DescriptorField {
    pub offset: usize,
    pub kind: String,
    pub name: String,
    #[serde(default)]
    pub width_bytes: Option<usize>,
}

#[derive(Debug, Deserialize)]
#[serde(untagged)]
pub enum DescriptorOp {
    AddConst { add_const: i64 },
    AddParam { add_param: String },
}

impl RefinementDescriptor {
    pub fn explicit_layout(&self) -> Option<AccountLayout> {
        if self.layout.is_empty() {
            return None;
        }
        let fields: Vec<AccountField> = self
            .layout
            .iter()
            .map(|field| AccountField {
                name: field.name.clone(),
                offset: field.offset,
                kind: field_kind(&field.kind, field.width_bytes),
            })
            .collect();
        let size = fields
            .iter()
            .map(|field| field.offset + field_width(&field.kind))
            .max()
            .unwrap_or(0);
        Some(AccountLayout {
            name: self.account.clone(),
            size,
            fields,
        })
    }
}

pub fn load_descriptor(path: &Path) -> Result<RefinementDescriptor, ArtifactError> {
    let text = read(path)?;
    let descriptor: RefinementDescriptor =
        serde_json::from_str(&text).map_err(|source| ArtifactError::Json {
            path: path.to_owned(),
            source,
        })?;
    if descriptor.schema_version > DESCRIPTOR_SCHEMA_MAX {
        return Err(ArtifactError::UnsupportedSchema {
            artifact: "descriptor",
            path: path.to_owned(),
            found: descriptor.schema_version,
            max: DESCRIPTOR_SCHEMA_MAX,
        });
    }
    if let Some(layout) = descriptor.explicit_layout() {
        if !layout
            .fields
            .iter()
            .any(|field| field.name == descriptor.mutated)
        {
            return Err(ArtifactError::InvalidDescriptor {
                path: path.to_owned(),
                message: format!(
                    "mutated field {:?} is not in the inline layout",
                    descriptor.mutated
                ),
            });
        }
    }
    Ok(descriptor)
}

#[derive(Debug, Deserialize)]
pub struct Overlay {
    pub idl: String,
    #[serde(rename = "instruction")]
    pub instructions: Vec<OverlayInstruction>,
}

#[derive(Debug, Deserialize)]
pub struct OverlayInstruction {
    pub name: String,
    pub refines: Option<String>,
    pub cu_budget: Option<u64>,
    #[serde(default)]
    pub account_layouts: BTreeMap<String, String>,
}

#[derive(Debug, Deserialize)]
pub struct CodamaIdl {
    pub program: IdlProgram,
}

#[derive(Debug, Deserialize)]
pub struct IdlProgram {
    pub name: String,
    #[serde(rename = "publicKey")]
    pub public_key: String,
    pub instructions: Vec<IdlInstruction>,
}

#[derive(Debug, Deserialize)]
pub struct IdlInstruction {
    pub name: String,
    pub accounts: Vec<IdlAccount>,
    pub arguments: Vec<IdlArgument>,
}

#[derive(Debug, Deserialize)]
pub struct IdlAccount {
    pub name: String,
    #[serde(rename = "isWritable", default)]
    pub is_writable: bool,
    #[serde(rename = "isSigner")]
    pub is_signer: serde_json::Value,
}

#[derive(Debug, Deserialize)]
pub struct IdlArgument {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: serde_json::Value,
    #[serde(rename = "defaultValue", default)]
    pub default_value: Option<serde_json::Value>,
}

fn read(path: &Path) -> Result<String, ArtifactError> {
    std::fs::read_to_string(path).map_err(|source| ArtifactError::Read {
        path: path.to_owned(),
        source,
    })
}

fn field_kind(kind: &str, width_bytes: Option<usize>) -> FieldKind {
    match kind {
        "pubkey" => FieldKind::Pubkey,
        "u64" => FieldKind::U64,
        "byte" => FieldKind::Byte,
        _ => FieldKind::Bytes(width_bytes.unwrap_or(0)),
    }
}

fn field_width(kind: &FieldKind) -> usize {
    match kind {
        FieldKind::Pubkey => 32,
        FieldKind::U64 => 8,
        FieldKind::Byte => 1,
        FieldKind::Bytes(width) => *width,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recovered_sidecar_round_trips_shared_contract() {
        let meta = load_qedmeta(Path::new(
            "../tests/fixtures/p_token.transfer.recovered.qedmeta.toml",
        ))
        .expect("load recovered sidecar");
        assert_eq!(meta.schema_version, 2);
        assert_eq!(meta.instructions[0].name, "transfer");
        assert_eq!(
            meta.instructions[0]
                .recovered
                .as_ref()
                .expect("recovered facts")
                .arm_entry_pc,
            304
        );
        assert!(meta.account_layouts().iter().any(|layout| {
            layout.name == "token"
                && layout
                    .fields
                    .iter()
                    .any(|field| field.name == "amount" && field.offset == 64)
        }));
    }

    #[test]
    fn descriptor_loader_rejects_future_schema() {
        let error = load_descriptor(Path::new("../tests/fixtures/descriptor_future_schema.json"))
            .expect_err("future schema must fail closed");
        assert!(matches!(error, ArtifactError::UnsupportedSchema { .. }));
    }
}
