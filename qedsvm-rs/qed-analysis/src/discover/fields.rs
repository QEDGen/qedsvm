//! Field labels for account data (solana-skills#450). A label is a DWARF member name for
//! an input offset that a generated guard reads. It is a label only: the theorem states
//! the byte offset, and no proof depends on the name.

use crate::concept_map::{ConceptMap, Structure};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LabelStatus {
    Labelled { structure_id: String },
    Refused(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldLabel {
    pub data_offset: u64,
    pub width: u64,
    pub name: Option<String>,
    pub status: LabelStatus,
}

fn scalar_size(type_name: &str) -> Option<u64> {
    match type_name {
        "u8" | "i8" | "bool" => Some(1),
        "u16" | "i16" => Some(2),
        "u32" | "i32" => Some(4),
        "u64" | "i64" | "usize" | "isize" => Some(8),
        "u128" | "i128" => Some(16),
        _ => None,
    }
}

/// The member that holds the load, if the load fits it: inside its extent, and exactly the
/// member when the member is a scalar.
fn member_for(s: &Structure, size: u64, off: u64, width: u64) -> Option<String> {
    let mut members: Vec<_> = s
        .members
        .iter()
        .filter_map(|m| m.byte_offset.map(|o| (o, m)))
        .collect();
    members.sort_by_key(|(o, _)| *o);
    for (i, (start, m)) in members.iter().enumerate() {
        let end = members.get(i + 1).map_or(size, |(o, _)| *o);
        if off >= *start && off + width <= end {
            if let Some(scalar) = m.type_name.as_deref().and_then(scalar_size) {
                if off != *start || width != scalar {
                    return None;
                }
            }
            return m.name.clone();
        }
    }
    None
}

/// Labels for `loads` (`(data offset, width)`) in an account of `data_len` bytes. The struct
/// must be the only one of that size that fits every load; otherwise every label is refused.
pub fn label_fields(map: &ConceptMap, data_len: u64, loads: &[(u64, u64)]) -> Vec<FieldLabel> {
    let fits: Vec<&Structure> = map
        .structures
        .iter()
        .filter(|s| s.byte_size == Some(data_len))
        .filter(|s| {
            loads
                .iter()
                .all(|&(o, w)| member_for(s, data_len, o, w).is_some())
        })
        .collect();
    let refused = |reason: String| {
        loads
            .iter()
            .map(|&(o, w)| FieldLabel {
                data_offset: o,
                width: w,
                name: None,
                status: LabelStatus::Refused(reason.clone()),
            })
            .collect()
    };
    match fits.as_slice() {
        [] => refused(format!("no {data_len}-byte struct fits the loads")),
        [s] => loads
            .iter()
            .map(|&(o, w)| FieldLabel {
                data_offset: o,
                width: w,
                name: member_for(s, data_len, o, w),
                status: LabelStatus::Labelled {
                    structure_id: s.id.clone(),
                },
            })
            .collect(),
        many => refused(format!(
            "{} {data_len}-byte structs fit the loads",
            many.len()
        )),
    }
}
