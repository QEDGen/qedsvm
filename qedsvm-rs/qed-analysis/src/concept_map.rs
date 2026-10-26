//! Same-build DWARF labels. These are untrusted proposals, never proof inputs.
//!
//! The mandatory `.text` equality gate precedes extraction. Type layouts are
//! relative to a source type; they do not identify serialized accounts, input
//! offsets, handler dispatch values, or runtime error return encodings.

use std::{collections::BTreeSet, sync::Arc};

use gimli::{AttributeValue as A, Reader, Section};
use object::{Object, ObjectSection};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use solana_sbpf::ebpf;

use crate::{
    symbolicate::{try_die_name, unmangle_addr, DwarfReader},
    PcMap,
};

type Dwarf = gimli::Dwarf<DwarfReader>;
type Unit = gimli::Unit<DwarfReader>;
type Entry<'a, 'b> = gimli::DebuggingInformationEntry<'a, 'b, DwarfReader>;

/// Version 1 of the JSON contract. Consumers must check this and artifact hashes.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConceptMap {
    pub schema_version: u32,
    pub trust: String,
    pub pc_convention: String,
    pub artifact: ArtifactIdentity,
    pub coverage: Coverage,
    pub functions: Vec<Function>,
    pub structures: Vec<Structure>,
    pub enumerations: Vec<Enumeration>,
    pub lines: Vec<Line>,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArtifactIdentity {
    pub deployed_sha256: String,
    pub debug_sha256: String,
    pub text_sha256: String,
    pub text_byte_size: usize,
    pub deployed_text_address: u64,
    pub debug_text_address: u64,
    pub sbpf_version: u32,
    pub logical_instruction_count: usize,
}

/// Availability flags, never a claim of complete recovery (optimization can
/// remove any entity). Counts are the lengths of the corresponding arrays.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Coverage {
    pub debug_info: bool,
    pub debug_line: bool,
    pub type_entries: bool,
}

/// Half-open range of logical instruction indices. End may equal program length.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PcRange {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Function {
    /// Stable within this exact debug artifact: absolute .debug_info DIE offset.
    pub id: String,
    pub name: Option<String>,
    pub inlined: bool,
    /// Nearest enclosing concrete function/inline DIE, not a name match.
    pub parent: Option<String>,
    pub ranges: Vec<PcRange>,
    pub call_site: Option<SourceLocation>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SourceLocation {
    pub file: Option<String>,
    pub line: Option<u64>,
    pub column: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Structure {
    pub id: String,
    pub name: Option<String>,
    pub byte_size: Option<u64>,
    pub members: Vec<Member>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Member {
    pub name: Option<String>,
    pub byte_offset: Option<u64>,
    pub type_id: Option<String>,
    pub type_name: Option<String>,
    pub bit_size: Option<u64>,
    pub data_bit_offset: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Enumeration {
    pub signed: Option<bool>,
    pub id: String,
    pub name: Option<String>,
    pub byte_size: Option<u64>,
    pub variants: Vec<Enumerator>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Enumerator {
    pub name: Option<String>,
    /// Decimal string preserves signedness and all 64 bits across JSON clients.
    pub value: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Line {
    pub range: PcRange,
    pub location: SourceLocation,
    /// Function IDs, outermost first. Multiple chains indicate ambiguity, not
    /// one synthetic stack joining unrelated overlapping DIEs.
    pub inline_chains: Vec<Vec<String>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Diagnostic {
    pub code: String,
    pub entity: Option<String>,
    pub message: String,
}

impl ConceptMap {
    /// Read a deployed ELF and its same-build unstripped twin. Mismatched text,
    /// unsupported ELF/version, and malformed DWARF return errors, not labels.
    /// Missing DWARF returns an explicitly partial map with diagnostics.
    pub fn from_elf_bytes(deployed: &[u8], debug: &[u8]) -> Result<Self, String> {
        let deployed_file = parse_sbf(deployed)?;
        let debug_file = parse_sbf(debug)?;
        let deployed_text = deployed_file
            .section_by_name(".text")
            .ok_or("deployed ELF has no .text")?;
        let debug_text = debug_file
            .section_by_name(".text")
            .ok_or("debug ELF has no .text")?;
        let text = deployed_text.data().map_err(|e| e.to_string())?;
        if text != debug_text.data().map_err(|e| e.to_string())? {
            return Err(".text mismatch: refusing labels from a different build".into());
        }
        let version = sbpf_version(&deployed_file)?;
        if version != sbpf_version(&debug_file)? {
            return Err("sBPF version mismatch".into());
        }
        let pcs = LogicalAddresses::new(text, debug_text.address(), version)?;
        let mut map = Self {
            schema_version: 1,
            trust: "untrusted_debug_labels".into(),
            pc_convention: "logical_lddw_once".into(),
            artifact: ArtifactIdentity {
                deployed_sha256: hash(deployed),
                debug_sha256: hash(debug),
                text_sha256: hash(text),
                text_byte_size: text.len(),
                deployed_text_address: deployed_text.address(),
                debug_text_address: debug_text.address(),
                sbpf_version: version,
                logical_instruction_count: pcs.map.logical_len(),
            },
            coverage: Coverage::default(),
            functions: vec![],
            structures: vec![],
            enumerations: vec![],
            lines: vec![],
            diagnostics: vec![],
        };
        let dwarf = Dwarf::load(|id| {
            let data = match debug_file.section_by_name(id.name()) {
                Some(section) => section.uncompressed_data().map_err(|e| e.to_string())?,
                None => std::borrow::Cow::Borrowed(&[][..]),
            };
            Ok::<_, String>(gimli::EndianReader::new(
                Arc::from(data.as_ref()),
                gimli::RunTimeEndian::Little,
            ))
        })?;
        map.coverage.debug_info = !dwarf.debug_info.reader().is_empty();
        map.coverage.debug_line = !dwarf.debug_line.reader().is_empty();
        if !map.coverage.debug_info {
            map.warn(
                "missing_debug_info",
                None,
                "No .debug_info; no function or type labels recovered.",
            );
        }
        if !map.coverage.debug_line {
            map.warn(
                "missing_debug_line",
                None,
                "No .debug_line; no source locations recovered.",
            );
        }
        map.extract(&dwarf, &pcs)
            .map_err(|e| format!("read DWARF: {e}"))?;
        if !map.coverage.type_entries {
            map.warn(
                "missing_type_entries",
                None,
                "No struct/enum DIEs; use full debug=2 for layouts and discriminants.",
            );
        }
        map.attach_inline_chains();
        map.diagnostics.sort();
        map.diagnostics.dedup();
        Ok(map)
    }

    /// Deterministic JSON, with no timestamp, filesystem reads, or random IDs.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    fn warn(&mut self, code: &str, entity: Option<String>, message: &str) {
        self.diagnostics.push(Diagnostic {
            code: code.into(),
            entity,
            message: message.into(),
        });
    }

    fn extract(&mut self, dwarf: &Dwarf, pcs: &LogicalAddresses) -> gimli::Result<()> {
        let mut units = dwarf.units();
        while let Some(header) = units.next()? {
            let unit = dwarf.unit(header)?;
            // Retain full ancestry: a member belongs only to its immediate
            // struct, an inline DIE to its nearest enclosing function.
            let mut ancestors: Vec<(isize, gimli::DwTag, Option<usize>)> = vec![];
            let mut cursor = unit.entries();
            let mut depth = 0isize;
            while let Some((delta, entry)) = cursor.next_dfs()? {
                depth += delta;
                while ancestors.last().is_some_and(|p| p.0 >= depth) {
                    ancestors.pop();
                }
                let id = die_id(&unit, entry.offset());
                let mut index = None;
                match entry.tag() {
                    gimli::DW_TAG_subprogram | gimli::DW_TAG_inlined_subroutine => {
                        let ranges = ranges(dwarf, &unit, entry, pcs)?;
                        let mut logical = vec![];
                        for (low, high) in ranges {
                            // Linker tombstones / removed functions are not code.
                            if low == 0 && low < pcs.base {
                                continue;
                            }
                            match pcs.range(low, high) {
                                Some(range) => logical.push(range),
                                None => self.warn("unmapped_function_range", Some(id.clone()), "DWARF range lies outside .text or cuts an instruction; omitted."),
                            }
                        }
                        logical.sort();
                        logical.dedup();
                        if !logical.is_empty() {
                            let parent = ancestors.iter().rev().find(|p| {
                                matches!(
                                    p.1,
                                    gimli::DW_TAG_subprogram | gimli::DW_TAG_inlined_subroutine
                                )
                            });
                            let parent = parent
                                .and_then(|p| p.2)
                                .map(|i| self.functions[i].id.clone());
                            let name = try_die_name(dwarf, &unit, entry, 0)?;
                            if name.is_none() {
                                self.warn("missing_function_name", Some(id.clone()), "No resolvable function name (cross-unit abstract origins are unsupported).");
                            }
                            index = Some(self.functions.len());
                            self.functions.push(Function {
                                id: id.clone(),
                                name,
                                inlined: entry.tag() == gimli::DW_TAG_inlined_subroutine,
                                parent,
                                ranges: logical,
                                call_site: call_site(dwarf, &unit, entry)?,
                            });
                        }
                    }
                    gimli::DW_TAG_structure_type => {
                        self.coverage.type_entries = true;
                        index = Some(self.structures.len());
                        self.structures.push(Structure {
                            id: id.clone(),
                            name: name(dwarf, &unit, entry)?,
                            byte_size: unsigned(entry, gimli::DW_AT_byte_size)?,
                            members: vec![],
                        });
                    }
                    gimli::DW_TAG_member => {
                        if let Some((_, gimli::DW_TAG_structure_type, Some(i))) = ancestors.last() {
                            let value = entry.attr_value(gimli::DW_AT_data_member_location)?;
                            let byte_offset = value.and_then(|v| v.udata_value());
                            let type_ref = entry.attr_value(gimli::DW_AT_type)?;
                            let (type_id, type_name) = match type_ref {
                                Some(A::UnitRef(off)) => (
                                    Some(die_id(&unit, off)),
                                    name(dwarf, &unit, &unit.entry(off)?)?,
                                ),
                                Some(A::DebugInfoRef(off)) => {
                                    (Some(format!("die:{:x}", off.0)), None)
                                }
                                _ => (None, None),
                            };
                            if byte_offset.is_none() {
                                self.warn("unknown_member_offset", Some(id.clone()), "Member has no constant byte offset; expressions are not evaluated.");
                            }
                            let bit_size = unsigned(entry, gimli::DW_AT_bit_size)?;
                            let data_bit_offset = unsigned(entry, gimli::DW_AT_data_bit_offset)?;
                            if bit_size.is_some() || data_bit_offset.is_some() {
                                self.warn("bitfield_member", Some(id.clone()), "Bit-field metadata is retained; byte offset alone is insufficient.");
                            }
                            self.structures[*i].members.push(Member {
                                name: name(dwarf, &unit, entry)?,
                                byte_offset,
                                type_id,
                                type_name,
                                bit_size,
                                data_bit_offset,
                            });
                        }
                    }
                    gimli::DW_TAG_enumeration_type => {
                        self.coverage.type_entries = true;
                        index = Some(self.enumerations.len());
                        self.enumerations.push(Enumeration {
                            signed: enum_signed(&unit, entry)?,
                            id: id.clone(),
                            name: name(dwarf, &unit, entry)?,
                            byte_size: unsigned(entry, gimli::DW_AT_byte_size)?,
                            variants: vec![],
                        });
                    }
                    gimli::DW_TAG_enumerator => {
                        if let Some((_, gimli::DW_TAG_enumeration_type, Some(i))) = ancestors.last()
                        {
                            let value = entry
                                .attr_value(gimli::DW_AT_const_value)?
                                .and_then(|value| integer(value, self.enumerations[*i].signed));
                            if value.is_none() {
                                self.warn(
                                    "unknown_enum_value",
                                    Some(id.clone()),
                                    "Enumerator has no supported integer constant.",
                                );
                            }
                            self.enumerations[*i].variants.push(Enumerator {
                                name: name(dwarf, &unit, entry)?,
                                value,
                            });
                        }
                    }
                    gimli::DW_TAG_variant_part => {
                        self.warn("unsupported_variant_part", Some(id.clone()), "Data-carrying/niche enum variant encodings are not decoded; no runtime error mapping is inferred.");
                    }
                    _ => {}
                }
                ancestors.push((depth, entry.tag(), index));
            }
            self.extract_lines(dwarf, &unit, pcs)?;
        }
        Ok(())
    }

    fn extract_lines(
        &mut self,
        dwarf: &Dwarf,
        unit: &Unit,
        pcs: &LogicalAddresses,
    ) -> gimli::Result<()> {
        let Some(program) = unit.line_program.clone() else {
            return Ok(());
        };
        let mut rows = program.rows();
        let mut previous: Option<(u64, SourceLocation)> = None;
        while let Some((header, row)) = rows.next_row()? {
            let address = pcs.normalize(row.address());
            if let Some((low, location)) = previous.take() {
                // Rows at the same address override the prior row. End-sequence
                // rows close the interval but never label the following code.
                if address > low {
                    if let Some(range) = pcs.range(low, address) {
                        self.lines.push(Line {
                            range,
                            location,
                            inline_chains: vec![],
                        });
                    } else if low != 0 {
                        self.warn(
                            "unmapped_line_range",
                            None,
                            "Line range lies outside .text or cuts an instruction; omitted.",
                        );
                    }
                } else if address < low {
                    self.warn(
                        "nonmonotonic_line_sequence",
                        None,
                        "Line addresses decreased without an end_sequence; interval omitted.",
                    );
                }
            }
            if !row.end_sequence() {
                previous = Some((
                    address,
                    SourceLocation {
                        file: row
                            .file(header)
                            .map(|f| file_path(dwarf, unit, header, f))
                            .transpose()?,
                        line: row.line().map(|n| n.get()),
                        column: match row.column() {
                            gimli::ColumnType::LeftEdge => None,
                            gimli::ColumnType::Column(n) => Some(n.get()),
                        },
                    },
                ));
            }
        }
        if previous.is_some() {
            self.warn(
                "unterminated_line_sequence",
                None,
                "Last line row has no end_sequence; no interval was invented.",
            );
        }
        Ok(())
    }

    fn attach_inline_chains(&mut self) {
        // Split line intervals at every function boundary so their stacks stay
        // valid throughout the interval, even when the line table does not split.
        let boundaries: BTreeSet<_> = self
            .functions
            .iter()
            .flat_map(|f| f.ranges.iter().flat_map(|r| [r.start, r.end]))
            .collect();
        let mut out = vec![];
        let mut incomplete = BTreeSet::new();
        for line in &self.lines {
            let points: Vec<_> = std::iter::once(line.range.start)
                .chain(
                    boundaries
                        .range((
                            std::ops::Bound::Excluded(line.range.start),
                            std::ops::Bound::Excluded(line.range.end),
                        ))
                        .copied(),
                )
                .chain(std::iter::once(line.range.end))
                .collect();
            for pair in points.windows(2) {
                let active: Vec<_> = self
                    .functions
                    .iter()
                    .filter(|f| {
                        f.ranges
                            .iter()
                            .any(|r| r.start <= pair[0] && pair[1] <= r.end)
                    })
                    .collect();
                let mut chains = vec![];
                for leaf in &active {
                    if active.iter().any(|f| f.parent.as_ref() == Some(&leaf.id)) {
                        continue;
                    }
                    let mut chain = vec![leaf.id.clone()];
                    if leaf.inlined && leaf.parent.is_none() {
                        incomplete.insert(leaf.id.clone());
                    }
                    let mut parent = leaf.parent.as_ref();
                    while let Some(id) = parent {
                        let Some(frame) = active.iter().find(|f| &f.id == id) else {
                            incomplete.insert(leaf.id.clone());
                            break;
                        };
                        chain.push(frame.id.clone());
                        if frame.inlined && frame.parent.is_none() {
                            incomplete.insert(leaf.id.clone());
                        }
                        parent = frame.parent.as_ref();
                    }
                    chain.reverse();
                    chains.push(chain);
                }
                chains.sort();
                chains.dedup();
                out.push(Line {
                    range: PcRange {
                        start: pair[0],
                        end: pair[1],
                    },
                    location: line.location.clone(),
                    inline_chains: chains,
                });
            }
        }
        out.sort_by(|a, b| {
            (a.range, &a.location, &a.inline_chains).cmp(&(b.range, &b.location, &b.inline_chains))
        });
        out.dedup_by(|a, b| {
            a.range == b.range && a.location == b.location && a.inline_chains == b.inline_chains
        });
        if out.iter().any(|l| l.inline_chains.len() > 1) {
            self.warn("ambiguous_inline_coverage", None, "Some PC intervals have multiple inline chains; consumers must preserve the alternatives.");
        }
        for id in incomplete {
            self.warn(
                "incomplete_inline_chain",
                Some(id),
                "Some inline coverage has no covering parent; the chain is partial.",
            );
        }
        self.lines = out;
    }
}

fn hash(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn parse_sbf(bytes: &[u8]) -> Result<object::File<'_>, String> {
    let file = object::File::parse(bytes).map_err(|e| format!("parse ELF: {e}"))?;
    // Newer platform-tools use EM_SBPF=263, unknown to object 0.36. Older
    // toolchains use EM_BPF=247. Require ELF64 LE before reading header fields.
    if file.format() != object::BinaryFormat::Elf
        || !file.is_64()
        || !file.is_little_endian()
        || !matches!(bytes.get(18..20), Some([247, 0] | [7, 1]))
    {
        return Err("expected a little-endian ELF64 SBF artifact (EM_BPF or EM_SBPF)".into());
    }
    Ok(file)
}

fn sbpf_version(file: &object::File<'_>) -> Result<u32, String> {
    match file.flags() {
        object::FileFlags::Elf { e_flags, .. } if matches!(e_flags, 0 | 3) => Ok(e_flags),
        _ => Err(
            "unsupported sBPF version: only V0 and V3 logical PC conventions are supported".into(),
        ),
    }
}

struct LogicalAddresses {
    version: u32,
    base: u64,
    text_len: usize,
    map: PcMap,
}
impl LogicalAddresses {
    fn new(text: &[u8], base: u64, version: u32) -> Result<Self, String> {
        if text.is_empty() || !text.len().is_multiple_of(ebpf::INSN_SIZE) {
            return Err(".text is empty or not a whole number of SBF slots".into());
        }
        base.checked_add(text.len() as u64)
            .ok_or(".text address overflow")?;
        let mut insns = vec![];
        let mut slot = 0;
        while slot < text.len() / ebpf::INSN_SIZE {
            let insn = ebpf::get_insn(text, slot);
            if insn.opc == ebpf::LD_DW_IMM {
                if (slot + 2) * ebpf::INSN_SIZE > text.len() {
                    return Err("truncated lddw in .text".into());
                }
                if text[(slot + 1) * ebpf::INSN_SIZE..(slot + 1) * ebpf::INSN_SIZE + 4] != [0; 4] {
                    return Err("invalid lddw continuation slot".into());
                }
                slot += 2;
            } else {
                slot += 1;
            }
            insns.push(insn);
        }
        Ok(Self {
            version,
            base,
            text_len: text.len(),
            map: PcMap::from_insns(&insns),
        })
    }

    fn normalize(&self, address: u64) -> u64 {
        // Legacy V0 DWARF uses SBF's split section/offset encoding. V3 uses
        // genuine virtual addresses, including the .text region at 2^32;
        // unsplitting those addresses would erase its base.
        if self.version == 0 {
            unmangle_addr(address)
        } else {
            address
        }
    }

    fn boundary(&self, address: u64) -> Option<usize> {
        let offset = usize::try_from(address.checked_sub(self.base)?).ok()?;
        if offset == self.text_len {
            return Some(self.map.logical_len());
        }
        if !offset.is_multiple_of(ebpf::INSN_SIZE) {
            return None;
        }
        let slot = offset / ebpf::INSN_SIZE;
        let logical = self.map.slot_to_logical(slot)?;
        // A continuation slot resolves through PcMap but is not a boundary.
        (self.map.logical_to_slot(logical) == Some(slot)).then_some(logical)
    }

    fn range(&self, low: u64, high: u64) -> Option<PcRange> {
        let start = self.boundary(low)?;
        let end = self.boundary(high)?;
        (start < end).then_some(PcRange { start, end })
    }
}

fn die_id(unit: &Unit, offset: gimli::UnitOffset) -> String {
    match offset.to_debug_info_offset(&unit.header) {
        Some(off) => format!("die:{:x}", off.0),
        None => format!("type-unit:{:?}:{:x}", unit.header.offset(), offset.0),
    }
}

fn name(dwarf: &Dwarf, unit: &Unit, entry: &Entry<'_, '_>) -> gimli::Result<Option<String>> {
    entry
        .attr_value(gimli::DW_AT_name)?
        .map(|v| {
            dwarf
                .attr_string(unit, v)
                .and_then(|s| s.to_string_lossy().map(|s| s.into_owned()))
        })
        .transpose()
}
fn unsigned(entry: &Entry<'_, '_>, attr: gimli::DwAt) -> gimli::Result<Option<u64>> {
    Ok(entry.attr_value(attr)?.and_then(|v| v.udata_value()))
}
fn integer(value: A<DwarfReader>, signed: Option<bool>) -> Option<String> {
    match value {
        A::Sdata(n) => Some(n.to_string()),
        A::Udata(n) => Some(n.to_string()),
        other => match signed {
            Some(true) => other.sdata_value().map(|n| n.to_string()),
            Some(false) => other.udata_value().map(|n| n.to_string()),
            None => None,
        },
    }
}

fn enum_signed(unit: &Unit, entry: &Entry<'_, '_>) -> gimli::Result<Option<bool>> {
    let mut value = entry.attr_value(gimli::DW_AT_type)?;
    // Follow local typedef/qualifier wrappers without chasing reference cycles.
    for _ in 0..8 {
        let Some(A::UnitRef(offset)) = value else {
            return Ok(None);
        };
        let base = unit.entry(offset)?;
        match base.attr_value(gimli::DW_AT_encoding)? {
            Some(A::Encoding(gimli::DW_ATE_signed | gimli::DW_ATE_signed_char)) => {
                return Ok(Some(true))
            }
            Some(A::Encoding(gimli::DW_ATE_unsigned | gimli::DW_ATE_unsigned_char)) => {
                return Ok(Some(false))
            }
            _ => value = base.attr_value(gimli::DW_AT_type)?,
        }
    }
    Ok(None)
}

fn ranges(
    dwarf: &Dwarf,
    unit: &Unit,
    entry: &Entry<'_, '_>,
    pcs: &LogicalAddresses,
) -> gimli::Result<Vec<(u64, u64)>> {
    // Normalize low/high independently: an offset high_pc must be added *after*
    // SBF address unsplitting, as in the existing symbolicator.
    if entry.attr_value(gimli::DW_AT_ranges)?.is_some() {
        let mut ranges = dwarf.die_ranges(unit, entry)?;
        let mut out = vec![];
        while let Some(r) = ranges.next()? {
            out.push((pcs.normalize(r.begin), pcs.normalize(r.end)));
        }
        return Ok(out);
    }
    let low = entry
        .attr_value(gimli::DW_AT_low_pc)?
        .map(|v| dwarf.attr_address(unit, v))
        .transpose()?
        .flatten()
        .map(|address| pcs.normalize(address));
    let high = entry.attr_value(gimli::DW_AT_high_pc)?;
    match (low, high) {
        (Some(low), Some(A::Udata(size))) => Ok(vec![(
            low,
            low.checked_add(size).ok_or(gimli::Error::AddressOverflow)?,
        )]),
        (Some(low), Some(high)) => Ok(dwarf
            .attr_address(unit, high)?
            .map(|high| vec![(low, pcs.normalize(high))])
            .unwrap_or_default()),
        _ => Ok(vec![]),
    }
}

fn attr_string(dwarf: &Dwarf, unit: &Unit, attr: A<DwarfReader>) -> gimli::Result<String> {
    Ok(dwarf
        .attr_string(unit, attr)?
        .to_string_lossy()?
        .into_owned())
}
fn file_path(
    dwarf: &Dwarf,
    unit: &Unit,
    header: &gimli::LineProgramHeader<DwarfReader>,
    file: &gimli::FileEntry<DwarfReader>,
) -> gimli::Result<String> {
    let path = attr_string(dwarf, unit, file.path_name())?;
    if path.starts_with('/') {
        return Ok(path);
    }
    let directory = file
        .directory(header)
        .map(|v| attr_string(dwarf, unit, v))
        .transpose()?
        .unwrap_or_default();
    let mut prefix = directory;
    if !prefix.starts_with('/') {
        if let Some(comp_dir) = unit.comp_dir.as_ref() {
            let comp_dir = comp_dir.to_string_lossy()?;
            if !comp_dir.is_empty() {
                prefix = if prefix.is_empty() {
                    comp_dir.into_owned()
                } else {
                    format!("{comp_dir}/{prefix}")
                };
            }
        }
    }
    Ok(if prefix.is_empty() {
        path
    } else {
        format!("{prefix}/{path}")
    })
}
fn call_site(
    dwarf: &Dwarf,
    unit: &Unit,
    entry: &Entry<'_, '_>,
) -> gimli::Result<Option<SourceLocation>> {
    let Some(A::FileIndex(file_index)) = entry.attr_value(gimli::DW_AT_call_file)? else {
        return Ok(None);
    };
    let file = unit
        .line_program
        .as_ref()
        .and_then(|p| {
            p.header()
                .file(file_index)
                .map(|f| file_path(dwarf, unit, p.header(), f))
        })
        .transpose()?;
    Ok(Some(SourceLocation {
        file,
        line: unsigned(entry, gimli::DW_AT_call_line)?,
        column: unsigned(entry, gimli::DW_AT_call_column)?,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn logical_ranges_reject_continuation_slots_and_preserve_program_end() {
        let text = [
            0x18, 0, 0, 0, 0, 0, 0, 0, // lddw
            0, 0, 0, 0, 1, 0, 0, 0, // high bits
            0x95, 0, 0, 0, 0, 0, 0, 0, // exit
        ];
        let pcs = LogicalAddresses::new(&text, 0x120, 0).unwrap();
        assert_eq!(pcs.range(0x120, 0x138), Some(PcRange { start: 0, end: 2 }));
        assert_eq!(pcs.range(0x130, 0x138), Some(PcRange { start: 1, end: 2 }));
        for (low, high) in [
            (0x128, 0x138),
            (0x120, 0x128),
            (0x121, 0x138),
            (0x118, 0x130),
            (0x120, 0x140),
            (0x130, 0x130),
        ] {
            assert_eq!(pcs.range(low, high), None);
        }
        assert!(LogicalAddresses::new(&text[..8], 0x120, 0).is_err());
        assert!(LogicalAddresses::new(&text[..23], 0x120, 0).is_err());
    }

    fn synthetic_map(functions: Vec<Function>, end: usize) -> ConceptMap {
        let mut map = ConceptMap::from_elf_bytes(
            include_bytes!("../../tests/fixtures/debug_concepts.so"),
            include_bytes!("../../tests/fixtures/debug_concepts.debug"),
        )
        .unwrap();
        map.functions = functions;
        map.lines = vec![Line {
            range: PcRange { start: 0, end },
            location: SourceLocation {
                file: Some("test.rs".into()),
                line: Some(1),
                column: None,
            },
            inline_chains: vec![],
        }];
        map.diagnostics.clear();
        map
    }

    fn function(id: &str, parent: Option<&str>, start: usize, end: usize) -> Function {
        Function {
            id: id.into(),
            name: Some(id.into()),
            inlined: parent.is_some(),
            parent: parent.map(str::to_owned),
            ranges: vec![PcRange { start, end }],
            call_site: None,
        }
    }

    #[test]
    fn overlapping_sibling_frames_remain_alternatives_and_split_line_intervals() {
        let mut map = synthetic_map(
            vec![
                function("root", None, 0, 10),
                function("left", Some("root"), 1, 5),
                function("right", Some("root"), 3, 8),
            ],
            10,
        );
        map.attach_inline_chains();
        let overlap = map
            .lines
            .iter()
            .find(|l| l.range == PcRange { start: 3, end: 5 })
            .unwrap();
        assert_eq!(
            overlap.inline_chains,
            vec![vec!["root", "left"], vec!["root", "right"]]
        );
        assert_eq!(
            map.lines
                .iter()
                .find(|l| l.range == PcRange { start: 5, end: 8 })
                .unwrap()
                .inline_chains,
            vec![vec!["root", "right"]]
        );
        assert!(map
            .diagnostics
            .iter()
            .any(|d| d.code == "ambiguous_inline_coverage"));
    }

    #[test]
    fn parent_coverage_gaps_are_reported_instead_of_claiming_complete_chains() {
        let mut map = synthetic_map(
            vec![
                function("root", None, 0, 2),
                function("inner", Some("root"), 1, 3),
            ],
            3,
        );
        map.attach_inline_chains();
        assert_eq!(
            map.lines
                .iter()
                .find(|l| l.range == PcRange { start: 2, end: 3 })
                .unwrap()
                .inline_chains,
            vec![vec!["inner"]]
        );
        assert!(map
            .diagnostics
            .iter()
            .any(|d| d.code == "incomplete_inline_chain" && d.entity.as_deref() == Some("inner")));
    }

    #[test]
    fn orphan_inline_ancestor_is_reported_even_when_a_child_covers_it_fully() {
        let mut orphan = function("orphan", None, 0, 3);
        orphan.inlined = true;
        let mut map = synthetic_map(vec![orphan, function("inner", Some("orphan"), 0, 3)], 3);
        map.attach_inline_chains();
        assert_eq!(map.lines[0].inline_chains, vec![vec!["orphan", "inner"]]);
        assert!(map
            .diagnostics
            .iter()
            .any(|d| d.code == "incomplete_inline_chain"));
    }

    #[test]
    fn fixed_width_enum_constants_respect_the_underlying_signedness() {
        assert_eq!(integer(A::Data2(0xfffd), Some(true)), Some("-3".into()));
        assert_eq!(integer(A::Data2(0xfffd), Some(false)), Some("65533".into()));
        assert_eq!(integer(A::Data2(0xfffd), None), None);
        assert_eq!(
            integer(A::Udata(u64::MAX), Some(false)),
            Some("18446744073709551615".into())
        );
        assert_eq!(integer(A::Sdata(-3), None), Some("-3".into()));
    }
}
