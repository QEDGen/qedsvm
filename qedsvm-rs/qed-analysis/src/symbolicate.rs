//! PC -> function-name symbolication for lifted programs.
//!
//! Consumes an ELF that carries a symbol table and/or DWARF (in practice the
//! `.debug` sidecar produced by `tests/fixtures/build-fixture.sh`), and answers
//! "what function is this program counter in", inline frames included. Pure
//! analysis: no Lean runtime, no execution.
//!
//! # PC spaces
//!
//! ELF symbol / DWARF addresses live in **slot** space: `slot = (addr -
//! text_base) / INSN_SIZE`, where an `lddw` occupies two slots. That matches
//! jump-offset space, not the logical (decoded-array) space qedlift and the
//! Lean decoder use, where `lddw` is one element. The `*_slot` methods take
//! slot PCs; the `*_logical` methods take a logical PC plus a [`PcMap`] and
//! translate first. For lddw-free programs the two spaces coincide.
//!
//! The DWARF walk is a hand-driven gimli port (not addr2line) because SBF
//! virtual addresses arrive in a split form that [`unmangle_addr`] undoes;
//! addr2line has no hook for that fixup.

use std::collections::BTreeMap;
use std::path::Path;
use std::sync::Arc;

use gimli::Reader;
use object::{Object, ObjectSection, ObjectSymbol};

use crate::PcMap;

/// Bytes per sBPF instruction slot.
const INSN_SIZE: u64 = 8;

type DwarfReader = gimli::EndianReader<gimli::RunTimeEndian, Arc<[u8]>>;

/// Undo SBF address splitting: virtual addresses come packed as
/// `(section_index << 32) | offset`, which collapses to `section_base +
/// offset` once the loader lays sections out contiguously. Every address read
/// from DWARF passes through here.
fn unmangle_addr(x: u64) -> u64 {
    (x >> 32).wrapping_add(x & 0xFFFF_FFFF)
}

/// PC -> function symbolication over one program's debug info.
pub struct SymbolIndex {
    text_base: u64,
    /// Entry-slot -> demangled function name, from the ELF symbol table.
    functions: BTreeMap<u64, String>,
    /// Inline-aware frame ranges, present only when the ELF carries DWARF.
    dwarf: Option<DwarfIndex>,
}

impl SymbolIndex {
    /// Parse an ELF image (a `.debug` sidecar, or any binary retaining symtab /
    /// DWARF). Returns an index with whatever layers are present; an ELF with
    /// neither symtab nor DWARF yields only fallback labels.
    pub fn from_elf_bytes(bytes: &[u8]) -> Result<SymbolIndex, String> {
        let file = object::File::parse(bytes).map_err(|e| format!("parse ELF: {e}"))?;
        let text = file
            .section_by_name(".text")
            .ok_or_else(|| "no .text section".to_string())?;
        let text_base = text.address();
        let text_range = text_base..text_base.saturating_add(text.size());

        let mut functions = BTreeMap::new();
        for sym in file.symbols() {
            if sym.kind() != object::SymbolKind::Text || !text_range.contains(&sym.address()) {
                continue;
            }
            let Ok(name) = sym.name() else { continue };
            if name.is_empty() {
                continue;
            }
            let slot = sym.address().saturating_sub(text_base) / INSN_SIZE;
            functions.insert(slot, rustc_demangle::demangle(name).to_string());
        }

        let dwarf = build_dwarf_index(bytes, text_base);
        Ok(SymbolIndex {
            text_base,
            functions,
            dwarf,
        })
    }

    /// Convenience wrapper over [`SymbolIndex::from_elf_bytes`] reading a file.
    pub fn from_path(path: impl AsRef<Path>) -> Result<SymbolIndex, String> {
        let bytes = std::fs::read(path.as_ref())
            .map_err(|e| format!("read {}: {e}", path.as_ref().display()))?;
        Self::from_elf_bytes(&bytes)
    }

    /// Name of the function containing slot PC `slot` (from the symbol table),
    /// or a `fn@slot<N>` fallback when no symbol covers it.
    pub fn label_slot(&self, slot: u64) -> String {
        self.functions
            .range(..=slot)
            .next_back()
            .map(|(_, name)| name.clone())
            .unwrap_or_else(|| format!("fn@slot{slot}"))
    }

    /// Inline-aware frame chain at slot PC `slot`, outermost first. `None` when
    /// there is no DWARF or nothing maps to that address.
    pub fn inline_frames_slot(&self, slot: u64) -> Option<Vec<String>> {
        let dwarf = self.dwarf.as_ref()?;
        let addr = slot.wrapping_mul(INSN_SIZE).wrapping_add(self.text_base);
        let frames = dwarf.frames_at(addr);
        if frames.is_empty() {
            return None;
        }
        Some(frames.into_iter().map(str::to_string).collect())
    }

    /// [`SymbolIndex::label_slot`] for a logical PC, translated through `map`.
    /// Returns the fallback when the logical PC is out of range.
    pub fn label_logical(&self, logical: usize, map: &PcMap) -> String {
        match map.logical_to_slot(logical) {
            Some(slot) => self.label_slot(slot as u64),
            None => format!("fn@logical{logical}"),
        }
    }

    /// [`SymbolIndex::inline_frames_slot`] for a logical PC, via `map`.
    pub fn inline_frames_logical(&self, logical: usize, map: &PcMap) -> Option<Vec<String>> {
        let slot = map.logical_to_slot(logical)?;
        self.inline_frames_slot(slot as u64)
    }

    /// Whether DWARF inline frames are available.
    pub fn has_dwarf(&self) -> bool {
        self.dwarf.is_some()
    }

    /// Number of named functions recovered from the symbol table.
    pub fn function_count(&self) -> usize {
        self.functions.len()
    }
}

// ---------------------------------------------------------------------------
// DWARF index (inline-aware frame ranges). Hand-driven gimli walk.
// ---------------------------------------------------------------------------

struct DwarfFrame {
    low: u64,
    high: u64,
    depth: usize,
    name: String,
}

struct DwarfIndex {
    frames: Vec<DwarfFrame>,
}

impl DwarfIndex {
    /// Frames covering `addr`, innermost (deepest, tightest) last so a caller
    /// reads them outermost -> innermost.
    fn frames_at(&self, addr: u64) -> Vec<&str> {
        let mut hits: Vec<&DwarfFrame> = self
            .frames
            .iter()
            .filter(|f| f.low <= addr && addr < f.high)
            .collect();
        hits.sort_by_key(|f| (f.depth, std::cmp::Reverse(f.high - f.low)));
        hits.into_iter().map(|f| f.name.as_str()).collect()
    }
}

fn attr_addr(
    dwarf: &gimli::Dwarf<DwarfReader>,
    unit: &gimli::Unit<DwarfReader>,
    value: gimli::AttributeValue<DwarfReader>,
) -> Option<u64> {
    match value {
        gimli::AttributeValue::Addr(a) => Some(unmangle_addr(a)),
        gimli::AttributeValue::DebugAddrIndex(i) => dwarf.address(unit, i).ok().map(unmangle_addr),
        _ => None,
    }
}

fn die_ranges_of(
    dwarf: &gimli::Dwarf<DwarfReader>,
    unit: &gimli::Unit<DwarfReader>,
    entry: &gimli::DebuggingInformationEntry<DwarfReader>,
) -> Vec<(u64, u64)> {
    if let Some(low) = entry
        .attr_value(gimli::DW_AT_low_pc)
        .ok()
        .flatten()
        .and_then(|v| attr_addr(dwarf, unit, v))
    {
        if let Ok(Some(hv)) = entry.attr_value(gimli::DW_AT_high_pc) {
            let high = match hv {
                gimli::AttributeValue::Udata(n) => Some(low.wrapping_add(n)),
                other => attr_addr(dwarf, unit, other),
            };
            return match high {
                Some(high) if high > low => vec![(low, high)],
                _ => Vec::new(),
            };
        }
    }
    if let Ok(Some(v)) = entry.attr_value(gimli::DW_AT_ranges) {
        let offset = match dwarf.attr_ranges_offset(unit, v) {
            Ok(Some(offset)) => offset,
            _ => return Vec::new(),
        };
        let mut out = Vec::new();
        if let Ok(mut iter) = dwarf.ranges(unit, offset) {
            while let Ok(Some(r)) = iter.next() {
                let (low, high) = (unmangle_addr(r.begin), unmangle_addr(r.end));
                if high > low {
                    out.push((low, high));
                }
            }
        }
        return out;
    }
    Vec::new()
}

fn die_name(
    dwarf: &gimli::Dwarf<DwarfReader>,
    unit: &gimli::Unit<DwarfReader>,
    entry: &gimli::DebuggingInformationEntry<DwarfReader>,
    depth: u32,
) -> Option<String> {
    let attr_str = |at: gimli::DwAt| -> Option<String> {
        let value = entry.attr_value(at).ok().flatten()?;
        let s = dwarf.attr_string(unit, value).ok()?;
        Some(s.to_string_lossy().ok()?.into_owned())
    };
    if let Some(name) = attr_str(gimli::DW_AT_linkage_name) {
        return Some(rustc_demangle::demangle(&name).to_string());
    }
    if let Some(name) = attr_str(gimli::DW_AT_name) {
        return Some(rustc_demangle::demangle(&name).to_string());
    }
    // Inlined/abstract DIEs point at the concrete definition; chase it (bounded).
    if depth < 8 {
        for at in [gimli::DW_AT_abstract_origin, gimli::DW_AT_specification] {
            if let Some(gimli::AttributeValue::UnitRef(off)) = entry.attr_value(at).ok().flatten() {
                if let Ok(referenced) = unit.entry(off) {
                    if let Some(name) = die_name(dwarf, unit, &referenced, depth + 1) {
                        return Some(name);
                    }
                }
            }
        }
    }
    None
}

fn build_dwarf_index(elf_bytes: &[u8], text_base: u64) -> Option<DwarfIndex> {
    let file = object::File::parse(elf_bytes).ok()?;
    file.section_by_name(".debug_info")?;
    let endian = if file.is_little_endian() {
        gimli::RunTimeEndian::Little
    } else {
        gimli::RunTimeEndian::Big
    };
    let load = |id: gimli::SectionId| -> Result<DwarfReader, gimli::Error> {
        let data = file
            .section_by_name(id.name())
            .and_then(|s| s.uncompressed_data().ok())
            .unwrap_or(std::borrow::Cow::Borrowed(&[]));
        Ok(gimli::EndianReader::new(Arc::from(data.as_ref()), endian))
    };
    let dwarf = gimli::Dwarf::load(load).ok()?;

    let mut frames = Vec::new();
    let mut units = dwarf.units();
    while let Ok(Some(header)) = units.next() {
        let Ok(unit) = dwarf.unit(header) else {
            continue;
        };
        let mut entries = unit.entries();
        let mut depth = 0isize;
        // Frame nesting depth per DIE tree depth, for the inline `depth` key.
        let mut frame_stack: Vec<isize> = Vec::new();
        // When a subtree resolves below text_base it is dead code; skip it.
        let mut dead_at: Option<isize> = None;
        while let Ok(Some((delta, entry))) = entries.next_dfs() {
            depth += delta;
            match dead_at {
                Some(d) if depth > d => continue,
                _ => dead_at = None,
            }
            while frame_stack.last().is_some_and(|&d| d >= depth) {
                frame_stack.pop();
            }
            if !matches!(
                entry.tag(),
                gimli::DW_TAG_subprogram | gimli::DW_TAG_inlined_subroutine
            ) {
                continue;
            }
            let frame_depth = frame_stack.len();
            frame_stack.push(depth);
            let ranges = die_ranges_of(&dwarf, &unit, entry);
            if ranges.is_empty() {
                continue;
            }
            if ranges.iter().any(|&(low, _)| low < text_base) {
                dead_at = Some(depth);
                frame_stack.pop();
                continue;
            }
            if let Some(name) = die_name(&dwarf, &unit, entry, 0) {
                for (low, high) in ranges {
                    frames.push(DwarfFrame {
                        low,
                        high,
                        depth: frame_depth,
                        name: name.clone(),
                    });
                }
            }
        }
    }
    Some(DwarfIndex { frames })
}

#[cfg(test)]
mod tests {
    use super::*;
    use solana_sbpf::ebpf;

    fn sidecar() -> SymbolIndex {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../tests/fixtures/counter_with_helper.debug"
        );
        SymbolIndex::from_path(path).expect("load counter_with_helper.debug")
    }

    #[test]
    fn resolves_functions_and_inline_frames() {
        let idx = sidecar();
        assert!(idx.has_dwarf(), "sidecar should carry DWARF");
        assert_eq!(idx.function_count(), 2, "increment_by + entrypoint");

        // Entry slots from the symbol table (no lddw in this fixture).
        assert_eq!(idx.label_slot(0), "increment_by");
        assert_eq!(idx.label_slot(4), "entrypoint");
        // A slot inside entrypoint still resolves to entrypoint.
        assert_eq!(idx.label_slot(5), "entrypoint");

        let frames = idx.inline_frames_slot(0).expect("inline frames at slot 0");
        assert_eq!(frames.first().map(String::as_str), Some("increment_by"));
    }

    #[test]
    fn logical_api_matches_slot_for_lddw_free() {
        let idx = sidecar();
        // counter_with_helper is lddw-free, so logical == slot. Build a matching
        // identity PcMap (9 slots of .text / 8 bytes) and confirm the logical
        // API agrees with the slot API.
        let insns: Vec<ebpf::Insn> = (0..9)
            .map(|_| ebpf::Insn {
                ptr: 0,
                opc: ebpf::MOV64_IMM,
                dst: 0,
                src: 0,
                off: 0,
                imm: 0,
            })
            .collect();
        let map = PcMap::from_insns(&insns);
        assert_eq!(idx.label_logical(0, &map), idx.label_slot(0));
        assert_eq!(idx.label_logical(4, &map), idx.label_slot(4));
        assert_eq!(
            idx.inline_frames_logical(0, &map),
            idx.inline_frames_slot(0)
        );
    }
}
