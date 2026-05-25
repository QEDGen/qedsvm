-- Per-instruction-class spec files. Split from the original 14k-line
-- monolith for readability. Linear chain: each file imports the previous.

import SVM.SBPF.InstructionSpecs.Preamble
import SVM.SBPF.InstructionSpecs.Alu
import SVM.SBPF.InstructionSpecs.Jump
import SVM.SBPF.InstructionSpecs.MemByte
import SVM.SBPF.InstructionSpecs.MemDwordLoad
import SVM.SBPF.InstructionSpecs.MemHalfword
import SVM.SBPF.InstructionSpecs.MemWord
import SVM.SBPF.InstructionSpecs.MemDwordStore
import SVM.SBPF.InstructionSpecs.ControlFlow
import SVM.SBPF.InstructionSpecs.Syscalls.Helper
import SVM.SBPF.InstructionSpecs.Syscalls.Log
import SVM.SBPF.InstructionSpecs.Syscalls.ReturnData
import SVM.SBPF.InstructionSpecs.Syscalls.Pda
import SVM.SBPF.InstructionSpecs.Syscalls.Mem
import SVM.SBPF.InstructionSpecs.Syscalls.Sysvar
import SVM.SBPF.InstructionSpecs.Terminating
import SVM.SBPF.InstructionSpecs.CallReturn
import SVM.SBPF.InstructionSpecs.Crypto
