/* RAM at 0x80000000 (QEMU `-machine spike`, Spike, and the Sail model's
   default). fd_vm_t is ~0.5 MiB (64 x 4 KiB stack + 256 KiB heap) and lives in
   .bss, so 64 MiB is ample. */
OUTPUT_ARCH(riscv)
ENTRY(_start)

MEMORY { RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 64M }

SECTIONS
{
    .text : { *(.text.init) *(.text .text.*) } > RAM
    .rodata : ALIGN(8) { *(.rodata .rodata.*) *(.srodata .srodata.*) } > RAM
    .tohost : ALIGN(64) { *(.tohost.0) *(.tohost.1) } > RAM
    .data : ALIGN(8) {
        __global_pointer$ = . + 0x800;
        *(.data .data.*) *(.sdata .sdata.*)
    } > RAM
    .bss : ALIGN(64) {
        __bss_start = .;
        *(.sbss .sbss.*) *(.bss .bss.*) *(COMMON)
        . = ALIGN(8);
        __bss_end = .;
    } > RAM
    . = ALIGN(16);
    _end = .;
    __stack_top = ORIGIN(RAM) + LENGTH(RAM);
}
