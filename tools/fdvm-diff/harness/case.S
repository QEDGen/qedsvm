/* Links the test case image; build.sh copies the chosen case to case.bin. */
    .section .rodata.case, "a"
    .balign 64
    .globl case_blob
case_blob:
    .incbin "case.bin"
