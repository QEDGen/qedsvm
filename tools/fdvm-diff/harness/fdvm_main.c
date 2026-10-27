/* fd_vm differential harness: run a batch of pre-loaded sBPF images through
   the UNMODIFIED Firedancer interpreter (fd_vm_validate + fd_vm_exec_notrace)
   on bare-metal rv64, printing one observable-outcome line per case on the
   HTIF console.

   The batch is linked in as `case.bin` (format: ../caselib.py). Loading
   the ELF is deliberately out of scope: qedsvm (../QedCase.lean) and this
   harness start from the same post-load image, so a disagreement is an
   interpreter disagreement, not a loader one.

   Per-case setup mirrors firedancer src/flamenco/vm/test_vm_instr.c:run_input
   (instr_ctx = NULL, one flat input region, register overrides applied after
   fd_vm_init). Syscalls available: the CU-only models in syscall_models.c. */

#include "flamenco/vm/fd_vm_private.h"   /* -I <firedancer>/src */

void htif_puts( char const * s );
void htif_puthex( uint64_t v );
void register_syscall_models( fd_sbpf_syscalls_t * syscalls );

extern uchar const case_blob[];

#define BATCH_MAGIC 0x32544142564446UL /* "FDVBAT2" + NUL, see caselib.py */
#define HDR_WORDS   24UL

#define FEAT_DIRECT_MAPPING   1UL
#define FEAT_SYSCALL_PARAM    2UL
#define FEAT_VAS_ADJUSTMENTS  4UL

static fd_vm_t _vm[1] __attribute__((aligned(FD_VM_HOST_REGION_ALIGN)));
/* Static buffers are zeroed by crt0, which costs ~4 RV64 steps per 8 bytes on
   the Sail model; keep them as small as the target corpus allows. */
#ifndef CASE_BUF_SZ
#define CASE_BUF_SZ (1UL<<20)
#endif
static uchar   input_buf[ CASE_BUF_SZ ] __attribute__((aligned(16)));
static uchar   prog_buf [ CASE_BUF_SZ ] __attribute__((aligned(16)));
static uchar   _syscalls[ FD_SBPF_SYSCALLS_FOOTPRINT ] __attribute__((aligned(FD_SBPF_SYSCALLS_ALIGN)));
static ulong   _calldests[ CASE_BUF_SZ/16UL ] __attribute__((aligned(64)));
static fd_vm_input_region_t input_region[1];

static void kv( char const * k, ulong v ) { htif_puts( " " ); htif_puts( k ); htif_puts( "=" ); htif_puthex( v ); }

/* FNV-1a over a byte range: a compact witness of the post-state of a region. */
static ulong fnv( uchar const * p, ulong n ) {
  ulong h = 0xcbf29ce484222325UL;
  for( ulong i=0UL; i<n; i++ ) { h ^= p[i]; h *= 0x100000001b3UL; }
  return h;
}

/* Runs one case; returns 0 or a harness error code (>=100). */
static int
run_case( ulong idx, ulong const * h, fd_sbpf_syscalls_t * syscalls ) {
  ulong sbpf_version  = h[0];
  ulong entry_pc      = h[1];
  ulong cu_budget     = h[2];
  ulong heap_max      = h[3];
  ulong text_cnt      = h[4];
  ulong rodata_sz     = h[5];
  ulong input_sz      = h[6];
  ulong calldests_cnt = h[7];
  ulong r2_initial    = h[8];
  ulong text_off      = h[9];
  ulong features      = h[10];
  ulong reg_mask      = h[11];
  ulong const * reg_init = h + 12;   /* r0..r11 */

  ulong const * text   = h + HDR_WORDS;
  uchar const * rodata = (uchar const *)( text + text_cnt );
  uchar const * input  = rodata + fd_ulong_align_up( rodata_sz, 8UL );
  ulong const * cdests = (ulong const *)( input + fd_ulong_align_up( input_sz, 8UL ) );
  if( input_sz>sizeof(input_buf) ) return 101;
  fd_memcpy( input_buf, input, input_sz );

  /* V0-V2: text is a window of the program image (fd_vm_validate rejects a
     text pointer outside [rodata, rodata+rodata_sz) with BAD_TEXT). The case
     still carries text separately so a mismatched image is detected here. */
  if( !FD_VM_SBPF_ENABLE_STRICTER_ELF_HEADERS( sbpf_version ) ) {
    ulong const * win = (ulong const *)( rodata + text_off );
    if( text_off + 8UL*text_cnt > rodata_sz || memcmp( win, text, 8UL*text_cnt ) ) return 104;
    text = win;
  } else {
    /* V3+: text is its own segment, but fd_vm_validate still requires it to
       sit at or after rodata in host memory and end within rodata_sz+text_sz
       of rodata's start, i.e. directly after an 8-aligned rodata. */
    ulong ro_pad = fd_ulong_align_up( rodata_sz, 8UL );
    if( ro_pad + 8UL*text_cnt > sizeof(prog_buf) ) return 105;
    fd_memcpy( prog_buf, rodata, rodata_sz );
    fd_memcpy( prog_buf + ro_pad, text, 8UL*text_cnt );
    rodata = prog_buf;
    text   = (ulong const *)( prog_buf + ro_pad );
  }

  /* V0-V2 need a calldests bitmap; V3+ must pass NULL (fd_vm_init enforces). */
  fd_sbpf_calldests_t * calldests = NULL;
  if( !FD_VM_SBPF_ENABLE_STRICTER_ELF_HEADERS( sbpf_version ) ) {
    if( fd_sbpf_calldests_footprint( text_cnt )>sizeof(_calldests) ) return 102;
    calldests = fd_sbpf_calldests_join( fd_sbpf_calldests_new( _calldests, text_cnt ) );
    for( ulong i=0UL; i<calldests_cnt; i++ ) fd_sbpf_calldests_insert( calldests, cdests[i] );
  }

  /* One flat writable input region, as qedsvm's `runtimeRegions` models it. */
  input_region[0] = (fd_vm_input_region_t){
    .vaddr_offset = 0UL, .haddr = (ulong)input_buf, .region_sz = (uint)input_sz,
    .address_space_reserved = input_sz, .is_writable = 1, .acc_region_meta_idx = 0UL };

  fd_vm_t * vm = fd_vm_join( fd_vm_new( _vm ) );
  vm = fd_vm_init( vm, NULL, heap_max, cu_budget, rodata, rodata_sz, text, text_cnt,
                   text_off, 8UL*text_cnt, entry_pc, (ulong const *)calldests,
                   sbpf_version, syscalls, NULL /* trace */, NULL /* sha */,
                   input_region, 1U, NULL, 0 /* is_deprecated */,
                   !!( features & FEAT_DIRECT_MAPPING ),
                   !!( features & FEAT_SYSCALL_PARAM ),
                   !!( features & FEAT_VAS_ADJUSTMENTS ),
                   0 /* dump_syscall_to_pb */, r2_initial );
  if( !vm ) return 103;
  for( ulong i=0UL; i<12UL; i++ ) if( reg_mask & (1UL<<i) ) vm->reg[i] = reg_init[i];

  htif_puts( "FDVM" );
  kv( "case", idx );
  int verr = fd_vm_validate( vm );
  kv( "validate", (ulong)(long)verr );
  if( !verr ) {
    int err = fd_vm_exec_notrace( vm );
    kv( "err", (ulong)(long)err );
    static char const * const rn[11] = { "r0","r1","r2","r3","r4","r5","r6","r7","r8","r9","r10" };
    for( ulong i=0UL; i<11UL; i++ ) kv( rn[i], vm->reg[i] );
    kv( "cu_used", cu_budget - vm->cu );
    kv( "frames", vm->frame_cnt );
    kv( "input_fnv", fnv( input_buf, input_sz ) );
  }
  htif_puts( "\n" );
  return 0;
}

int
main( void ) {
  ulong const * b = (ulong const *)case_blob;
  if( b[0]!=BATCH_MAGIC ) { htif_puts( "FDVM bad-batch-magic\n" ); return 100; }
  ulong cnt = b[1];
  ulong off = 2UL;   /* in words */

  fd_sbpf_syscalls_t * syscalls = fd_sbpf_syscalls_join( fd_sbpf_syscalls_new( _syscalls ) );
  register_syscall_models( syscalls );

  for( ulong i=0UL; i<cnt; i++ ) {
    ulong len_words = b[off];
    int rc = run_case( i, b + off + 1UL, syscalls );
    if( rc ) { htif_puts( "FDVM" ); kv( "case", i ); kv( "harness_error", (ulong)rc ); htif_puts( "\n" ); }
    off += 1UL + len_words;
  }
  htif_puts( "FDVM done\n" );
  return 0;
}
