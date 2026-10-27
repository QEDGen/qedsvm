/* Syscall MODELS for the harness. The refinement theorem treats syscalls as an
   explicit interface (a hypothesis about what each syscall does to the VM
   state), not as code under verification. These models implement only that
   interface contract: CU charging, r0, and the error channel, mirroring
   FD_VM_CU_UPDATE (fd_vm_syscall_macros.h) minus its instr_ctx error logging
   (instr_ctx is NULL here). They let the harness exercise the interpreter's
   side of the syscall boundary: meter re-sync, SIGCOST-on-syscall, sigsyscall. */

#include "flamenco/vm/fd_vm_private.h"   /* -I <firedancer>/src */

static int
cu_only( fd_vm_t * vm, ulong cost ) {
  if( FD_UNLIKELY( cost>vm->cu ) ) { vm->cu = 0UL; return FD_VM_SYSCALL_ERR_COMPUTE_BUDGET_EXCEEDED; }
  vm->cu    -= cost;
  vm->reg[0] = 0UL;
  return FD_VM_SUCCESS;
}

/* sol_log_64_: FD_VM_LOG_64_UNITS (100), then writes a log line (dropped). */
static int
model_sol_log_64( void * vm, ulong r1, ulong r2, ulong r3, ulong r4, ulong r5 ) {
  (void)r1; (void)r2; (void)r3; (void)r4; (void)r5;
  return cu_only( (fd_vm_t *)vm, FD_VM_LOG_64_UNITS );
}

void
register_syscall_models( fd_sbpf_syscalls_t * syscalls ) {
  fd_sbpf_syscalls_t * e = fd_sbpf_syscalls_insert( syscalls, 0x5c2a3178UL /* murmur3("sol_log_64_") */ );
  e->func = model_sol_log_64;
  e->name = "sol_log_64_";
}
