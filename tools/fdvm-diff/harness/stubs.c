/* Link stubs for the only external symbols fd_vm_interp.c / fd_vm.c reference.
   Every stub is meant to be unreachable on the harness path; each one traps
   with a distinct HTIF exit code so a reached stub is caught, never ignored.

     fd_log_private_{0,1}, fd_log_wallclock  : FD_LOG_* in fd_vm_init/new/join
                                               failure branches
     fd_dump_vm_syscall_to_protobuf          : only when vm->dump_syscall_to_pb
     fd_vm_trace_event_exe                   : only in fd_vm_exec_trace          */
#include <stdint.h>

__attribute__((noreturn)) void htif_exit( int code );
void htif_puts( char const * s );

#define TRAP( code, name ) do { htif_puts( "STUB-REACHED " name "\n" ); htif_exit( code ); } while(0)

char const * fd_log_private_0( char const * fmt, ... ) { (void)fmt; TRAP( 201, "fd_log_private_0" ); }
void fd_log_private_1( int level, long now, char const * file, int line, char const * func, char const * msg ) {
  (void)level; (void)now; (void)file; (void)line; (void)func; (void)msg; TRAP( 202, "fd_log_private_1" );
}
long fd_log_wallclock( void ) { TRAP( 203, "fd_log_wallclock" ); }
void fd_dump_vm_syscall_to_protobuf( void * vm, char const * name ) { (void)vm; (void)name; TRAP( 204, "fd_dump_vm_syscall_to_protobuf" ); }
int  fd_vm_trace_event_exe( void * t, unsigned long pc, unsigned long ic, unsigned long cu, unsigned long * reg, unsigned long const * text, unsigned long text_cnt, unsigned long ic_correction, unsigned long frame_cnt ) {
  (void)t; (void)pc; (void)ic; (void)cu; (void)reg; (void)text; (void)text_cnt; (void)ic_correction; (void)frame_cnt;
  TRAP( 205, "fd_vm_trace_event_exe" );
}
