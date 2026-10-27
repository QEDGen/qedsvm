/* Minimal HTIF console + exit (Berkeley host-target interface, as implemented
   by Spike, QEMU `-machine spike`, and the Sail RISC-V model's tohost hook).
   Harness I/O only: it is outside the refinement boundary. */
#include <stdint.h>

/* The Sail model treats the .tohost SECTION BASE as tohost (QEMU uses the
   symbol), so tohost must come first: separate subsections pin the order. */
volatile uint64_t tohost   __attribute__((section(".tohost.0"), aligned(8)));
volatile uint64_t fromhost __attribute__((section(".tohost.1"), aligned(8)));

/* QEMU/Spike acknowledge each console write through `fromhost`; the Sail
   model consumes `tohost` synchronously and never writes `fromhost`, so the
   handshake is compiled in only for HTIF_HANDSHAKE (QEMU) builds. */
void htif_putc( char c ) {
#ifdef HTIF_HANDSHAKE
  while( tohost ) { fromhost = 0; }
  tohost = ( 1UL << 56 ) | ( 1UL << 48 ) | (uint8_t)c;
  while( !fromhost ) {}
  fromhost = 0;
#else
  tohost = ( 1UL << 56 ) | ( 1UL << 48 ) | (uint8_t)c;
#endif
}

void htif_puts( char const * s ) { while( *s ) htif_putc( *s++ ); }

void htif_puthex( uint64_t v ) {
  static char const hex[] = "0123456789abcdef";
  htif_puts( "0x" );
  for( int i = 60; i >= 0; i -= 4 ) htif_putc( hex[ ( v >> i ) & 15 ] );
}

__attribute__((noreturn)) void htif_exit( int code ) {
  for(;;) tohost = ( (uint64_t)(uint32_t)code << 1 ) | 1;
}
