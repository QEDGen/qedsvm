# Bare-metal rv64 toolchain: Debian gcc-riscv64-unknown-elf + newlib built from
# Debian's newlib-source (no prebuilt riscv64 newlib package exists in trixie).
FROM debian:trixie@sha256:4c25275446ca371766b8b093c696782eabce06263fccacb8d5d813b3dc44b308
RUN apt-get update -qq && DEBIAN_FRONTEND=noninteractive apt-get install -y -qq \
      gcc-riscv64-unknown-elf binutils-riscv64-unknown-elf newlib-source \
      qemu-system-misc gcc make xz-utils texinfo bzip2 file python3 >/dev/null
RUN mkdir /build && cd /build && tar xf /usr/src/newlib/newlib-*.tar.* && \
    cd newlib-* && mkdir b && cd b && \
    ../configure --target=riscv64-unknown-elf --prefix=/opt/newlib \
      --disable-newlib-supplied-syscalls --enable-newlib-reent-small \
      --disable-multilib CFLAGS_FOR_TARGET="-O2 -mcmodel=medany -march=rv64imac_zicsr -mabi=lp64" >/dev/null && \
    make -j10 >/tmp/mk.log 2>&1 || (tail -40 /tmp/mk.log; false) && make install >/dev/null && rm -rf /build
ENV NEWLIB=/opt/newlib/riscv64-unknown-elf
