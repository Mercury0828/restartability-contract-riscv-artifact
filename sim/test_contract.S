# test_contract.S — the CONTRACT handler: the binary that is certified against alpha.
#
# WHY THIS FILE EXISTS, SEPARATELY FROM test.S.
#
# test.S carries an INSTRUMENTED handler. It records mcause/mepc/mtval/vstart, probes the lane after
# the faulting one, and maintains a trap counter -- eight regular memory accesses, one of which reads
# the vector store's own destination array. That instrumentation is what makes test.S a useful DR-2
# measurement harness, and it is exactly what disqualifies it as a witness for alpha: alpha requires
# the trap region to be MEMORY-SILENT, because the erasure argument deletes the trap region and
# erasing an ordinary write would break it. It also writes five temporaries without restoring them,
# so it does not leave the user-visible register state as it found it.
#
# This file carries the handler that actually satisfies the contract:
#
#     csrsi  pmpcfg0, 2       # set the W bit of entry 0: NAPOT|R (0x19) -> NAPOT|R|W (0x1B)
#     sfence.vma x0, x0       # privileged spec 3.7.2, required after a PMP CSR write
#     mret                    # return to the unchanged mepc; vstart untouched
#
# Three instructions. It writes NO general-purpose register -- the repair is an immediate-form CSR
# set, so no scratch register is needed at all -- and performs NO load or store. Therefore:
#
#   * memory-silence holds by inspection: there is no memory access to be silent about;
#   * user-visible register state is preserved trivially: nothing is written;
#   * alpha_regs holds a fortiori, since the store's inputs are a subset of "nothing written";
#   * a suffix instruction that reads any register sees what it would have seen with no trap.
#
# The last point is the one that matters. A handler that clobbers a temporary and does not restore it
# is distinguishable by a program that simply uses that temporary after the replay, even though the
# temporary is not an input of the faulting store.
#
# What the handler does change, and these are the contract's intended differences: the protection
# entry it repairs, and the trap machinery's own CSRs (mcause/mepc/mtval/mstatus) which the hardware
# writes on entry and mret restores on exit. vstart is deliberately left alone -- the replay needs it.
#
# Parameters via --defsym, as in test.S:
#   VTYPEI, VL, K, FAULT
# Exit codes (HTIF tohost = (code<<1)|1):
#   0 success; 6 bad final memory; 8 vsetvli returned wrong VL
#
# NOTE ON WHAT THIS TEST CAN AND CANNOT CHECK. With no instrumentation there is nothing to record, so
# this harness cannot check mcause/mepc/vstart. It checks the thing that matters here: under FAULT=1
# the store CANNOT complete unless the handler's repair took effect, because an unrepaired replay
# would fault again and spin until the instruction limit. So SUCCESS under FAULT=1 is itself the
# evidence that the trap was taken and the repair worked. test.S remains the harness for the
# trap-record measurements.

  .section .text.init
  .globl _start
_start:
  # M-mode boot
  la    t0, handler
  csrw  mtvec, t0

  # PMP entry 0: NAPOT 8-byte region at dst + K*8  (LOWER-numbered than the broad entry, so it wins:
  # PMP is static priority and the lowest-numbered matching entry decides)
  la    t0, dst
  addi  t0, t0, K*8
  srli  t0, t0, 2            # NAPOT 8B: pmpaddr = base>>2, bit0=0
  csrw  pmpaddr0, t0
  # PMP entry 1: NAPOT covering everything
  li    t0, -1
  csrw  pmpaddr1, t0
  # pmpcfg0: entry1 = NAPOT|RWX = 0x1F ; entry0 = FAULT? NAPOT|R=0x19 : NAPOT|R|W=0x1B
  .if FAULT
  li    t0, (0x1F<<8) | 0x19
  .else
  li    t0, (0x1F<<8) | 0x1B
  .endif
  csrw  pmpcfg0, t0

  # enable vector unit: mstatus.VS = dirty (bits 10:9 = 11)
  li    t0, (3<<9)
  csrs  mstatus, t0
  # MPP = U (clear bits 12:11)
  li    t0, (3<<11)
  csrc  mstatus, t0
  # enter U-mode
  la    t0, umain
  csrw  mepc, t0
  mret

  # ---------------- the contract handler ----------------
  # Three instructions, no GPR written, no memory accessed.
  .balign 4
  .globl handler
handler:
  csrsi pmpcfg0, 2           # entry0 |= W : NAPOT|R (0x19) -> NAPOT|R|W (0x1B). No GPR involved.
  sfence.vma x0, x0          # privileged spec 3.7.2: required after writing the PMP CSRs
  mret                       # mepc unchanged, vstart unchanged: the store replays from lane K
  .globl handler_end
handler_end:

  # ---------------- U-mode main ----------------
  .balign 4
umain:
  li    a0, VL
  .word (VTYPEI<<20)|(10<<15)|(7<<12)|(5<<7)|0x57    # vsetvli t0, a0, VTYPEI
  li    t1, VL
  bne   t0, t1, fail8

  la    a1, src
  .word (1<<25)|(11<<15)|(7<<12)|(8<<7)|0x07         # vle64.v v8, (a1)
  la    a2, dst
  .globl vse_insn
vse_insn:
  .word (1<<25)|(12<<15)|(7<<12)|(8<<7)|0x27         # vse64.v v8, (a2)  <-- traps at lane K

  # ---- after (replayed) store completes: final memory must equal src ----
  la    a1, src
  la    a2, dst
  li    t2, 0
memchk:
  ld    t3, 0(a1)
  ld    t4, 0(a2)
  bne   t3, t4, fail6
  addi  a1, a1, 8
  addi  a2, a2, 8
  addi  t2, t2, 1
  li    t5, VL
  blt   t2, t5, memchk

  li    a0, 1
  j     exit
fail6:  li a0, (6<<1)|1
  j exit
fail8:  li a0, (8<<1)|1
exit:
  la    t5, tohost
  sd    a0, 0(t5)
1:  j   1b

  # ---------------- data ----------------
  .section .data
  .balign 64
  .globl src
src:
  .dword 0x1111111111111111
  .dword 0x2222222222222222
  .dword 0x3333333333333333
  .dword 0x4444444444444444
  .balign 64
  .globl dst
dst:
  .dword 0, 0, 0, 0

  .section .tohost, "aw", @progbits
  .balign 64
  .globl tohost
tohost:  .dword 0
  .globl fromhost
fromhost: .dword 0
