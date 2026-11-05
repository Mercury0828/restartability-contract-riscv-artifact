# DR-2 test: U-mode vse64.v with PMP hole at lane K -> M-mode repair -> mret replay.
# Parameters via --defsym:
#   VTYPEI : vtype immediate for vsetvli (0xD8 = SEW=64,LMUL=1,ta,ma ; 0xD9 = SEW=64,LMUL=2)
#   VL     : vector length (2 or 4)
#   K      : faulting lane index (PMP hole at dst + K*8)
#   FAULT  : 1 = PMP hole present (deny U write, cfg=0x19); 0 = pmp_ok pre-set (cfg=0x1B)
# Exit codes (HTIF tohost = (code<<1)|1):
#   0 success; 2 no trap; 3 bad mcause; 4 bad mepc; 5 bad vstart; 6 bad final memory;
#   7 second trap; 8 vsetvli returned wrong VL
# Hand-encoded vector instructions (binutils 2.35 has no RVV):
#   vsetvli t0, a0, VTYPEI  = (VTYPEI<<20)|(10<<15)|(7<<12)|(5<<7)|0x57
#   vle64.v v8, (a1)        = (1<<25)|(11<<15)|(7<<12)|(8<<7)|0x07
#   vse64.v v8, (a2)        = (1<<25)|(12<<15)|(7<<12)|(8<<7)|0x27

  .section .text.init
  .globl _start
_start:
  # M-mode boot
  la    t0, handler
  csrw  mtvec, t0

  # PMP entry 0: NAPOT 8-byte region at dst + K*8
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

  # ---------------- M-mode trap handler ----------------
  .balign 4
handler:
  csrr  t0, mcause
  la    t1, rec_mcause
  sd    t0, 0(t1)
  csrr  t0, mepc
  sd    t0, 8(t1)            # rec_mepc
  csrr  t0, mtval
  sd    t0, 16(t1)           # rec_mtval
  csrr  t0, 0x008            # vstart (CSR name unknown to binutils 2.35)
  sd    t0, 24(t1)           # rec_vstart
  # probe: value of lane PROBE at trap time (PROBE = K+1 if K+1 < VL else VL-1)
  .if (K+1) < VL
  .set PROBE, K+1
  .else
  .set PROBE, VL-1
  .endif
  la    t2, dst
  ld    t3, PROBE*8(t2)
  sd    t3, 32(t1)           # rec_probe_lane
  # trap counting: fail(7) on second trap
  ld    t3, 40(t1)           # trap_count
  addi  t3, t3, 1
  sd    t3, 40(t1)
  li    t4, 1
  bgt   t3, t4, fail7_m
  # repair: rewrite pmpcfg0 with entry0 = pmp_ok (NAPOT|R|W = 0x1B), fixed constants
  li    t0, (0x1F<<8) | 0x1B
  csrw  pmpcfg0, t0
  # Privileged spec 3.7.2: an implementation with page-based virtual memory may cache the identity
  # mapping used in Bare and M-mode, and may cache the PMP check for it, so M-mode software MUST
  # synchronize after writing the PMP CSRs. Running in Bare mode is NOT the same condition as the
  # implementation not having paging at all. Without this the replay may still see the stale
  # permission and the repair is not architecturally guaranteed to have taken effect.
  sfence.vma x0, x0
  # mret to unchanged mepc; vstart untouched
  mret

fail7_m:
  li    a0, (7<<1)|1
  la    t5, tohost
  sd    a0, 0(t5)
1:  j   1b

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

  # ---- after (replayed) store completes: verify ----
  # final memory: dst[i] == src[i] for i in 0..VL-1
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

  .if FAULT
  # trap record checks
  la    t1, rec_mcause
  ld    t3, 40(t1)           # trap_count
  beqz  t3, fail2
  ld    t3, 0(t1)            # mcause == 7 (store/AMO access fault)
  li    t4, 7
  bne   t3, t4, fail3
  ld    t3, 8(t1)            # mepc == &vse_insn
  la    t4, vse_insn
  bne   t3, t4, fail4
  ld    t3, 24(t1)           # vstart == K
  li    t4, K
  bne   t3, t4, fail5
  .else
  # no-fault reference: trap_count must be 0
  la    t1, rec_mcause
  ld    t3, 40(t1)
  bnez  t3, fail7
  .endif

  # success
  li    a0, 1
  j     exit
fail2:  li a0, (2<<1)|1
  j exit
fail3:  li a0, (3<<1)|1
  j exit
fail4:  li a0, (4<<1)|1
  j exit
fail5:  li a0, (5<<1)|1
  j exit
fail6:  li a0, (6<<1)|1
  j exit
fail7:  li a0, (7<<1)|1
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
  .balign 64
  .globl rec_mcause
rec_mcause:
  .dword 0                   # +0  mcause
  .dword 0                   # +8  mepc
  .dword 0                   # +16 mtval
  .dword 0                   # +24 vstart
  .dword 0                   # +32 probe lane value at trap
  .dword 0                   # +40 trap_count

  .section .tohost, "aw", @progbits
  .balign 64
  .globl tohost
tohost:  .dword 0
  .globl fromhost
fromhost: .dword 0
