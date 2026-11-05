# RESTART-V frozen litmus suite — the core templates (deliverable D-c)

This directory is the **template-instantiated** part of deliverable D-c. `guide.md:88` freezes D-c as

> an Isla-executable litmus suite: **60–150 tests instantiated from ≥10 core templates** (frozen floor: 60).

The `≥10 core templates` half of that requirement is what this file discharges: twelve named core
templates for the RESTART-V **trap / repair / replay** family, each with an ID, its shape, the question
it probes, and the axes along which it is instantiated. The instantiated `.toml` files live beside this
file; the verbatim verdicts are in `RESULTS.md`.

## What "template" means here, and what it does not

A template is a **shape plus a question**, not a file. Two files instantiate the same template when
they ask the same question of the same shape with one axis moved. Two files instantiate *different*
templates when the question itself changes — MP asks about W→W producer ordering, SB asks about W→R,
LB about R→W, FT08 about coherence, FT06/FT07 about the replay itself, FT10 about the handler.

The honesty rail that governs this directory: **an instantiation must move a semantically meaningful
axis.** Renaming registers, renaming the test, or reordering unrelated instructions is not an
instantiation. Every file below states in its header which axis it moves and against which sibling.

## The twelve core templates

| ID | Shape | Question it probes | Instantiation axes |
|---|---|---|---|
| **FT01** | MP, 2 harts, with a real M-mode trap between the producer's two stores | Does the trap boundary order the producer's pre-trap store before its post-replay store? | lane assignment (x↔y); stored value; **position of the trap** relative to the two stores (before / between / after) |
| **FT02** | FT01 with the faulting store deleted — no TRAP event | The control that isolates the trap boundary: with no trap-entry event, any trap-derived drain relation is empty | lane assignment; stored value; **presence of the privileged preamble at all** (CSRW/XRET present vs wholly absent) |
| **FT03** | FT01 plus an explicit fence on the producer | Calibration: the harness must be able to reach `forbidden` on this shape via a mechanism that is known-good | **fence strength** (`rw,rw` vs `w,w`); fence **position** (before vs after the trap boundary); trap present/absent under a fixed fence |
| **FT04** | SB, 2 harts, trap between hart 0's store and its load | Does the trap boundary supply W→R ordering (i.e. does it act like a store-buffer drain)? | trap present/absent; fence present/absent on the trapping hart |
| **FT05** | LB, 2 harts, trap between hart 0's load and its store | Does the trap boundary supply R→W ordering (full pipeline serialisation)? | trap present/absent |
| **FT06** | Single hart: fault → M-handler repair → `mret` without advancing `mepc` → **replay** → read back | Does the re-executed instruction commit, and is the value it commits the replayed one? | **stored value** (value-discriminated read-back); **asserted outcome** (positive vs the handler-did-not-run negative); **which address** is read back (repaired fault address vs a symbolic lane) |
| **FT07** | Single hart: store → trap/replay → read back the *pre-trap* store (rfi across the boundary) | Does a store in flight at trap entry survive the round trip for the same hart? | asserted read-back value (fresh vs stale) — the pair must split under sc-per-location |
| **FT08** | coWW on one lane spanning the trap boundary, observed by a coRR pair on another hart | Is coherence preserved across the trap boundary? | **observation order** (coherence-inverted vs coherence-respecting) |
| **FT09** | Remote observer, single unordered load, reading a store adjacent to the boundary | Is a store next to the trap boundary externally visible (`rfe`) at all? | **which side of the boundary** the observed store sits on (pre-trap vs post-replay); **asserted observation** (seen vs not seen — the non-vacuity partner) |
| **FT10** | The **handler itself** performs a memory store, po-adjacent to its `csrw` repair | Is the handler's own access ordered against the interrupted stream's, across a privilege change — and does the intervening CSRW event contribute? | **order of the handler's store relative to the `csrw`** (the only pair in the suite that moves a CSRW event across a memory event while holding TRAP/XRET fixed) |
| **FT11** | FT01's producer held fixed; the **observer's** ordering mechanism varied | Which observer-side ordering mechanisms this pipeline actually enforces, in the presence of a trap | **observer ordering**: address dependency / control dependency / bare program order (vs FT01's fence) |
| **FT12** | The same multi-hart shapes with **no privileged machinery at all** — no preamble, no PMP, no handler, no fault | The no-fault reference every trap test is read against, under identical config/IR/cat | **memory shape** (MP / SB / LB) |

## The instantiated files

| Template | Files in this directory | Reference instance already in the repo |
|---|---|---|
| FT01 | `FT01_b_lane_yx`, `FT01_c_val2`, `FT01_d_trap_before_both`, `FT01_e_trap_after_both` | `litmus/trap-scoping/S1v2_trap_mp.toml` |
| FT02 | `FT02_a_notrap_lane_yx`, `FT02_b_notrap_val2`, `FT02_c_notrap_nopreamble` | `litmus/trap-scoping/S1v2_control_notrap.toml` |
| FT03 | `FT03_a_fence_ww_trap`, `FT03_b_fence_rwrw_notrap`, `FT03_c_fence_after_trap` | `litmus/trap-scoping/S1v2_control_fence.toml` |
| FT04 | `FT04_a_sb_trap`, `FT04_b_sb_notrap`, `FT04_c_sb_trap_fence` | — |
| FT05 | `FT05_a_lb_trap`, `FT05_b_lb_notrap` | — |
| FT06 | `FT06_a_replay_val2`, `FT06_b_replay_no_sentinel`, `FT06_c_replay_then_symbolic` | `litmus/trap-scoping/trap_store_faultB2_replay.toml` |
| FT07 | `FT07_a_rfi_across_trap`, `FT07_b_rfi_across_trap_stale` | — |
| FT08 | `FT08_a_coRR_inverted`, `FT08_b_coRR_ordered` | — |
| FT09 | `FT09_a_rfe_post_replay`, `FT09_b_rfe_pre_trap`, `FT09_c_rfe_post_replay_unseen` | — |
| FT10 | `FT10_a_handler_store_after_csrw`, `FT10_b_handler_store_before_csrw` | — |
| FT11 | `FT11_a_obs_addr_dep`, `FT11_b_obs_ctrl_dep`, `FT11_c_obs_po_only` | — |
| FT12 | `FT12_a_mp_reference`, `FT12_b_sb_reference`, `FT12_c_lb_reference` | — |

**33 new files, 12 templates, 33/33 yielding a verdict** (see `RESULTS.md`).
Where a template's *reference* instance already existed in
`litmus/trap-scoping/` it was **not** copied into this directory — a byte-equivalent duplicate would
inflate the repo-wide count without adding a measurement, which the D-c honesty rails forbid. The four
templates whose reference instance is listed above are therefore instantiated here only by their
*variants*; the reference file is cited instead.

## Shared machinery (why the trap tests actually execute)

Every trapping instance reuses, verbatim, the machinery of the working
`litmus/trap-scoping/trap_store_faultB2_replay.toml`:

```
	csrw pmpaddr0, x29        # x29 = 0x207FFFFF (NAPOT) -> entry 0 = [0x80000000,0x84000000)
	csrw pmpcfg0, x30         # x30 = 0x1F = A=NAPOT|RWX
	csrw mepc, x28            # x28 = 0x80100010 -> first U-mode instruction
	mret                      # drop to U-mode  (emits an XRET event)
	...
	sw x5,0(x7)               # x7 = 0x84001000, OUTSIDE entry 0 -> E_SAMO_Access_Fault
	                          #   -> sail_trap (TRAP) -> M-handler widens pmpaddr0 to
	                          #      [0x80000000,0x88000000), sets x1 = 0x2A, mret WITHOUT
	                          #      advancing mepc -> sail_mret (XRET) -> the SAME store replays
```

with the handler at `0x80200000`:

```
	lui t6, 0x21000
	addi t6, t6, -1
	csrw pmpaddr0, t6
	addi x1, x0, 0x2A
	mret
```

Three constraints are load-bearing and must be preserved by any further instantiation:

1. **The preamble is exactly four 4-byte instructions (16 bytes).** `x28 = 0x80100010` is seeded by the
   config, so the fifth instruction is where U-mode starts. `csrw` and `mret` have no compressed form,
   so the preamble length is stable even with `sys_enable_rvc = true`; instructions *after* the `mret`
   may compress freely, because from there on `mepc` is written by the trap hardware, not by the config.
2. **The CSR source registers must stay concrete.** `x28/x29/x30/x5/x7` are seeded in
   `riscv64_g2_trap_umode_ipo.toml`. If they are left symbolic the WARL legaliser in `pmpWriteCfgReg`
   forks and the SMT solve times out; this is why that config is mandatory as **both** `-C` and
   `--footprint-config`.
3. **The config's `in_program_order` delta is required.** `riscv64_g2_trap_umode_ipo.toml` extends
   `in_program_order` to `["sail_barrier", "sail_trap", "sail_mret", "sail_write_CSR"]`. Without it
   isla's `po` (isla-axiomatic/src/axiomatic.rs:411-420) does not relate the abstract trap events to
   anything, and every trap-derived relation is identically empty. This is a disclosed **modelling
   commitment**, not a neutral tooling fix — see `model/S1v2_trap_differential_2026-07-30.md` §3(b).

## Run recipe

```bash
cd /root/restartv/isla
./target/release/isla-axiomatic \
  -A /root/restartv/isla-snapshots-regen/rv64d_g58.ir \
  -C  <REPO>/litmus/trap-scoping/riscv64_g2_trap_umode_ipo.toml \
  --footprint-config <REPO>/litmus/trap-scoping/riscv64_g2_trap_umode_ipo.toml \
  -m  <REPO>/litmus/cat/riscv_s1v2_nodrain.cat \
  -s 300 -T 4 <REPO>/litmus/frozen-suite/FT<nn>_<variant>.toml
```

`<REPO>` = `/mnt/e/Project-git/restartability-contract-riscv`. Use **literal** absolute paths: shell
variable expansion is mangled through the Windows→WSL bridge. `run_frozen_suite.sh` and `run_all.sh` in
this directory are the exact runners used to produce `RESULTS.md`.

**`-s 300` and above, not the `-s 60` of the earlier S1-v2 measurements.** On the machine used for
this run the same reference test (`S1v2_trap_mp`) took `288931ms` where it previously took
`53952ms` — a ~5× slower host — and at `-s 60` it came back `error` ("Error in parsing smt output
to get allowed/forbidden", `z3 head: 'timeout'`) rather than `allowed`. The verdict at `-s 300` is
`S1v2_trap_mp allowed (14 of 14) 288931ms`, i.e. identical to the recorded one. The SMT timeout is a
property of the host, not of the tests.

Nine of the 33 needed more than `-s 300` under 6-way parallelism; all nine returned a verdict once
concurrency was lowered and `-s` raised (two of them only at `-s 2400`). The heaviest instances are
the fence+trap MP shapes (16 candidates) and the handler-store shapes (14 candidates). **Budget the
trap family at `-s 900` or more and at most two concurrent isla instances on a 32-core host**;
`RESULTS.md` §2 records every intermediate `error` verbatim.
