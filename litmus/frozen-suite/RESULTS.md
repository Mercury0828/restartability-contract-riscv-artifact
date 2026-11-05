# RESULTS — frozen litmus suite (deliverable D-c), measured 2026-07-30

> **Honesty rails.** Every line in the verdict columns below is the **verbatim** `isla-axiomatic`
> summary line (the trailing terminal progress dots are stripped; nothing else is edited).
> `error` ≠ `forbidden` ≠ `timeout` ≠ `allowed`, never conflated. **A test is counted as delivered
> only if it RUNS AND YIELDS A VERDICT** (`allowed` or `forbidden`). Intermediate runs that
> `error`ed are **not** deleted from this record: §2 lists every one of them verbatim alongside the
> run that eventually produced the verdict, so the reader can see exactly how many attempts each
> number cost.

---

## 0. Headline

| Quantity | Count |
|---|---|
| Core templates named and instantiated (`TEMPLATES.md`) | **12** |
| New `.toml` files created in `litmus/frozen-suite/` | **33** |
| **New tests that RUN AND YIELD A VERDICT** | **33** |
| New tests that do not yield a verdict | **0** |
| Pre-existing repo tests that run and yield a verdict | **47** |
| Pre-existing repo test files that do not | **2** |
| **REPO-WIDE TOTAL OF RUNNABLE TESTS** | **80** |
| Frozen floor for D-c | 60 |

**Floor cleared: 80 ≥ 60, from 12 core templates**, and inside the required 60–150 band.
The "instantiated from ≥10 core templates" clause is satisfied directly: `TEMPLATES.md` names 12
templates, and every new file states in its header which template it instantiates and which
semantic axis it moves relative to which sibling.

Note the honest shape of that 80: **33** of it is the new template-instantiated trap/replay suite,
**11** is the pre-existing trap-scoping work, and **36** is the standard RVWMO suite, which is
oracle calibration and not instantiated from RESTART-V templates. The claim being made is
*80 runnable tests, of which 44 are RESTART-V trap-family tests and 33 are template-instantiated*,
not *80 template-instantiated tests*.

---

## 1. New tests — verbatim verdicts (33 files, 33 verdicts)

Run recipe for every row (literal absolute paths; `<REPO>` = `/mnt/e/Project-git/restartability-contract-riscv`):

```bash
cd /root/restartv/isla
./target/release/isla-axiomatic \
  -A /root/restartv/isla-snapshots-regen/rv64d_g58.ir \
  -C  <REPO>/litmus/trap-scoping/riscv64_g2_trap_umode_ipo.toml \
  --footprint-config <REPO>/litmus/trap-scoping/riscv64_g2_trap_umode_ipo.toml \
  -m  <REPO>/litmus/cat/riscv_s1v2_nodrain.cat \
  -s <TIMEOUT> -T <THREADS> <REPO>/litmus/frozen-suite/<TEST>.toml
```

`pass 1` = 6 concurrent, `-s 300 -T 4`; `pass 2` = 2 concurrent, `-s 900 -T 8`;
`pass 3` = 2 concurrent, `-s 2400 -T 14`. See §2 for why more than one pass was needed.

| # | Test | Verbatim `isla-axiomatic` summary line | Verdict from |
|---|---|---|---|
| 1 | FT01_b_lane_yx | `FT01_b_lane_yx allowed (14 of 14) 402918ms` | pass 2 |
| 2 | FT01_c_val2 | `FT01_c_val2 allowed (16 of 16) 248739ms` | pass 3 |
| 3 | FT01_d_trap_before_both | `FT01_d_trap_before_both allowed (14 of 14) 625267ms` | pass 2 |
| 4 | FT01_e_trap_after_both | `FT01_e_trap_after_both allowed (14 of 14) 462831ms` | pass 2 |
| 5 | FT02_a_notrap_lane_yx | `FT02_a_notrap_lane_yx allowed (8 of 8) 42686ms` | pass 1 |
| 6 | FT02_b_notrap_val2 | `FT02_b_notrap_val2 allowed (8 of 8) 78219ms` | pass 1 |
| 7 | FT02_c_notrap_nopreamble | `FT02_c_notrap_nopreamble allowed (4 of 4) 8204ms` | pass 1 |
| 8 | FT03_a_fence_ww_trap | `FT03_a_fence_ww_trap forbidden (0 of 16) 367630ms` | pass 2 |
| 9 | FT03_b_fence_rwrw_notrap | `FT03_b_fence_rwrw_notrap forbidden (0 of 8) 18297ms` | pass 1 |
| 10 | FT03_c_fence_after_trap | `FT03_c_fence_after_trap forbidden (0 of 16) 145784ms` | pass 2 |
| 11 | FT04_a_sb_trap | `FT04_a_sb_trap allowed (14 of 14) 413099ms` | pass 2 |
| 12 | FT04_b_sb_notrap | `FT04_b_sb_notrap allowed (8 of 8) 22527ms` | pass 1 |
| 13 | FT04_c_sb_trap_fence | `FT04_c_sb_trap_fence forbidden (0 of 16) 475420ms` | pass 1 |
| 14 | FT05_a_lb_trap | `FT05_a_lb_trap allowed (14 of 14) 313269ms` | pass 1 |
| 15 | FT05_b_lb_notrap | `FT05_b_lb_notrap allowed (8 of 8) 13733ms` | pass 1 |
| 16 | FT06_a_replay_val2 | `FT06_a_replay_val2 allowed (7 of 7) 36505ms` | pass 1 |
| 17 | FT06_b_replay_no_sentinel | `FT06_b_replay_no_sentinel forbidden (0 of 7) 5157ms` | pass 1 |
| 18 | FT06_c_replay_then_symbolic | `FT06_c_replay_then_symbolic allowed (7 of 7) 77194ms` | pass 1 |
| 19 | FT07_a_rfi_across_trap | `FT07_a_rfi_across_trap allowed (7 of 7) 66230ms` | pass 1 |
| 20 | FT07_b_rfi_across_trap_stale | `FT07_b_rfi_across_trap_stale forbidden (0 of 7) 3020ms` | pass 1 |
| 21 | FT08_a_coRR_inverted | `FT08_a_coRR_inverted forbidden (0 of 16) 20145ms` | pass 1 |
| 22 | FT08_b_coRR_ordered | `FT08_b_coRR_ordered allowed (16 of 16) 196879ms` | pass 1 |
| 23 | FT09_a_rfe_post_replay | `FT09_a_rfe_post_replay allowed (7 of 7) 76325ms` | pass 1 |
| 24 | FT09_b_rfe_pre_trap | `FT09_b_rfe_pre_trap allowed (7 of 7) 230387ms` | pass 1 |
| 25 | FT09_c_rfe_post_replay_unseen | `FT09_c_rfe_post_replay_unseen allowed (7 of 7) 47319ms` | pass 1 |
| 26 | FT10_a_handler_store_after_csrw | `FT10_a_handler_store_after_csrw allowed (14 of 14) 357341ms` | pass 3 |
| 27 | FT10_b_handler_store_before_csrw | `FT10_b_handler_store_before_csrw allowed (14 of 14) 666441ms` | pass 2 |
| 28 | FT11_a_obs_addr_dep | `FT11_a_obs_addr_dep allowed (21 of 21) 315702ms` | pass 1 |
| 29 | FT11_b_obs_ctrl_dep | `FT11_b_obs_ctrl_dep allowed (14 of 28) 346734ms` | pass 1 |
| 30 | FT11_c_obs_po_only | `FT11_c_obs_po_only allowed (14 of 14) 206776ms` | pass 1 |
| 31 | FT12_a_mp_reference | `FT12_a_mp_reference allowed (4 of 4) 4663ms` | pass 1 |
| 32 | FT12_b_sb_reference | `FT12_b_sb_reference allowed (4 of 4) 2894ms` | pass 1 |
| 33 | FT12_c_lb_reference | `FT12_c_lb_reference allowed (4 of 4) 2616ms` | pass 1 |

**33 verdicts: 26 `allowed`, 7 `forbidden`. 0 errors, 0 timeouts, 0 tests without a summary line.**

### Per-template delivery — no template resisted instantiation

| Template | Instances | Verdicts | Errors |
|---|---|---|---|
| FT01 MP + trap between the producer's stores | 4 | 4 | 0 |
| FT02 MP, no trap (control) | 3 | 3 | 0 |
| FT03 MP + explicit fence (calibration) | 3 | 3 | 0 |
| FT04 SB across a trap | 3 | 3 | 0 |
| FT05 LB across a trap | 2 | 2 | 0 |
| FT06 fault → repair → replay, value-discriminated | 3 | 3 | 0 |
| FT07 replay + same-hart load-back (rfi) | 2 | 2 | 0 |
| FT08 coherence spanning the trap boundary | 2 | 2 | 0 |
| FT09 remote observer of the replayed store (rfe) | 3 | 3 | 0 |
| FT10 handler CSR-write vs a memory access | 2 | 2 | 0 |
| FT11 observer dependency-ordered vs fence-ordered | 3 | 3 | 0 |
| FT12 no-fault reference run | 3 | 3 | 0 |
| **Total** | **33** | **33** | **0** |

---

## 2. Every intermediate `error`, and why the final numbers are still honest

Nine of the 33 tests came back `error` before they came back with a verdict. Suppressing that would
be dishonest even though the final tally is clean, so the full history is here.

### 2.1 What the `error`s were

isla's `-s` is a per-SMT-call timeout in **wall-clock seconds**, so it is sensitive to how much of
the machine each z3 call actually gets. When a call exceeds it, isla prints

```
Error in parsing smt output to get allowed/forbidden ...
z3 head: 'timeout
'...
```

and reports the test as **`error`**. Pass 1 ran six isla instances at `-T 4` on a 32-core host,
which inflated every z3 call; nine tests timed out that way. Passes 2 and 3 lowered the concurrency
and raised `-s`.

| Test | pass 1 (`-s 300 -T 4`, 6-way) | pass 2 (`-s 900 -T 8`, 2-way) | pass 3 (`-s 2400 -T 14`, 2-way) |
|---|---|---|---|
| FT01_b_lane_yx | `FT01_b_lane_yx error (12 of 14) 662073ms` | `allowed (14 of 14) 402918ms` | — |
| FT01_c_val2 | `FT01_c_val2 error (13 of 16) 702305ms` | `FT01_c_val2 error (15 of 16) 901180ms` | `allowed (16 of 16) 248739ms` |
| FT01_d_trap_before_both | `FT01_d_trap_before_both error (12 of 14) 617793ms` | `allowed (14 of 14) 625267ms` | — |
| FT01_e_trap_after_both | `FT01_e_trap_after_both error (11 of 14) 629437ms` | `allowed (14 of 14) 462831ms` | — |
| FT03_a_fence_ww_trap | `FT03_a_fence_ww_trap error (0 of 16) 401864ms` | `forbidden (0 of 16) 367630ms` | — |
| FT03_c_fence_after_trap | `FT03_c_fence_after_trap error (0 of 16) 398121ms` | `forbidden (0 of 16) 145784ms` | — |
| FT04_a_sb_trap | `FT04_a_sb_trap error (8 of 14) 735406ms` | `allowed (14 of 14) 413099ms` | — |
| FT10_a_handler_store_after_csrw | `FT10_a... error (12 of 14) 570024ms` | `FT10_a... error (13 of 14) 1043556ms` | `allowed (14 of 14) 357341ms` |
| FT10_b_handler_store_before_csrw | `FT10_b... error (12 of 14) 646577ms` | `allowed (14 of 14) 666441ms` | — |

The `(n of N)` counts show these were **partial solves, not modelling failures**: isla built the
full candidate set, executed the trap/handler/replay sequence, and solved most candidates — e.g.
`FT01_c_val2` reached 15 of 16 before the last one exceeded even a 900-second budget.

### 2.2 Why re-running is not verdict-shopping

The failure mode is **one-directional**. A resource limit can only *prevent* a verdict; it cannot
manufacture one, and it cannot turn a `forbidden` into an `allowed` or the reverse. Concretely:

- **No test that produced a verdict was ever re-run.** Each of the 33 rows in §1 is the *first*
  verdict that test produced; passes 2 and 3 were applied **only** to inputs whose previous result
  was `error`.
- **No test changed its verdict between passes**, because none was given the chance to.
- Where two `error`s precede a verdict, the candidate-solved count rises monotonically
  (13→15→16 for FT01_c, 12→13→14 for FT10_a), which is what a pure resource limit looks like.

If the rule were instead "a test counts only if it returns a verdict on the first attempt at
`-s 300` under 6-way load", the count would be **24** new tests rather than 33. That number is
recorded here too so the reader can pick their own bar.

### 2.3 Host calibration — this host is ~5× slower than the one the S1-v2 matrix was measured on

The reference test reproduces its recorded **verdict** but not its recorded **runtime**:

| Run | Verbatim |
|---|---|
| recorded in `model/S1v2_trap_differential_2026-07-30.md`, `-s 60 -T 4` | `S1v2_trap_mp allowed (14 of 14) 53952ms` |
| this host, `-s 60 -T 4` | `S1v2_trap_mp error (7 of 14) 214232ms` (z3 `timeout`) |
| this host, `-s 300 -T 8` | `S1v2_trap_mp allowed (14 of 14) 288931ms` |

So on this host `-s 60` is simply not a viable budget for the trap family, and the suite was run at
`-s 300` and above. The verdict is unchanged; only the budget needed to reach it differs.

---

## 3. Repo-wide runnable-test count — re-measured, not cited

Every pre-existing litmus file in the repository was re-run here. Two IR snapshots are involved and
the difference between them is load-bearing, so it is recorded rather than quietly resolved.

### 3.1 A correction to a recorded baseline: `rv64d.ir` no longer runs the RVWMO suite

`model/M3_oracle_remeasure_2026-07-25.md` records **36/36 verdicts, 0 errors** on
`/root/restartv/isla-snapshots-regen/rv64d.ir` with `configs/riscv64_g2.toml` and the stock
`riscv.cat`. **That does not reproduce on this host.** All 36 come back `error (0 of 1)` in 5–19 s
— far too fast to be a timeout — with:

```
Warning: Could not find register __isla_always_aligned when parsing registers.defaults in configuration
error: Symbolic (bit)vector length in subrange_internal
Backtrace: zisla_footprint
zisla_footprint_no_init
zexecute
zvmem_write
zvmem_write_addr
```

This is exactly the crash `model/split_misaligned_footprint_fix.patch` exists to fix: upstream
`split_misaligned` computes `bytes_per_access = 2^count_trailing_zeros(vaddr_bits)`, a **symbolic**
bitvector width whenever the store address is symbolic — which is always, in a litmus footprint.
`rv64d.ir` does not carry the fix (and does not define `__isla_always_aligned`, so the config's
aligned-access shortcut cannot rescue it). `rv64d_g58.ir` **does** carry it.

The prediction that follows is confirmed exactly: on `rv64d.ir` the only pre-existing trap tests
that still return verdicts are the three whose sole memory accesses are to the **concrete** address
`0x84001000` — `diag_umode_exit_fixed`, `trap_store_faultB1_defaults`, `trap_store_faultB2_replay` —
while every test with a **symbolic** store address errors.

**Consequence for the count:** the measurement below uses `rv64d_g58.ir`, the IR that carries the
fix and the IR the frozen suite itself uses. The `rv64d.ir` failure is preserved in this document
rather than discarded, because it corrects a number recorded elsewhere in the repo.

### 3.2 `litmus/rvwmo-suite/` — 36 files, **36 verdicts, 0 errors**

IR `rv64d_g58.ir`, config `configs/riscv64_g2.toml`, cat `web/client/dist/riscv.cat`, `-s 300 -T 4`.

| Test | Verbatim | Test | Verbatim |
|---|---|---|---|
| 2+2W | `2+2W allowed (4 of 4) 33888ms` | MP+po+addr | `MP+po+addr allowed (4 of 4) 22321ms` |
| 2+2W+fence.rw.rw+po | `2+2W+fence.rw.rw+po allowed (4 of 4) 27687ms` | MP+po+ctrl | `MP+po+ctrl allowed (4 of 8) 29071ms` |
| 2+2W+fence.rw.rws | `2+2W+fence.rw.rws forbidden (0 of 4) 37375ms` | MP+po+fence.rw.rw | `MP+po+fence.rw.rw allowed (4 of 4) 2820ms` |
| LB | `LB allowed (4 of 4) 2362ms` | R | `R allowed (4 of 4) 4083ms` |
| LB+ctrl+po | `LB+ctrl+po allowed (4 of 8) 26813ms` | R+fence.rw.rw+po | `R+fence.rw.rw+po allowed (4 of 4) 5105ms` |
| LB+ctrls | `LB+ctrls forbidden (0 of 16) 24289ms` | R+fence.rw.rws | `R+fence.rw.rws forbidden (0 of 4) 6804ms` |
| LB+data+ctrl | `LB+data+ctrl forbidden (0 of 8) 28752ms` | R+po+fence.rw.rw | `R+po+fence.rw.rw allowed (4 of 4) 5154ms` |
| LB+data+po | `LB+data+po allowed (4 of 4) 1903ms` | S | `S allowed (4 of 4) 2247ms` |
| LB+datas | `LB+datas forbidden (0 of 4) 2613ms` | S+fence.rw.rw+ctrl | `S+fence.rw.rw+ctrl forbidden (0 of 8) 7450ms` |
| LB+fence.rw.rw+ctrl | `LB+fence.rw.rw+ctrl forbidden (0 of 8) 17285ms` | S+fence.rw.rw+data | `S+fence.rw.rw+data forbidden (0 of 4) 4631ms` |
| LB+fence.rw.rw+data | `LB+fence.rw.rw+data forbidden (0 of 4) 4078ms` | S+fence.rw.rw+po | `S+fence.rw.rw+po allowed (4 of 4) 4798ms` |
| LB+fence.rw.rw+po | `LB+fence.rw.rw+po allowed (4 of 4) 10202ms` | S+fence.rw.rws | `S+fence.rw.rws forbidden (0 of 4) 3895ms` |
| LB+fence.rw.rws | `LB+fence.rw.rws forbidden (0 of 4) 6872ms` | S+po+ctrl | `S+po+ctrl allowed (4 of 8) 3975ms` |
| MP | `MP allowed (4 of 4) 3232ms` | S+po+data | `S+po+data allowed (4 of 4) 1313ms` |
| MP+fence.rw.rw+addr | `MP+fence.rw.rw+addr allowed (4 of 4) 47023ms` | S+po+fence.rw.rw | `S+po+fence.rw.rw allowed (4 of 4) 3041ms` |
| MP+fence.rw.rw+ctrl | `MP+fence.rw.rw+ctrl allowed (4 of 8) 29065ms` | SB | `SB allowed (4 of 4) 2206ms` |
| MP+fence.rw.rw+po | `MP+fence.rw.rw+po allowed (4 of 4) 29630ms` | SB+fence.rw.rw+po | `SB+fence.rw.rw+po allowed (4 of 4) 5164ms` |
| MP+fence.rw.rws | `MP+fence.rw.rws forbidden (0 of 4) 28161ms` | SB+fence.rw.rws | `SB+fence.rw.rws forbidden (0 of 4) 5109ms` |

**Side observation, flagged as unconfirmed and NOT part of the D-c count.** Against the herd `refs`
oracle these 36 now score **35/36**, where `model/M3_oracle_remeasure_2026-07-25.md` scored 31/36 on
`rv64d.ir`. The four newly-matching tests are exactly the **data**-dependency ones — `LB+datas`,
`LB+data+ctrl`, `LB+fence.rw.rw+data`, `S+fence.rw.rw+data` — which now return `forbidden` as RVWMO
requires, instead of the previously recorded `allowed`. The single remaining mismatch is the
**address**-dependency test `MP+fence.rw.rw+addr allowed (4 of 4)`, expected `forbidden`. If this
holds up it means the data-dependency extraction gap is closed on `rv64d_g58.ir` and only the
addr-dependency gap remains. It was not the object of this task, it has been measured once, and it
should be independently re-run before anything is built on it.

### 3.3 `litmus/trap-scoping/` — 13 test files, **11 verdicts, 2 non-runnable**

The directory holds 18 `.toml` files; **5 are configs, not tests** (`riscv64_g2_pmp`,
`riscv64_g2_trap`, `riscv64_g2_trap_umode`, `riscv64_g2_trap_umode_defaults`,
`riscv64_g2_trap_umode_ipo`) and are excluded from the count.

Each test was run with the recipe its own provenance document specifies. Where that recipe named
`rv64d.ir` and hit the §3.1 footprint crash, a second attempt on `rv64d_g58.ir` was made and is the
one that counts; both lines are shown.

| Test | Config / cat | Verbatim | Counted |
|---|---|---|---|
| S1_mp | `riscv64_g2.toml` / `riscv_s1_nodrain.cat` | rv64d.ir: `S1_mp error (0 of 1) 30386ms` → g58: `S1_mp allowed (4 of 4) 49051ms` | ✔ |
| S1_control_fence | `riscv64_g2.toml` / `riscv_s1_nodrain.cat` | rv64d.ir: `S1_control_fence error (0 of 1) 6165ms` → g58: `S1_control_fence forbidden (0 of 4) 56216ms` | ✔ |
| S1v2_trap_mp | ipo / `riscv_s1v2_nodrain.cat` | `S1v2_trap_mp allowed (14 of 14) 465459ms` | ✔ |
| S1v2_control_notrap | ipo / `riscv_s1v2_nodrain.cat` | `S1v2_control_notrap allowed (8 of 8) 35246ms` | ✔ |
| S1v2_control_fence | ipo / `riscv_s1v2_nodrain.cat` | `S1v2_control_fence forbidden (0 of 16) 254974ms` | ✔ |
| trap_ecall_working | `riscv64_g2_trap.toml` / `riscv.cat` | rv64d.ir: `trap-ecall error (0 of 1) 4056ms` → g58: `trap-ecall allowed (4 of 4) 8890ms` | ✔ |
| trap_ecall | `riscv64_g2_trap.toml` / `riscv.cat` | rv64d.ir: `trap-ecall error (0 of 1) 3470ms` → g58: `trap-ecall forbidden (0 of 4) 8511ms` | ✔ |
| trap_store_faultA | `riscv64_g2_trap.toml` / `riscv.cat` | rv64d.ir: `trap-store-faultA error (0 of 1) 4708ms` → g58: `trap-store-faultA allowed (4 of 4) 8927ms` | ✔ |
| trap_store_faultB1_defaults | `..._umode_defaults.toml` / `riscv.cat` | `trap-store-faultB1 allowed (6 of 6) 2209ms` | ✔ |
| trap_store_faultB2_replay | `..._umode_defaults.toml` / `riscv.cat` | `trap-store-faultB2-replay allowed (7 of 7) 2300ms` | ✔ |
| diag_umode_exit_fixed | `..._umode_defaults.toml` / `riscv.cat` | `diag-umode-exit allowed (3 of 3) 452ms` | ✔ |
| **trap_store_faultB1** | `..._umode.toml` / `riscv.cat` | rv64d.ir: `trap-store-faultB1 error (0 of 6) 1158ms`; g58: `NO-SUMMARY-LINE rc=137` (**OOM-killed**) | ✘ |
| **diag_umode_exit** | `..._umode.toml` / `riscv.cat` | rv64d.ir: `diag-umode-exit error (0 of 3) 419ms`; g58: `NO-SUMMARY-LINE rc=137` (**OOM-killed**) | ✘ |

The two non-runnable files are **known-superseded, not new breakage**: both use
`riscv64_g2_trap_umode.toml`, the config *without* concrete GPR `[registers.defaults]`, whose
`pmpWriteCfgReg` fork explosion is documented in `model/M3_trap_umode_2026-07-24.md` as precisely
the reason `riscv64_g2_trap_umode_defaults.toml` was created. Their fixed counterparts
(`trap_store_faultB1_defaults`, `diag_umode_exit_fixed`) both run. `rc=137` is SIGKILL from the
kernel OOM killer — the documented fork tower — not a timeout.

One caveat on `trap_ecall`: it returns a verdict (`forbidden (0 of 4)`), so by the stated rule it
counts as runnable, but that `forbidden` is degenerate. The file sets `mtvec` via a litmus
`reset = {...}`, a path that is dead in this snapshot (documented in `trap_ecall_working`'s own
header), so its asserted outcome is simply unreachable. It is a runnable test with a
correct-but-uninformative verdict, and nothing should be built on it.

### 3.4 Repo-wide tally

| Group | Test files | Yield a verdict | Do not |
|---|---|---|---|
| `litmus/rvwmo-suite/` (standard RVWMO, oracle calibration) | 36 | **36** | 0 |
| `litmus/trap-scoping/` (excl. 5 config files) | 13 | **11** | 2 |
| `litmus/frozen-suite/` (**new**, template-instantiated) | 33 | **33** | 0 |
| **Total** | **82** | **80** | **2** |

**Repo-wide runnable tests: 80.** Frozen floor 60 — cleared with a margin of 20, inside the 60–150
band. Before this work the comparable figure was 48 files, of which 0 were instantiated from
RESTART-V templates and the ≥10-template requirement had never been demonstrated.

---

## 4. What the new verdicts actually say

All new verdicts are under `riscv_s1v2_nodrain.cat` — **stock RVWMO with the trap events visible but
no drain clause** — so they characterise the *no-drain* completion. That is the right baseline: the
drain completion's job is to differ from it, and until now that comparison existed for exactly one
shape (MP).

### 4.1 The trap boundary supplies no ordering of its own, in all three shapes

| Shape | across a trap | no trap | with a fence |
|---|---|---|---|
| MP (W→W) | `FT01_b allowed (14 of 14)` | `FT02_a allowed (8 of 8)` | `FT03_a forbidden (0 of 16)` |
| SB (W→R) | `FT04_a allowed (14 of 14)` | `FT04_b allowed (8 of 8)` | `FT04_c forbidden (0 of 16)` |
| LB (R→W) | `FT05_a allowed (14 of 14)` | `FT05_b allowed (8 of 8)` | — |

Each row is a self-contained three-cell control: the trap and no-trap columns **agree**, and the
fence column **flips**. Agreement is the expected answer under a no-drain completion; the flip is
the calibration proving the decider is not stuck. Extending this to W→R and R→W is new — the
pre-existing S1-v2 differential covered W→W only, so "the trap boundary does not act as a store
buffer drain" (`FT04_a` vs `FT04_c`) and "the trap boundary does not serialise the pipeline"
(`FT05_a`) are measured here for the first time.

### 4.2 Trap position is invisible to the no-drain completion — by construction, and now checkably

`FT01_d allowed (14 of 14)` (trap before both stores), `FT01_e allowed (14 of 14)` (trap after both),
`FT01_b allowed (14 of 14)` (trap between them). Under `riscv_s1v2_nodrain.cat` all three must
agree, because that cat contains no clause mentioning `[TRAP]` at all — and they do.

These three exist to become a **positional discriminator** the moment they are re-run under
`riscv_s1v2_drain.cat`, where `trap_drain = ([M];po;[TRAP]);([TRAP];po;[XRET]);([XRET];po;[M])` is
non-empty between the two stores **only** for `FT01_b`. If the drain cat flips `FT01_b` to
`forbidden` while leaving `FT01_d` and `FT01_e` `allowed`, that isolates the drain edge to the
ordering-relevant slot far more sharply than the existing trap/no-trap control can. **That run has
not been performed** — this suite makes it a one-command follow-up, and nothing in this document
claims its result.

### 4.3 A fence survives the trap/handler/replay round trip

`FT03_c forbidden (0 of 16)` places `fence rw,rw` **between the replayed faulting store and the flag
store** — so the trap, the handler, and the `mret` all sit between the DATA store and the fence —
and the MP cycle is still closed. The trap round trip does not swallow the fence's ordering
contribution. `FT03_a forbidden (0 of 16)` sharpens this: a bare `fence w,w`, the minimal fence that
supplies a W→W edge, is enough, so the decider honours the fence's actual predecessor/successor sets
rather than treating any fence as a full barrier.

### 4.4 The replay is real, and the suite can prove a negative

Three discriminating pairs split, each varying only the asserted outcome over an identical program:

| Question | Positive | Negative |
|---|---|---|
| does the replayed store commit, and did the handler run? | `FT06_a_replay_val2 allowed (7 of 7)` | `FT06_b_replay_no_sentinel forbidden (0 of 7)` |
| does a pre-trap store survive for the same hart? | `FT07_a_rfi_across_trap allowed (7 of 7)` | `FT07_b_rfi_across_trap_stale forbidden (0 of 7)` |
| is coherence preserved across the boundary? | `FT08_b_coRR_ordered allowed (16 of 16)` | `FT08_a_coRR_inverted forbidden (0 of 16)` |

`FT06_a` is the strongest: the replayed store writes **2**, a value only the re-executed instruction
can produce, and the assertion demands both that the load-back reads 2 *and* that the handler
sentinel `x1 = 0x2A` is set. `FT06_b` demands the read-back **without** the sentinel and is
`forbidden` — so the read-back is not satisfiable by anything except a genuine handler-repaired
replay. `FT07_b forbidden` shows the trap boundary creates no exception to sc-per-location, and
`FT08_a forbidden` shows a coherence-inverted observation of a coWW pair straddling the boundary is
rejected while `FT08_b` accepts the coherence-respecting one.

### 4.5 The observer's freedom is measured, not assumed

`FT09_a allowed (7 of 7)` (a remote hart **does** see the post-replay store) and
`FT09_c allowed (7 of 7)` (it **does not**) are *both* allowed. This is the non-vacuity check the
rest of the suite leans on: an unordered observer must be free in both directions, and if `FT09_c`
had come back `forbidden` the harness would have been imposing an inter-hart ordering RVWMO does not
have, which would put every `allowed` elsewhere in this document in question. `FT09_b allowed
(7 of 7)` adds that a **pre-trap** store is externally visible too, so the boundary discards neither
side.

### 4.6 Observer-side ordering — one honest non-result

`FT11_a` (address dependency) `allowed (21 of 21)`, `FT11_b` (control dependency)
`allowed (14 of 28)`, `FT11_c` (bare program order) `allowed (14 of 14)`: none of the three orders
the observer's two loads, which is why FT01's *fenced* observer is what makes FT03's `forbidden`
reachable at all.

- `FT11_b` is **architecturally correct**: RVWMO's control rule is `r11 = [M];ctrl;[W]`; it orders a
  load before a later *store*, not before a later *load*.
- `FT11_a` is **not attributable** from this test alone. §3.2 shows the addr-dependency extraction
  gap is still present on this pipeline (`MP+fence.rw.rw+addr allowed`, expected `forbidden`), so
  `FT11_a`'s `allowed` could be the architecture or could be the tool. It is reported as a
  measurement and carries no claim about the trap.

### 4.7 Handler CSR-write ordering — the pair completes, with a null result

`FT10_a allowed (14 of 14)` (handler's store **after** `csrw pmpaddr0`) and `FT10_b allowed
(14 of 14)` (the same store **before** it) agree. This is the one pair in the suite that moves a
`sail_write_CSR` event across a memory event while holding TRAP, XRET and the three memory accesses
fixed, so it isolates the CSRW event's ordering contribution — and under the no-drain completion
that contribution is **nil**, which is the expected answer since `riscv_s1v2_nodrain.cat` has no
clause mentioning `[CSRW]`. It also establishes something not previously shown: the M-mode handler's
**own** memory access is unordered against the interrupted U-mode stream's earlier access, i.e. the
privilege change alone supplies no ordering. Like §4.2, this pair becomes informative under a
completion that *does* constrain `[CSRW]`; no such run is claimed here.

---

## 5. Reproduction

Scripts, in this directory, exactly as used:

| Script | What it does |
|---|---|
| `run_frozen_suite.sh` | runs one or more frozen-suite tests, records the verbatim summary line |
| `run_all.sh` | pass 1 — all 33 tests, 6 concurrent, `-s 300 -T 4` |
| `retry_errors.sh` | pass 2 — only the tests that came back `error`, 2 concurrent, `-s 900 -T 8` |
| `retry_final.sh` | pass 3 — the two still outstanding, 2 concurrent, `-s 2400 -T 14` |
| `run_repo_baseline.sh` | one pre-existing test, with the recipe its provenance document names |
| `run_baseline_all.sh` | the whole pre-existing corpus |
| `run_trap_baseline_g58.sh` | second attempt on `rv64d_g58.ir` for the trap-scoping tests that hit the §3.1 footprint crash |

Environment: WSL2 Ubuntu-22.04, 32 cores, 15 GB RAM; `isla-axiomatic` release build at
`/root/restartv/isla/target/release/`; IR snapshots at `/root/restartv/isla-snapshots-regen/`
(`rv64d_g58.ir`, 14,973,012 bytes). Use **literal** absolute paths — shell-variable expansion is
mangled through the Windows→WSL bridge.

**Not modified by this work:** no Sail source, no IR, no `.cat` file, and no pre-existing litmus or
config file was changed. The frozen suite consists entirely of new files plus the runner scripts,
and it reuses `litmus/trap-scoping/riscv64_g2_trap_umode_ipo.toml` and
`litmus/cat/riscv_s1v2_nodrain.cat` as they stand. In particular the `in_program_order` modelling
commitment disclosed in `model/S1v2_trap_differential_2026-07-30.md` §3(b) is **inherited, not
re-argued**: every trap verdict above is conditional on it.
