# Early-write suite: results (2026-11-04)

Reviewer request (external review R1, `rounds/fmsd/review_ext_R1.md`): one experiment with early writes,
two duplicate lane groups and a remote reader, reporting reads and final values. Paper: Section 8,
`sec:eval-early`, Table `tab:early`.

`error` ≠ `forbidden` ≠ `timeout` ≠ `allowed`. A test counts only if Isla itself prints `allowed` or
`forbidden`. Every line below is the verbatim isla-axiomatic summary line.

## Setup

- Isla axiomatic, IR `rv64d_g58.ir`, config `litmus/trap-scoping/riscv64_g2_trap_umode_ipo.toml`, Cat
  model `litmus/cat/riscv_s1v2_nodrain.cat`: the same recipe as the trap suite (`frozen-suite/`).
- Runner `run_ew.sh` (`-s 2400`, 6 to 12 threads, three tests concurrently).
- Isla ran inside the Ubuntu-22.04 root filesystem, mounted read-only and entered with chroot from
  Ubuntu-24.04 (`chroot_drive.sh`, `chroot_run.sh`), because Ubuntu-22.04 no longer starts
  (`Wsl/Service/E_UNEXPECTED`, 2026-11-04; its disk and Isla binary are intact). Calibration: `EW_BN_r575`
  gives the same line in the chroot as in the distro (`forbidden (0 of 20)`, `dbg_EW_BN_r575.log`).

## The 20 tests

| Test | Program | Condition | Expected |
|---|---|---|---|
| EW_AF_r00/r06/r50/r56 | faulting, lanes 2 and 3 early, reader hart 1 | hart 1 reads (0,0)/(0,6)/(5,0)/(5,6), handler mark | allowed |
| EW_AN_r00/r06/r50/r56 | fault-free, each lane once, reader hart 1 | same reads | allowed |
| final/EW_AF_fin56, fina0, finb0 | faulting, no reader | `*a=5 & *b=6` (with mark) / `*a=0` / `*b=0` | allowed / forbidden / forbidden |
| final/EW_AN_fin56, fina0, finb0 | fault-free, no reader | same | same |
| EW_BF_r575 | faulting, lane 2 only, remote writer of 7, reader reads lane 2 three times | 5, 7, 5 with mark | allowed (Prop. 3) |
| EW_BN_r575 | fault-free counterpart | 5, 7, 5 | forbidden (Prop. 3) |
| final/EW_BF_fin5, fin7 | faulting, lane 2 only, remote writer, no reader | `*a=5` / `*a=7` (with mark) | allowed |
| final/EW_BN_fin5, fin7 | fault-free counterpart | `*a=5` / `*a=7` | allowed |

## Verdicts (final run, `RESULTS_mf_raw.txt`, solver option `smt.macro_finder`)

All 20 tests reach a verdict, and every verdict is the expected one.

```
EW_AF_r00	EW_AF_r00 allowed (18 of 18) 1885ms	6s
EW_AF_r06	EW_AF_r06 allowed (18 of 18) 2114ms	6s
EW_AF_r50	EW_AF_r50 allowed (18 of 18) 1860ms	6s
EW_AF_r56	EW_AF_r56 allowed (18 of 18) 2453ms	7s
EW_AN_r00	EW_AN_r00 allowed (10 of 10) 711ms	5s
EW_AN_r06	EW_AN_r06 allowed (10 of 10) 792ms	5s
EW_AN_r50	EW_AN_r50 allowed (10 of 10) 630ms	4s
EW_AN_r56	EW_AN_r56 allowed (10 of 10) 655ms	5s
EW_AF_fin56	EW_AF_fin56 allowed (9 of 9) 1679ms	6s
EW_AF_fina0	EW_AF_fina0 forbidden (0 of 9) 1795ms	5s
EW_AF_finb0	EW_AF_finb0 forbidden (0 of 9) 1588ms	5s
EW_AN_fin56	EW_AN_fin56 allowed (5 of 5) 681ms	5s
EW_AN_fina0	EW_AN_fina0 forbidden (0 of 5) 612ms	5s
EW_AN_finb0	EW_AN_finb0 forbidden (0 of 5) 688ms	4s
EW_BF_r575	EW_BF_r575 allowed (32 of 32) 3167ms	7s
EW_BN_r575	EW_BN_r575 forbidden (0 of 20) 1043ms	5s
EW_BF_fin5	EW_BF_fin5 allowed (16 of 16) 1320ms	6s
EW_BF_fin7	EW_BF_fin7 allowed (16 of 16) 1009ms	6s
EW_BN_fin5	EW_BN_fin5 allowed (10 of 10) 605ms	5s
EW_BN_fin7	EW_BN_fin7 allowed (10 of 10) 455ms	4s
```

## Default solver settings (without `smt.macro_finder`)

19 of the 20 tests were also run with Isla's default z3 call. All 19 give the same verdict with the same
candidate counts (`RESULTS_raw.txt`, `final/FINAL_raw.txt`):

```
EW_AF_r50	EW_AF_r50 allowed (18 of 18) 292884ms	300s
EW_AF_r00	EW_AF_r00 allowed (18 of 18) 401318ms	408s
EW_AF_r06	EW_AF_r06 allowed (18 of 18) 316003ms	322s
EW_AF_r56	EW_AF_r56 allowed (18 of 18) 535144ms	540s
EW_BF_r575	EW_BF_r575 error (31 of 32) 637820ms	645s
```

The twentieth, `EW_BF_r575`, returned `error (31 of 32)` twice (`dbg_EW_BF_r575.log`: z3 head `unknown`,
`model is not available`). Diagnosis (`diag/`):

- `diag/BF_z3_each.txt`: z3 on each of the 32 saved candidate files: 31 `sat`, candidate 10 `unknown`
  after 449 s. So the error comes from one candidate on which z3's quantifier instantiation gives up,
  not from a timeout (`-s 2400`).
- `diag/BF_c10_variants.txt`: candidate 10 under other z3 settings: `sat` with `smt.macro_finder=true`
  (1 s), `smt.ematching=false` (2 s) and random seeds 1, 2, 3; `unknown` or no answer with three
  other settings.
- `macro_finder.smt2` passes `(set-option :smt.macro_finder true)` through isla's `--extra-smt`, which
  places it after the assertions and before `check-sat` (checked on candidate 10: `sat`, 0 s).
  Macro finding is a satisfiability-preserving preprocessing step of z3.
- Cross-check on the trap suite: the 33 tests of `frozen-suite/` under `smt.macro_finder` give the same
  verdict and the same candidate counts as `frozen-suite/RESULTS.md`, 33 of 33, in 87 s in total
  (`diag/FT_mf_raw.txt`).

## Final-memory conditions: an Isla issue and how the tests avoid it

`isla-axiomatic/src/last_write_to.smt2` defines `*a = v` as: some event at address a with value v has no
`co` successor (or v is the initial value and IW has no `co` successor at a). The event is not required to
be a write, and loads have no `co` successors. So a load of a that reads the initial value 0 satisfies
`*a = 0`.

- `diag/DG_AN_fin_a0`: hart 0 stores 5 to a and reloads it (`0:x9 = 5`); `*a = 0` is still `allowed (12 of 12)`.
- Without loads, the encoding is sound for these tests: `2+2W+fence.rw.rws` (no loads) gives
  `forbidden (0 of 4)` under the same config (`diag/DIAG_raw.txt`).

The first final-memory tests (`dropped/`, with the reader hart) are therefore withdrawn. Their lines
(`dropped/pass1_memassert.txt`) include `EW_AF_fina0 allowed`, which is this spurious witness, and
`EW_AF_fin56 error` from the 8-bit literal below. The tests in `final/` contain no load of a or b
(generator `final/gen_final.py`).

## Attempt history (all lines kept)

1. `attempt1_raw.txt`, first two lines after the AN/BN block: `EW_AF_r00 error (0 of 18)`,
   `EW_BF_r575 error (0 of 32)`. Cause: the handler mark was compared with the 8-bit literal `0x2A`
   (z3: `Sorts (_ BitVec 64) and (_ BitVec 8) are incompatible`). Fixed with the 16-digit literal
   `0x000000000000002A`.
2. Detached overnight run (2026-11-03): no result lines; the WSL distro stopped and killed it.
3. 2026-11-04 08:45: launched in Ubuntu-24.04 by mistake (no Isla there); rc=127 for all five, no test
   ran (lines in `attempt1_raw.txt`).
4. Chroot run, default solver: AF 4 × allowed, BF `error (31 of 32)` (`RESULTS_raw.txt`).
5. `final/` pass 1 (`final/FINAL_raw_pass1.txt`): the B tests were generated with the remote writer
   renumbered to thread 1 but its reset pc left at thread 2's code address, so the writer ran no code
   (hence `EW_BN_fin7 forbidden`). Generator fixed; the four B tests rerun (`final/FINAL_raw.txt`).
6. Final run of all 20 under `smt.macro_finder` (`RESULTS_mf_raw.txt`), the verdicts above.
