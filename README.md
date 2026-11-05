# Artifact: Restarting a Faulting RISC-V Vector Store

This is the artifact of the paper

> Jiachen Shen and Hui Zhong. *Restarting a Faulting RISC-V Vector Store: A Contract and a Mechanized
> Refinement under RVWMO.* Submitted to Formal Methods in System Design.

Archived on Zenodo: [10.5281/zenodo.23966253](https://doi.org/10.5281/zenodo.23966253).

It contains the Rocq development, the 100 Isla litmus tests with their verbatim results, the Sail
patches used to build the Isla model, and the simulator runs of the fault, repair and replay path.

## Contents

| Path | Contents | Paper |
|---|---|---|
| `rocq/` | The Rocq development (51 files, Coq 8.15.0) and `verify.sh`. `VERIFY_LOG.txt` is the output of `verify.sh` for this version. | Sections 2 to 5, Appendix B |
| `litmus/rvwmo-suite/` | The 36 standard RVWMO tests (calibration). | Section 8.2, Appendix C |
| `litmus/frozen-suite/` | The 33 tests of the trap suite, their templates (`TEMPLATES.md`), run scripts and results (`RESULTS.md`). | Sections 8.5, 8.8, Appendix C |
| `litmus/trap-scoping/` | The earlier trap-scoping tests (11 runnable, 2 diagnostics), the tests of the drain differential, and the Isla configurations. | Sections 8.6, 8.8 |
| `litmus/early-write/` | The 20 tests of the early-write suite, the run scripts, the raw results and the diagnostics (`diag/`). `RESULTS.md` records every run, and `dropped/` keeps the first final-memory tests, which carried loads of the lanes and were replaced (Section 8.4). | Section 8.4, Table 6 |
| `litmus/cat/` | The Cat models: the no-drain and strict-drain completions and the trap tripwire. | Section 8.1 |
| `model/` | The three Sail patches and `REBUILD.md`, the recipe for the Isla model. | Section 8.1 |
| `sim/` | The test program, the contract handler, the measurement handler, the run harness and the traces of the five `sail_riscv_sim` runs; `handler_regs_cert.sh` checks the handler against the schema α. | Sections 8.3, 8.7 |

## Checking the proofs

Requires Coq 8.15.0 (for example from opam: `opam install coq.8.15.0`).

```
cd rocq
bash verify.sh
```

`verify.sh` deletes all compiled files, builds the 51 files in dependency order and runs
`Print Assumptions` on 81 headline results. It exits with status 0 and prints
`ALL GREEN: 51 files build, 81 headline theorems 0-axiom.` when every file builds and every headline
result is closed under the global context. `make` builds the same files through `_CoqProject`.

The numbered results of the paper and the Rocq theorems that prove them:

| Result | Rocq theorem (file) |
|---|---|
| Lemma 1 | `rvwmo_perbyte_coherence` (`Perbyte.v`); main model `Main_model_acyclic` (`L2_consistency.v`) |
| the mixed-size run | `ex_perbyte_ok`, `ex_union_cycle`, `ex_load_value` (`Perbyte_example.v`) |
| Theorem 2 | `ML_T1_refinement_pb` (`Perbyte.v`); union check `ML_T1_refinement`, token form `ML_T1_refinement_instantiated` (`ML_T1.v`) |
| union check implies per-byte check | `union_to_perbyte` (`Perbyte.v`) |
| Corollary 3 | `ML_T1_covers_single_lane` (`ML_T1.v`) |
| global adjacency fails | `natural_order_breaks_global_adj` (`ML_instance.v`) |
| Theorem 6 | `ML_stage2_endtoend_pb` (`Perbyte.v`); `endtoend_Cand_N_struct`, `endtoend_O2_lanes` (`ML_stage2.v`) |
| the PMP matching rule | `allows_iff_deciding_full`, `spec_example_denied`, `frozen_lanes_never_partial` (`Pmp_partial.v`) |
| Theorem 7 | `normal_instance_pos`; `normal_instance` for a total program order (`Normal_instance.v`) |
| premises inhabited, lane writes in program order | `ml2_T1_pb_instance`, `ml2_stage2_pb_instance`, `ml2_stage2_instance`, `ml2_normal_instance`, `ml2_instance_observation` (`ML_instance_2h.v`) |
| premises inhabited, lane writes of each attempt unordered | `mu_T1_pb_instance`, `mu_stage2_pb_instance`, `mu_stage2_instance`, `mu_normal_instance`, `mu_po_not_total` (`ML_instance_unord.v`) |
| Proposition 4 | `gamma_adj_needed_obs` (`Gamma_adj_obs.v`); final values `gamma_adj_needed_full` (`Gamma_adj_needed.v`) |
| Proposition 5 | `gamma_D_implies_gamma_adj` (`L2_gamma.v`) |
| trap-region erasure | `general_ctx_erasure` (`Ctx_erasure.v`) |
| orientation is forced | `replay_keeper_impossible_under_reexec` (`Reexec_orientation.v`) |
| the r2 case | `r2N_sub_r2F` (`PPO_frozen.v`) |
| the cyclic pattern | `alleged_counterexample_is_cyclic` (`R2_counterexample.v`) |
| register agreement and the duplicate clause | `alpha_regs_gives_Dup` (`Alpha_regs.v`) |
| clobbered data register | `ar_i_alpha_fails_when_data_clobbered` (`Alpha_regs_instance.v`) |

The comments in the Rocq sources are working notes written during the development. The statements
and proofs are what `verify.sh` checks.

## Running the litmus tests

The tests need Isla, Z3 4.8.12 and the Isla model of sail-riscv built as described in
`model/REBUILD.md`. The run scripts read three variables:

```
export ARTIFACT_ROOT=$(pwd)                                 # the root of this artifact
export ISLA=/path/to/isla/target/release/isla-axiomatic     # default: /root/restartv/isla/...
export ISLA_IR=/path/to/rv64d_g58.ir                        # default: /root/restartv/isla-snapshots-regen/...
```

Examples:

```
# trap suite (Section 8.5): one verdict line per test
bash litmus/frozen-suite/run_frozen_suite.sh out.txt litmus/frozen-suite/FT*.toml

# early-write suite (Section 8.4) with Z3's macro finder, budget 2400 s, 6 solver threads
bash litmus/early-write/run_ew.sh -x litmus/early-write/macro_finder.smt2 out.txt 2400 6 \
     $(sed 's|.*|litmus/early-write/&.toml|' litmus/early-write/LIST.txt)
```

Each script writes the verbatim Isla summary line of each test, for example
`EW_BF_r575 allowed (32 of 32)`. The recorded runs are in the `RESULTS*.md` and `*_raw.txt` files
next to the tests. Running times depend on the host and on the solver budget; the paper reports the
budgets used.

## Simulator runs

`sim/run_dr2.sh` assembles `sim/test.S` for the five configurations of Section 8.3 with GNU binutils
2.35.1 and runs each on the released `sail_riscv_sim` 0.13 with VLEN = 128. Set `SAIL_RISCV_SIM` to the
simulator binary. The `*.trace.log` and `*.stdout.log` files are the recorded traces, and
`results.txt` the recorded outcomes; the script overwrites them, so run it on a copy of `sim/`. `sim/test_contract.S` carries the three-instruction handler of
the contract, and `bash sim/handler_regs_cert.sh` (run from the artifact root) assembles it,
disassembles it and checks every architectural location it writes against α.

## License

MIT, see `LICENSE`.
