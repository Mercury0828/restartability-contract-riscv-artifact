# Rebuilding the Isla model

The litmus tests of the paper run on an Isla intermediate representation (IR) of sail-riscv, built
as follows. The IR itself (`rv64d_g58.ir`, about 15 MB) is not included; it is regenerated from the
sources below.

## Versions

| Component | Version |
|---|---|
| sail-riscv | `bacam/sail-riscv`, branch `202606-isla` ("Add Isla cmake targets"), commit `7b12a05` |
| Sail | 0.20.1 (opam package `sail.0.20.1`, OCaml 4.13.1) |
| isla-sail plugin | from `rems-project/isla`, `isla-sail` at commit `7f6882b` |
| Isla | `rems-project/isla`, master as of 2026-07-23, `cargo build --release` |
| Z3 | 4.8.12 |

## The three patches

Apply them in this order to a clean checkout of commit `7b12a05`:

1. `step_endcycle_isla_harness.patch` (`model/postlude/step.sail`). The symbolic step loop that Isla
   executes ends a cycle only when a hart waits. A retired instruction does not end one, so all
   instructions of a thread fall into one cycle and Isla rejects the test. The patch ends a cycle
   after every retired instruction.
2. `split_misaligned_footprint_fix.patch` (`model/sys/vmem_utils.sail`). It fixes the symbolic width
   of the misaligned-split path. Without it, four data-dependency tests of the calibration suite come
   out allowed against a forbidden reference.
3. `M3_g5_abstract_trap_events.patch`. It declares the trap-entry, exception-return and CSR-write
   events (`sail_trap`, `sail_mret`, `sail_write_CSR`) so that a Cat model can refer to them.

## Generating the IR

```bash
git clone https://github.com/bacam/sail-riscv.git sail-riscv-src
cd sail-riscv-src && git checkout 7b12a05
git apply <artifact>/model/step_endcycle_isla_harness.patch
git apply <artifact>/model/split_misaligned_footprint_fix.patch
git apply <artifact>/model/M3_g5_abstract_trap_events.patch

# build the isla-sail plugin against Sail 0.20.1
cd <isla>/isla-sail && opam exec -- make        # -> _build/default/sail_plugin_isla.cmxs

# generate the IR (the config rv64d_v256_e64.json comes from the sail-riscv config template,
# as in the generated_isla_rv64d cmake target of the branch)
cd <sail-riscv-src>/model
isla-sail --strict-var --strict-bitvector --strict-exponentials --require-version 0.20.1 \
  --isla-output-dir out -o rv64d --config out/rv64d_v256_e64.json --all-modules riscv.sail_project
# -> out/rv64d.ir, used as ISLA_IR (rv64d_g58.ir in the scripts)
```

## Checks

- `isla-footprint -A rv64d_g58.ir -C configs/riscv64_g2.toml -i "sw x7, 0(x8)"` returns write-memory
  events (it fails without patch 2).
- With `litmus/cat/riscv_trap.cat`, the test `litmus/trap-scoping/trap_store_faultB2_replay.toml` is
  forbidden (0 of 7); the tripwire axiom in that Cat file fires only when the trap events of patch 3
  are present.
