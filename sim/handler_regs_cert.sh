#!/usr/bin/env bash
# handler_regs_cert.sh — certificate that the CONTRACT handler satisfies alpha.
#
# WHICH BINARY THIS CERTIFIES, AND WHY IT CHANGED. It used to certify the handler in
# sim/test.S. That was wrong: test.S carries an INSTRUMENTED handler which records
# mcause/mepc/mtval/vstart, probes the lane after the faulting one, and keeps a trap counter -- eight
# regular memory accesses, one of them a read of the vector store's own destination array -- and which
# writes five temporaries without restoring them. Neither is compatible with alpha, whose memory-silence
# clause is what lets the erasure delete the trap region, and neither leaves the user-visible register
# state as it found it. test.S remains the DR-2 measurement harness; sim/test_contract.S
# carries the three-instruction handler that actually satisfies the contract, and this certifies THAT.
#
# Alpha_regs.v proves: if the handler image agrees with the pre-trap state on the base address
# register, the data vector register, vl, the element width and the mask, then the first attempt and
# the replay are a whole-footprint-equal duplicate pair. That is the antecedent the erasure theorems
# consume, and this script discharges its hypothesis for the CONCRETE handler by disassembling it and
# enumerating every architectural location it writes.
#
# It is a real check, not a restatement: it fails loudly if the handler ever grows an instruction that
# writes one of the store's inputs. Run from the repo root:  bash sim/handler_regs_cert.sh
#
# Requires the RISC-V toolchain (assembler + objdump) in WSL.

set -u
SRC="${1:-sim/test_contract.S}"
WORKDIR="/tmp/handler_regs_cert.$$"
fail=0

red()  { printf '\033[31m%s\033[0m\n' "$*"; }
grn()  { printf '  \033[32mok  \033[0m %s\n' "$*"; }
info() { printf '  \033[36m%s\033[0m %s\n' "$1" "$2"; }

[ -f "$SRC" ] || { red "MISSING SOURCE: $SRC"; exit 1; }

mkdir -p "$WORKDIR"
riscv64-unknown-elf-as -march=rv64g -o "$WORKDIR/h.o" "$SRC" \
    --defsym VTYPEI=0xD9 --defsym VL=4 --defsym K=2 --defsym FAULT=1 2>"$WORKDIR/as.err" || {
  red "ASSEMBLY FAILED"; cat "$WORKDIR/as.err"; rm -rf "$WORKDIR"; exit 1; }

riscv64-unknown-elf-objdump -d "$WORKDIR/h.o" > "$WORKDIR/dis.txt" 2>/dev/null

# ---- isolate the handler body: from the `handler:` label to the mret that returns to U-mode -------
# Symbols are local, so cut on the disassembly text between the handler entry and fail7_m.
hstart="$(grep -n '<handler>:' "$WORKDIR/dis.txt" | head -1 | cut -d: -f1)"
hend="$(grep -n '<handler_end>:' "$WORKDIR/dis.txt" | head -1 | cut -d: -f1)"
if [ -z "$hstart" ] || [ -z "$hend" ]; then
  red "CANNOT LOCATE HANDLER BODY in the disassembly (labels <handler> / <handler_end> not found)"
  rm -rf "$WORKDIR"; exit 1
fi
sed -n "$((hstart+1)),$((hend-1))p" "$WORKDIR/dis.txt" | grep -E '^\s+[0-9a-f]+:' > "$WORKDIR/body.txt"

ninstr="$(wc -l < "$WORKDIR/body.txt")"
[ "$ninstr" -gt 0 ] || { red "EMPTY HANDLER BODY"; rm -rf "$WORKDIR"; exit 1; }
info "handler" "$ninstr instructions between <handler> and <handler_end>"

# ---- the store's inputs, per the Alpha_regs model ------------------------------------------------
# `vse64.v v8, (a2)` under `vsetvli t0, a0, VTYPEI` with vm=1 reads:
#   v8   the data vector register        (vs3)
#   a2   the base address register       (rs1)
#   vl, vtype   the length and element width
#   v0   the mask register               (not read here, vm=1, but included: the model has a mask)
STORE_GPR="a2"
STORE_VREG="v0 v8"
STORE_CSR="vl vtype vlenb"

# ---- enumerate what the handler writes -----------------------------------------------------------
# Destination register of each instruction. Loads/ALU/csrr write rd (field 1); stores and branches
# write no register; csrw/csrs/csrc write a CSR named in field 1.
awk '
  { $1=""; $2=""; sub(/^[ \t]+/,"") }              # drop address and encoding
  { mnem=$1; sub(/^[^ \t]+[ \t]*/,""); ops=$0 }
  {
    split(ops, a, ",")
    gsub(/[ \t]/, "", a[1]); gsub(/[ \t]/, "", a[2])
    if (mnem ~ /^(sd|sw|sh|sb|beq|bne|blt|bge|bltu|bgeu|bgt|ble|beqz|bnez|blez|bgez|bltz|bgtz|j|jr|ret|mret|sret|wfi|fence|sfence.vma|nop|unimp)$/) next
    if (mnem ~ /^csr[wsc]i?$/)      { print "CSR " a[1]; next }
    if (mnem ~ /^csrr[wsc]i?$/)     { print "REG " a[1]; print "CSR " a[2]; next }
    if (mnem == "csrr")             { print "REG " a[1]; print "CSRREAD " a[2]; next }
    if (a[1] != "") print "REG " a[1]
  }
' "$WORKDIR/body.txt" | sort -u > "$WORKDIR/writes.txt"

WROTE_REGS="$(grep '^REG ' "$WORKDIR/writes.txt" | sed 's/^REG //' | sort -u | tr '\n' ' ')"
WROTE_CSRS="$(grep '^CSR ' "$WORKDIR/writes.txt" | sed 's/^CSR //' | sort -u | tr '\n' ' ')"
info "writes GPR" "${WROTE_REGS:-<none>}"
info "writes CSR" "${WROTE_CSRS:-<none>}"

# ---- gate 1: no store input GPR is written -------------------------------------------------------
clash=""
for r in $STORE_GPR; do
  for w in $WROTE_REGS; do [ "$r" = "$w" ] && clash="$clash $r"; done
done
if [ -n "$clash" ]; then
  red "FAIL: handler writes the store's base-address register:$clash"; fail=1
else
  grn "handler writes no store input GPR (base address register $STORE_GPR untouched)"
fi

# ---- gate 2: no vector register is written -------------------------------------------------------
vclash="$(printf '%s\n' $WROTE_REGS | grep -E '^v[0-9]+$' | tr '\n' ' ')"
if [ -n "$vclash" ]; then
  red "FAIL: handler writes vector register(s): $vclash"; fail=1
else
  grn "handler writes no vector register (data register v8 and mask v0 untouched)"
fi

# ---- gate 2b: nothing in the body is undecodable --------------------------------------------------
# An instruction the disassembler cannot name could write anything, so gates 1-3 would be scanning
# past it. Hand-encoded .word directives are exactly how the vector instructions enter this file, and
# this toolchain has no RVV, so it prints such a word as a bare hex literal in the mnemonic column and
# assembles no vector mnemonic at all. That makes THIS the gate that catches a smuggled vector write;
# gate 2 above is the residual check for a toolchain that does decode them.
unknown="$(awk -F'\t' '
  { m = $3; sub(/^[ \t]+/, "", m); sub(/[ \t]+$/, "", m)
    if (m == "" || m ~ /^0x[0-9a-f]+$/ || m ~ /^\.(word|insn|[0-9]+byte)/ || m ~ /unknown|\(bad\)/) c++ }
  END { print c+0 }' "$WORKDIR/body.txt")"
if [ "$unknown" != 0 ]; then
  red "FAIL: $unknown undecodable word(s) in the handler body — register effects unknown"; fail=1
else
  grn "every handler instruction decodes (no hand-encoded word to scan past)"
fi

# ---- gate 3: no length/type CSR is written -------------------------------------------------------
cclash=""
for c in $STORE_CSR; do
  for w in $WROTE_CSRS; do [ "$c" = "$w" ] && cclash="$cclash $c"; done
done
# vsetvli also writes vl/vtype; catch it by mnemonic in case the handler ever gains one
if grep -qE '^\s+[0-9a-f]+:.*\bvset' "$WORKDIR/body.txt"; then
  cclash="$cclash vsetvl-instruction"
fi
if [ -n "$cclash" ]; then
  red "FAIL: handler writes length/type state:$cclash"; fail=1
else
  grn "handler writes no length/type state (vl, vtype untouched; no vset* instruction)"
fi

# ---- gate 4: the CSRs it does write are the intended ones -----------------------------------------
# The repair is allowed to write the protection entry; anything else is a change of scope that must be
# re-argued, so it is reported rather than silently accepted.
EXPECTED_CSR="pmpcfg0"
unexpected=""
for w in $WROTE_CSRS; do
  case " $EXPECTED_CSR " in *" $w "*) ;; *) unexpected="$unexpected $w";; esac
done
if [ -n "$unexpected" ]; then
  red "FAIL: handler writes CSRs outside the repair set ($EXPECTED_CSR):$unexpected"; fail=1
else
  grn "handler's only CSR write is the protection entry ($EXPECTED_CSR)"
fi

# ---- gate 5: the synchronization the protection-entry write requires ------------------------------
if grep -q 'sfence.vma' "$WORKDIR/body.txt"; then
  grn "protection-entry write is followed by sfence.vma (privileged spec 3.7.2)"
else
  red "FAIL: handler writes the protection entry with no sfence.vma"; fail=1
fi

# ---- gate 6: the trap region is MEMORY-SILENT ----------------------------------------------------
# alpha's memory-silence clause is what licenses the erasure: the argument deletes the trap region, and
# deleting an ordinary write would change the memory projection. So this is not a stylistic preference
# -- a handler with one stray store is not a witness for the contract.
memops="$(grep -cE $'	(sd|sw|sh|sb|ld|lw|lh|lb|lwu|lhu|lbu|amo[a-z.]*|lr\.|sc\.)	' "$WORKDIR/body.txt" || true)"
if [ "$memops" != 0 ]; then
  red "FAIL: handler performs $memops regular memory access(es) — the trap region is NOT memory-silent"
  grep -E $'	(sd|sw|sh|sb|ld|lw|lh|lb|lwu|lhu|lbu)	' "$WORKDIR/body.txt" | head -4
  fail=1
else
  grn "trap region is memory-silent (0 loads, 0 stores)"
fi

# ---- gate 7: NO general-purpose register is written ----------------------------------------------
# Stronger than gate 1 and it is the one that closes the suffix objection: a handler that clobbers a
# temporary without restoring it is distinguishable by a program that uses that temporary after the
# replay, even when the temporary is not an input of the faulting store. Writing none settles it.
if [ -n "$WROTE_REGS" ]; then
  red "FAIL: handler writes GPR(s):$WROTE_REGS — user-visible register state is not preserved"
  red "      (restore them before mret, or use register-free CSR forms)"
  fail=1
else
  grn "no general-purpose register is written (user-visible state preserved trivially)"
fi

rm -rf "$WORKDIR"
echo
if [ "$fail" = 0 ]; then
  echo "CONTRACT-HANDLER CERT: PASS — the certified binary is memory-silent, writes no"
  echo "  general-purpose register, and repairs only the designated protection entry. So it"
  echo "  satisfies alpha_regs (a fortiori), Alpha_regs.alpha_regs_gives_Dup applies to it, and"
  echo "  the duplicate pair's value equality is discharged rather than assumed."
else
  echo "CONTRACT-HANDLER CERT: FAIL"
fi
exit $fail
