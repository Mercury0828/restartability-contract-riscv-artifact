#!/bin/bash
# DR-2 build + run harness. Runs all pre-registered variants and archives logs.
set -e
cd "$(dirname "$0")"
SIM=${SAIL_RISCV_SIM:-sail_riscv_sim}   # released sail_riscv_sim 0.13
AS=riscv64-unknown-elf-as
LD=riscv64-unknown-elf-ld

# VLEN=128 override (frozen platform: VLEN=128, ELEN=64)
cat > vlen128.json <<'EOF'
{ "extensions": { "V": { "vlen_exp": 7 } } }
EOF

build () { # name vtypei vl k fault
  $AS -march=rv64g -o $1.o test.S \
      --defsym VTYPEI=$2 --defsym VL=$3 --defsym K=$4 --defsym FAULT=$5
  $LD -T link.ld -o $1.elf $1.o
}

run () { # name
  set +e
  $SIM --config-override vlen128.json \
       --trace-instr --trace-csr --trace-exception --trace-mem \
       --trace-output $1.trace.log --inst-limit 200000 $1.elf > $1.stdout.log 2>&1
  echo "$1 exit=$?" >> results.txt
  grep -E "SUCCESS|FAILURE|tohost" $1.stdout.log | tail -3 >> results.txt
  set -e
}

rm -f results.txt

# Variants (frozen configs; K per pre-registration):
build c1_vl2_k0   0xD8 2 0 1 ; run c1_vl2_k0     # (LMUL=1,VL=2), k=0
build c2_vl2_k1   0xD8 2 1 1 ; run c2_vl2_k1     # (LMUL=1,VL=2), k=1=VL-1
build c3_vl4_k2   0xD9 4 2 1 ; run c3_vl4_k2     # (LMUL=2,VL=4), k=2  <-- nastiest in-scope shape
build c4_vl4_k3   0xD9 4 3 1 ; run c4_vl4_k3     # (LMUL=2,VL=4), k=3=VL-1
build c5_vl4_ref  0xD9 4 2 0 ; run c5_vl4_ref    # no-fault reference (pmp_ok pre-set)

echo "==== results ===="
cat results.txt
