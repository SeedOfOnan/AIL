#!/usr/bin/env bash
# AIL PIC18 Integration Test
#
# Pipeline:
#   lake exe ailc  → MPASM-compatible assembly
#   xc8-cc         → Intel HEX (via C wrapper that pre-initialises RAM)
#   gpsim          → simulation on pic18f4520 (same core ISA as Q71)
#
# Expected result: W = 0x37 after execution.
# The test store (in Main.lean) emits MOVF 0x20, W which loads RAM[0x20].
# The C wrapper pre-initialises RAM[0x20] = 0x37 before calling _ail_main.
#
# Usage: bash test/pic18_integration.sh  (from the AIL project root)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
WORK_DIR="$(mktemp -d)"
EXPECTED_W=0x37

DFP="C:/Program Files/Microchip/MPLABX/v6.30/packs/Microchip/PIC18Fxxxx_DFP/1.7.171/xc8"

echo "=== AIL PIC18 Integration Test ==="
echo "Work dir: $WORK_DIR"

# 1. Build and emit assembly -------------------------------------------------
echo ""
echo "[1/4] Emitting assembly via 'lake exe ailc'..."
cd "$PROJECT_DIR"
lake build ailc 2>/dev/null
lake exe ailc > "$WORK_DIR/ail_out.s"
echo "      Assembly:"
sed 's/^/        /' "$WORK_DIR/ail_out.s"

# 2. Write C wrapper ---------------------------------------------------------
echo ""
echo "[2/4] Writing C wrapper..."
cat > "$WORK_DIR/wrapper.c" << 'EOF'
// AIL integration test wrapper.
// Declares _ail_main as an external C-callable function (defined in ail_out.s).
// Initialises RAM[0x20] = 0x37, calls _ail_main (which does MOVF 0x20, W),
// then loops forever. After the call W contains 0x37.
// XC8 prepends '_' to C names when linking to assembly.
// 'ail_main' in C -> '_ail_main' in the linker, matching our assembly label.
extern void ail_main(void);
void main(void) {
    __asm("MOVLW 0x37");
    __asm("MOVWF 0x20");
    ail_main();
    while(1);
}
EOF

# 3. Compile with XC8 --------------------------------------------------------
echo ""
echo "[3/4] Compiling with XC8..."
xc8-cc \
  -mcpu=PIC18F4520 \
  -mdfp="$DFP" \
  -O0 \
  "$WORK_DIR/wrapper.c" \
  "$WORK_DIR/ail_out.s" \
  -o "$WORK_DIR/test.hex" 2>&1 | grep -v "^$" | sed 's/^/      /'

if [ ! -f "$WORK_DIR/test.hex" ]; then
    echo "FAIL: XC8 did not produce a hex file"
    exit 1
fi
echo "      Hex produced: $WORK_DIR/test.hex"

# 4. Simulate with gpsim -----------------------------------------------------
echo ""
echo "[4/4] Simulating with gpsim (pic18f4520)..."
GPSIM_OUT=$(cd "$WORK_DIR" && echo "processor pic18f4520
load test.hex
step 40
dump r
quit" | gpsim 2>&1)

# Extract W register value from the summary line: "fe8 W       = XX"
W_LINE=$(echo "$GPSIM_OUT" | grep -o 'W       = [0-9a-fA-F]*' | head -1)
W_VALUE=$(echo "$W_LINE" | awk '{print $3}')

echo "      gpsim W register line: '$W_LINE'"
echo "      Extracted W = 0x$W_VALUE"

EXPECTED_DEC=$(printf "%d" $EXPECTED_W)
ACTUAL_DEC=$(printf "%d" "0x$W_VALUE" 2>/dev/null || echo "?")

echo ""
echo "=== Result ==="
if [ "$ACTUAL_DEC" -eq "$EXPECTED_DEC" ] 2>/dev/null; then
    echo "PASS: W = 0x$W_VALUE ($ACTUAL_DEC decimal) — expected $EXPECTED_W"
else
    echo "FAIL: W = 0x$W_VALUE ($ACTUAL_DEC decimal) — expected $EXPECTED_W ($(printf "%d" $EXPECTED_W) decimal)"
    echo ""
    echo "Full gpsim output:"
    echo "$GPSIM_OUT"
    exit 1
fi

rm -rf "$WORK_DIR"
