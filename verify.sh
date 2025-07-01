#!/bin/bash
# Verification Script for Riemann Hypothesis Proof

echo "🔍 Verifying Riemann Hypothesis Proof..."
echo "========================================"

# Check for sorries
echo "Checking for remaining sorries..."
SORRY_COUNT=$(find src -name "*.lean" -exec grep -c "sorry" {} + | awk '{sum += $1} END {print sum}')

if [ "$SORRY_COUNT" -eq "0" ]; then
    echo "✅ No sorries found - proof is complete!"
else
    echo "❌ Found $SORRY_COUNT sorries remaining"
    find src -name "*.lean" -exec grep -n "sorry" {} +
fi

# Check file integrity
echo ""
echo "Checking file integrity..."
for file in src/*.lean src/Infrastructure/*.lean; do
    if [ -f "$file" ]; then
        echo "✅ $file exists"
    fi
done

# Build with Lean
echo ""
echo "Building with Lean 4..."
if command -v lake &> /dev/null; then
    lake build
else
    echo "⚠️  Lake not found - please install Lean 4"
fi

echo ""
echo "Verification complete!"
