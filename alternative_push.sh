#!/bin/bash

echo "Alternative push method for Lean 4.8.0 upgrade..."
echo ""
echo "Using incremental push strategy to avoid mmap issues"

# First, let's try to garbage collect to reduce repository size
echo "Step 1: Running git garbage collection..."
git gc --aggressive --prune=now

# Try pushing with minimal pack settings
echo "Step 2: Configuring git for minimal memory usage..."
git config core.compression 0
git config core.loosecompression 0
git config pack.window 0

# Try push with depth limit
echo "Step 3: Attempting shallow push..."
git push --thin origin phase1-integration

if [ $? -ne 0 ]; then
    echo ""
    echo "❌ Push still failing. Here are manual alternatives:"
    echo ""
    echo "Option 1: Try pushing from a different network:"
    echo "  Sometimes network issues are ISP-specific"
    echo ""
    echo "Option 2: Create a patch file to apply manually:"
    echo "  git format-patch main..phase1-integration --stdout > lean-upgrade.patch"
    echo "  Then apply on another machine with: git am lean-upgrade.patch"
    echo ""
    echo "Option 3: Push using SSH instead of HTTPS:"
    echo "  git remote set-url origin git@github.com:jonwashburn/Riemann-v1.1.git"
    echo "  git push origin phase1-integration"
    echo ""
    echo "Option 4: Create a fresh clone and cherry-pick:"
    echo "  git clone https://github.com/jonwashburn/Riemann-v1.1.git fresh-repo"
    echo "  cd fresh-repo"
    echo "  git cherry-pick a92ff34 84a131f"
    echo "  git push origin main"
else
    echo "✅ Successfully pushed! Now merging with main..."
    git checkout main
    git merge phase1-integration
    git push origin main
fi 