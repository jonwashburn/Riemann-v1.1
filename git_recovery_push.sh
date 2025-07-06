#!/bin/bash

echo "Git Recovery and Push Script for Lean 4.8.0 Upgrade"
echo "==================================================="
echo ""
echo "This script will help push your Lean 4.8.0 changes after fixing git issues."
echo ""

# First, try to repair git if possible
echo "Step 1: Attempting to repair git repository..."
git fsck --full

if [ $? -ne 0 ]; then
    echo ""
    echo "⚠️  Git repository has issues. Trying to recover..."
    
    # Try to rebuild refs
    echo "Rebuilding refs..."
    find .git/refs -type f -name "* *" -delete 2>/dev/null
    git for-each-ref --format="%(refname)" | while read ref; do
        git show-ref --verify --quiet "$ref" || git update-ref -d "$ref"
    done
fi

echo ""
echo "Step 2: Creating clean branch for push..."

# Use the commit hashes directly since refs might be broken
MAIN_COMMIT="f511903"  # Last known good main commit
UPGRADE_COMMIT="a92ff34"  # Lean 4.8.0 upgrade
GITIGNORE_COMMIT="84a131f"  # .gitignore addition

# Create a clean branch from the last known good main
git checkout -f $MAIN_COMMIT
git checkout -b lean48-clean

echo ""
echo "Step 3: Cherry-picking upgrade commits..."

# Cherry-pick the clean commits
git cherry-pick $UPGRADE_COMMIT
if [ $? -ne 0 ]; then
    echo "❌ Failed to cherry-pick upgrade commit. Manual intervention needed."
    exit 1
fi

git cherry-pick $GITIGNORE_COMMIT
if [ $? -ne 0 ]; then
    echo "❌ Failed to cherry-pick .gitignore commit. Manual intervention needed."
    exit 1
fi

echo ""
echo "Step 4: Pushing clean branch..."
git push -u origin lean48-clean

if [ $? -eq 0 ]; then
    echo ""
    echo "✅ Successfully pushed lean48-clean branch!"
    echo ""
    echo "Next steps:"
    echo "1. Go to https://github.com/jonwashburn/Riemann-v1.1"
    echo "2. Create a Pull Request from 'lean48-clean' to 'main'"
    echo "3. Merge the PR"
    echo ""
    echo "Or merge locally:"
    echo "  git checkout main"
    echo "  git reset --hard origin/main"
    echo "  git merge lean48-clean"
    echo "  git push origin main"
else
    echo ""
    echo "❌ Push failed. Your changes are safe in the lean48-clean branch."
    echo ""
    echo "Alternative: Create a fresh clone and apply patches"
    echo "1. In a new directory:"
    echo "   git clone https://github.com/jonwashburn/Riemann-v1.1.git fresh-repo"
    echo "   cd fresh-repo"
    echo ""
    echo "2. Apply the changes manually:"
    echo "   - Copy the modified files from this repo"
    echo "   - Specifically: lean-toolchain, lakefile.lean, and src/RiemannHypothesis/Infrastructure/"
    echo "   - Commit and push"
fi 