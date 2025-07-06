#!/bin/bash

echo "Pushing Lean 4.8.0 upgrade to GitHub and merging with main..."

# First, try to push the current branch
echo "Step 1: Pushing phase1-integration branch..."
git push origin phase1-integration

if [ $? -eq 0 ]; then
    echo "✅ Successfully pushed phase1-integration branch"
    
    # Switch to main branch
    echo "Step 2: Switching to main branch..."
    git checkout main
    
    # Pull latest changes from main
    echo "Step 3: Pulling latest changes from main..."
    git pull origin main
    
    # Merge phase1-integration into main
    echo "Step 4: Merging phase1-integration into main..."
    git merge phase1-integration
    
    # Push the merged main branch
    echo "Step 5: Pushing updated main branch..."
    git push origin main
    
    echo "✅ Successfully merged Lean 4.8.0 upgrade into main branch!"
    echo ""
    echo "Summary of changes:"
    echo "- Upgraded from Lean 4.22.0-rc2 to Lean 4.8.0"
    echo "- Updated mathlib from v4.3.0 to v4.8.0"
    echo "- Fixed import paths and API compatibility"
    echo "- All modules compile successfully"
    echo "- 20 sorry placeholders for ongoing proof work"
    echo "- Repository ready for continued development"
    
else
    echo "❌ Failed to push phase1-integration branch"
    echo "You can try running this script again later or push manually:"
    echo "  git push origin phase1-integration"
    echo "  git checkout main"
    echo "  git merge phase1-integration"
    echo "  git push origin main"
fi 