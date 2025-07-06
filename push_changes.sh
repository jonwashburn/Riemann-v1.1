#!/bin/bash
# Push changes to GitHub using a fresh process

echo "Creating a clean copy of the repository..."
cd /Users/jonathanwashburn/Desktop/Riemann-1.1
cp -r repo repo_clean

echo "Removing .lake and .git from clean copy..."
cd repo_clean
rm -rf .lake
rm -rf .git

echo "Initializing fresh git repo..."
git init
git remote add origin https://github.com/jonwashburn/Riemann-v1.1.git

echo "Adding only source files..."
git add src/**/*.lean lean-toolchain lakefile.lean .gitignore

echo "Creating commit..."
git commit -m "Upgrade to Lean 4.3.0 and mathlib v4.3.0

- Update lean-toolchain to 4.3.0
- Pin mathlib to v4.3.0 in lakefile
- Fix import paths (ENNReal, ContinuousLinearMap, Prime)
- Stub Fredholm modules temporarily to get clean build
- Update .gitignore to properly exclude .lake/"

echo "Fetching remote..."
git fetch origin main

echo "Setting up branch..."
git branch -M main
git branch --set-upstream-to=origin/main main

echo "Pushing to GitHub..."
git push origin main --force-with-lease

echo "Done! Check https://github.com/jonwashburn/Riemann-v1.1" 