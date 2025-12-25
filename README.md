# eval_CategoryTheory

## Overview
Category theory from Mathlib

## What This Eval Tests
Topic-specific evaluation on Mathlib (CategoryTheory)

## Dataset Size
all available theorems

## Files
- `Library/` - Theorem files with `@[target]` annotations and `sorry` proofs
- `Library.lean` - Root import file
- `lakefile.lean` - Lake build configuration
- `lake-manifest.json` - Dependency manifest

## Source
Standalone theorems from Mathlib that only depend on Mathlib

## Usage with Agora
```bash
lake update
lake build
```
Then point Agora to this repository URL.

## Dependencies
- Lean 4 (v4.17.0)
- Mathlib4 (v4.17.0)
- VerifiedAgora
