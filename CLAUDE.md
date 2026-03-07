# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

A Lean 4 formalization project for adic spaces, building on Mathlib. The project uses Lean 4 v4.29.0-rc3 with Mathlib v4.29.0-rc3.

## Build Commands

```bash
# Build the full project
lake build

# Build and fetch Mathlib cache first (recommended on fresh clone)
lake exe cache get && lake build

# Check a single file without full build
lake env lean "Adic spaces/Basic.lean"
```

## Project Structure

- `lakefile.toml` — Lake build configuration; depends on `mathlib` from `leanprover-community`
- `Adic spaces.lean` — Root import file for the library
- `Adic spaces/` — Source directory containing all Lean files
  - `Basic.lean` — Base module (currently a placeholder)
- `.github/workflows/lean_action_ci.yml` — CI: builds project and generates docs via `lean-action` + `docgen-action`

The Lake library name is `«Adic spaces»` (French-quoted due to the space). Imports use this quoting: `import «Adic spaces».Basic`.

## Lean Options (from lakefile.toml)

- `pp.unicode.fun = true` — pretty-prints `fun a ↦ b`
- `relaxedAutoImplicit = false` — no auto-implicit variables; all variables must be declared
- `weak.linter.mathlibStandardSet = true` — mathlib style linting enabled
- `maxSynthPendingDepth = 3`

## Conventions

- Follow Mathlib naming conventions and style (the mathlib linter is active).
- All new `.lean` files under `Adic spaces/` must be imported in `Adic spaces.lean`.
- Since `relaxedAutoImplicit = false`, always declare universe variables and type variables explicitly with `variable` or `section` blocks.
