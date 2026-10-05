# Gaussian tilt covariance

[![Lean checks](https://github.com/liuchliuch/gaussian-tilt-covariance-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/liuchliuch/gaussian-tilt-covariance-lean/actions/workflows/lean.yml)

Lean 4 formalization of [*Optimal Covariance Inflation under Gaussian Tilts*](https://arxiv.org/abs/2609.08930v1).

The covariance inflation upper and lower bounds and sharp dimension scale, with independent specifications for all 27 active numbered results.

Corollary 4.10 uses an explicit constant-renaming correction. The literal same-constant chain is separately refuted; the corrected proposition is proved. The main upper and lower theorems and the sharp exponent are unaffected. See the erratum for the exact quantifiers and constants.

## Build and verify

Lean **4.24.0**, Mathlib and every transitive Git dependency are pinned.
Install [elan](https://github.com/leanprover/elan), then run:

```sh
elan toolchain install leanprover/lean4:v4.24.0
lake exe cache get
lake build
python3 scripts/verify.py
```

The verification command rebuilds the complete project library, audits originating declarations and their transitive axioms, and runs the retained regressions. Pinned Mathlib caches may be reused. Do not update `lake-manifest.json` when reproducing this version.

## Statements and proofs

29 targets check the 26 literal numbered results, corrected Corollary 4.10, its literal refutation, and the complete corrected catalog. The independent specification imports only Reference definitions and Mathlib; all model definitions remain fixed.

The [official Comparator](https://github.com/leanprover/comparator) runs in a separate Linux CI job with Landrun and the upstream systemd restriction. It compares target types and fixed declaration dependencies, enforces the axiom policy, and replays the exported solution through Lean’s default kernel. Rejection controls test the checking path. See [verification instructions](docs/VERIFICATION.md) for commands, pins and scope.

## Read the formalization

- [Main analytic results](GaussianTilt/OriginalAnalyticClosure.lean)
- [Numbered proofs](GaussianTilt/NumberedProofs.lean)
- [Independent specifications](GaussianTilt/Reference/NumberedStatements.lean)
- [Paper correspondence](docs/NUMBERED_STATEMENTS.md)
- [Corollary 4.10 correction](docs/COROLLARY410_ERRATUM.md)

The source distribution contains the mathematical library, statement specifications, retained tests, pinned configuration and verification tools. Generated logs, dependencies and build caches are excluded; CI publishes its reports as workflow artifacts.

No project license has been selected. The cited paper and upstream dependencies retain their own licensing terms.
