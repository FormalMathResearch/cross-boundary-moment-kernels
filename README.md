# Cross-Boundary Moment Kernels

Lean formalization of cross-boundary moment kernels, one-crossing geometry, total positivity, size bias, and curvature.

## Overview

This repository is the formal-verification companion to the mathematical manuscript

**Cross-Boundary Moment Kernels: One-Crossing Geometry, Total Positivity, Size Bias, and Curvature.**

The project aims to formalize the main definitions, identities, and proofs in **Lean 4** with **mathlib**, and to use the formalization as an independent check of the mathematical argument before the publication revision of the manuscript.

## Mathematical scope

The manuscript studies a hierarchy built from global and truncated half-integer moments

\[
I_j = \int_0^\infty y^{j-1/2} h(y)\,dy,
\qquad
J_j(u) = \int_0^u y^{j-1/2} h(y)\,dy,
\]

and the cross-boundary determinants

\[
K_k(u) = J_k(u) I_{k+1} - J_{k+1}(u) I_k.
\]

The planned formalization covers, in particular:

- positivity and the cross-boundary integral representation of `K_k`;
- strict log-convexity of the moment sequence;
- the quadratic derivative structure of the crossing kernel;
- the universal one-crossing theorem;
- strict total positivity of order two for the normalized hierarchy;
- the truncated Gram/variance decomposition;
- the multiplicative size-bias hierarchy;
- the inter-order equivalence principle at the canonical crossing;
- the exactly solvable Gamma model and its sharp crossing threshold;
- the curvature-pairing identity, including the required integration and Fubini arguments.

## Formalization status

**Stage 1: project setup and core definitions.** The Lean project now contains the manuscript-level definitions of the half-integer moments, the full-support moment-weight hypotheses, the cross-boundary determinant, the canonical normalization, and the two crossing kernels.

No mathematical theorem in the manuscript should be regarded as Lean-verified until its corresponding Lean proof has been completed and CI has passed. Verification status will be recorded theorem by theorem as the development progresses.

The intended order of development is to formalize the algebraic and order-theoretic core first, then the Gamma model, and finally the more analytic curvature-pairing argument.

## Toolchain

The project is pinned to:

- **Lean 4.32.1**
- **mathlib v4.32.1**

GitHub Actions builds the project on pushes to `main` and on pull requests targeting `main`.

## Repository organization

- `CrossBoundaryMomentKernels.lean` — root library module;
- `CrossBoundaryMomentKernels/Basic.lean` — basic moment-weight and kernel definitions;
- `.github/workflows/ci.yml` — Lean/mathlib CI build;
- `lakefile.toml` and `lean-toolchain` — reproducible project configuration.

Further modules will follow the mathematical dependency structure of the manuscript rather than its page layout whenever that makes the formalization clearer.

## Goals

The project has two complementary goals:

1. produce a reproducible Lean formalization of the main mathematical results;
2. detect any hidden assumptions, indexing issues, normalization errors, or proof gaps before the manuscript is prepared for publication.

If the Lean development requires a mathematical change to the manuscript, that change will be documented explicitly rather than hidden in the formalization.

## Paper status

The accompanying manuscript has undergone an independent mathematical referee-style audit. The Lean development is the next verification stage before the publication revision.

## License and citation

License and citation metadata will be added once the formalization and manuscript release structure are finalized.
