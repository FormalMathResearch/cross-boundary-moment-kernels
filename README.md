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

**Stage 3: two manuscript results verified.** The project contains the manuscript-level definitions of the half-integer moments, full-support moment weights, the cross-boundary determinant, the canonical normalization, and the two crossing kernels.

The following manuscript results have complete end-to-end Lean proofs and have passed `lake build --wfail` together with `leanchecker`:

- **Lemma 3.1 — strict moment log-convexity:**
  \(I_{k+1}^2 < I_k I_{k+2}\) for every \(k \ge 0\), together with the strict increase of \(\gamma_k = I_{k+1}/I_k\).
- **Theorem 2.2(i) — positive cross-boundary representation:** for every \(u>0\), `K_k(u)` is represented by the cross-boundary integral over \(0<y\le u<z\), and \(K_k(u)>0\). The repository also proves the manuscript-exact integrand identity
  \((yz)^{k-1/2}(z-y)h(y)h(z)\) and the corresponding iterated-integral formula.

Both headline proofs retain the mathematical argument through local `have` and `calc` blocks. Strictness is derived from the manuscript's full-support hypothesis rather than from a stronger pointwise-positivity assumption. The verified proofs contain no `sorry` placeholders.

No other mathematical theorem in the manuscript should be regarded as Lean-verified until its corresponding proof has been completed and CI has passed. Verification status is recorded theorem by theorem as the development progresses.

The intended order of development is to formalize the algebraic and order-theoretic core first, then the Gamma model, and finally the more analytic curvature-pairing argument.

## Toolchain

The project is pinned to:

- **Lean 4.32.1**
- **mathlib v4.32.1**

GitHub Actions builds with warnings treated as failures and runs `leanchecker` on pushes to `main` and on pull requests targeting `main`.

## Repository organization

- `CrossBoundaryMomentKernels.lean` — root library module;
- `CrossBoundaryMomentKernels/Basic.lean` — basic moment-weight and kernel definitions;
- `CrossBoundaryMomentKernels/MomentLogConvexity.lean` — manuscript Lemma 3.1 and its supporting identities;
- `CrossBoundaryMomentKernels/CrossBoundaryRepresentation.lean` — end-to-end proof of Theorem 2.2(i) in a robust factorized form;
- `CrossBoundaryMomentKernels/CrossBoundaryManuscriptForm.lean` — exact translation to the integrand and iterated-integral notation printed in the manuscript;
- `.github/workflows/ci.yml` — Lean/mathlib CI build and kernel checking;
- `lakefile.toml` and `lean-toolchain` — reproducible project configuration.

Further modules follow the mathematical dependency structure of the manuscript rather than its page layout whenever that makes the formalization clearer.

## Goals

The project has two complementary goals:

1. produce a reproducible Lean formalization of the main mathematical results;
2. detect any hidden assumptions, indexing issues, normalization errors, or proof gaps before the manuscript is prepared for publication.

If the Lean development requires a mathematical change to the manuscript, that change will be documented explicitly rather than hidden in the formalization.

## Paper status

The accompanying manuscript has undergone an independent mathematical referee-style audit. The Lean development is the next verification stage before the publication revision.

## License and citation

License and citation metadata will be added once the formalization and manuscript release structure are finalized.
