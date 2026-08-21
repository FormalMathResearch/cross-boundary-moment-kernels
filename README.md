# Cross-Boundary Moment Kernels

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22046413.svg)](https://doi.org/10.5281/zenodo.22046413)

Lean formalization of cross-boundary moment kernels, one-crossing geometry, total positivity, size bias, Gamma models, and curvature.

## Overview

This repository is the formal-verification companion to the mathematical manuscript

**Cross-Boundary Moment Kernels: One-Crossing Geometry, Total Positivity, Size Bias, and Curvature.**

The aim is to formalize the manuscript's main definitions, identities, and proofs in **Lean 4** with **mathlib**, and to use the formalization as an independent mathematical check before publication.

For a theorem-by-theorem mapping from the manuscript to Lean declarations, including hypothesis notes and verification scope, see **[`MANUSCRIPT_VERIFICATION.md`](MANUSCRIPT_VERIFICATION.md)**.

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

The Lean development includes the manuscript's full-support moment-weight framework, the cross-boundary representation and one-crossing geometry, strict TP2, the truncated Gram decomposition, the multiplicative size-bias hierarchy, the inter-order equivalence and trichotomy, the exactly solvable Gamma model, and the curvature-pairing theorem with its absolute-convergence and Fubini justification.

## Formalization status

The current development contains publication-facing Lean statements for the following manuscript results:

- **Theorem 2.2(i)–(vi)** — cross-boundary representation, universal one-crossing geometry, strict TP2, truncated Gram decomposition, and multiplicative size bias;
- **Theorem 2.3** — six-way inter-order equivalence;
- **Corollary 2.4** — necessary normalization curvature;
- **Theorem 2.5** — curvature pairing;
- **Corollary 2.6** — curvature balance for log-concave weights;
- **Theorem 2.7** — exact Gamma model and sharp adjacent-crossing threshold;
- **Corollaries 2.8 and 2.9** — explicit counterexamples showing that neither log-concavity nor positive moment curvature alone forces increasing crossing order;
- **Proposition 2.10** — exact Gamma product law;
- **Lemma 3.1** — strict moment log-convexity;
- **Remark 4.1** — equality and reversed inter-order trichotomies.

The manuscript's **Definition 2.1** is mirrored by `FullSupportMomentWeight` in `Basic.lean`.

A result should be regarded as **Lean-verified** only when its statement has been audited against the manuscript and the exact relevant PR state has passed both `lake build --wfail` and `leanchecker`. The authoritative theorem-by-theorem scope is recorded in [`MANUSCRIPT_VERIFICATION.md`](MANUSCRIPT_VERIFICATION.md).

### Manuscript-hypothesis discipline

The formalization is deliberately conservative about assumptions:

- strictness is derived from the manuscript full-support condition rather than replacing it by pointwise positivity of `h`;
- the one-crossing derivative law is stated almost everywhere, matching the regularity available for a merely measurable weight;
- Gamma results are split when necessary so that `k ≥ 1` is not imposed on all-index identities;
- in Theorem 2.5, `h' = -V'h` is derived from `h = exp(-V)` and `V ∈ C²(0,∞)` rather than assumed separately;
- the signed curvature Fubini step is performed only after an explicit finite absolute Tonelli estimate using the manuscript envelope.

No mathematical hypothesis is intentionally strengthened merely to make Lean proofs easier. If a future formalization step requires a genuine change to the manuscript, that change should be documented explicitly.

## Curvature theorem API

For publication and citation there is a single manuscript-facing curvature theorem/corollary endpoint:

- `curvature_theorem_2_5`
- `curvature_corollary_2_6`

both in `CrossBoundaryMomentKernels/CurvatureManuscriptForm.lean`.

Theorem 2.5 exposes the manuscript hypotheses individually. Its visible proof follows the actual causal chain used by Lean: exact two-copy representation, symmetry plus the `C²` FTC step, and signed Fubini with identification of the inner bracket as `R_k`. The lower-level integration-by-parts, tilted-law, covariance, Tonelli, and integrability results remain modular kernel-checked dependencies.

## CI and verification provenance

The project is pinned to:

- **Lean 4.32.1**
- **mathlib v4.32.1**

GitHub Actions treats warnings as failures and runs `leanchecker`.

For pull requests, CI checks both relevant commit notions:

- `build` checks GitHub's normal synthetic merge ref against `main`;
- `build-pr-head` explicitly checks out `github.event.pull_request.head.sha`.

Both jobs run `lake build --wfail` and `leanchecker`. This allows a verification claim to be attached to an immutable PR-head SHA rather than only to GitHub's generated merge commit.

The root module `CrossBoundaryMomentKernels.lean` imports the complete formal development, including the Gamma and curvature manuscript-facing modules.

## Repository organization

### Foundations and Theorem 2.2

- `CrossBoundaryMomentKernels/Basic.lean` — Definition 2.1, moments, determinants, normalization, and crossing kernels;
- `CrossBoundaryMomentKernels/MomentLogConvexity.lean` — manuscript Lemma 3.1;
- `CrossBoundaryMomentKernels/CrossBoundaryRepresentation.lean` and `CrossBoundaryManuscriptForm.lean` — Theorem 2.2(i);
- `CrossBoundaryMomentKernels/OneCrossing*.lean` — Theorem 2.2(ii)–(iii), including regularity and manuscript derivative form;
- `CrossBoundaryMomentKernels/TotalPositivity*.lean` — Theorem 2.2(iv);
- `CrossBoundaryMomentKernels/GramDecomposition.lean` and `GramManuscriptForm.lean` — Theorem 2.2(v);
- `CrossBoundaryMomentKernels/SizeBias*.lean` and `CrossBoundaryKGram.lean` — Theorem 2.2(vi).

### Inter-order theory

- `CrossBoundaryMomentKernels/InterOrder.lean` — `Lambda`, `Omega`, crossing matching, and local/global curvature identities;
- `CrossBoundaryMomentKernels/InterOrderEquivalence.lean` — Theorem 2.3;
- `CrossBoundaryMomentKernels/InterOrderTrichotomy.lean` — Remark 4.1 and Corollary 2.4.

### Gamma model

- `CrossBoundaryMomentKernels/GammaModel.lean`, `GammaRecurrence.lean`, `GammaExplicit.lean` — analytic and algebraic Gamma identities;
- `CrossBoundaryMomentKernels/GammaCorollaries.lean` — scale/curvature and crossing consequences;
- `CrossBoundaryMomentKernels/GammaProductLaw.lean`, `GammaProductMGF.lean`, `GammaProductDistribution.lean` — exact product-law formalization;
- `CrossBoundaryMomentKernels/GammaManuscriptForm.lean` — publication-facing Theorem 2.7, Corollaries 2.8–2.9, and Proposition 2.10.

### Curvature pairing

- `CrossBoundaryMomentKernels/CurvaturePairing.lean` and `CurvaturePairingMoments.lean` — manuscript analytic hypotheses and Lemma 5.1 specializations;
- `CrossBoundaryMomentKernels/CurvatureTiltedMeasure.lean` and `CurvatureCovariance.lean` — tilted law and covariance reduction;
- `CrossBoundaryMomentKernels/CurvatureTwoCopy*.lean` — two-copy representation of moment curvature;
- `CrossBoundaryMomentKernels/CurvatureFTC.lean` — local `C²` FTC step;
- `CrossBoundaryMomentKernels/CurvatureTonelli.lean`, `CurvatureEnvelopeIntegrability.lean`, `CurvatureAbsoluteTonelli.lean`, `CurvatureAbsoluteIntegrability.lean` — absolute-convergence gate;
- `CrossBoundaryMomentKernels/CurvatureBracket.lean`, `CurvatureSignedFubini*.lean`, `CurvatureSignedIntegrability.lean` — signed Fubini and identification with `R_k`;
- `CrossBoundaryMomentKernels/CurvatureSymmetryFTC.lean` — symmetry and ordered-region bridge;
- `CrossBoundaryMomentKernels/CurvatureBalance.lean` — analytic crossing split used by Corollary 2.6;
- `CrossBoundaryMomentKernels/CurvatureManuscriptForm.lean` — publication-facing Theorem 2.5 and Corollary 2.6.

### Reproducibility and audit

- `CrossBoundaryMomentKernels.lean` — root library module importing the formal development;
- `MANUSCRIPT_VERIFICATION.md` — manuscript-to-Lean verification matrix;
- `.github/workflows/ci.yml` — merge-ref and exact-PR-head CI;
- `lakefile.toml` and `lean-toolchain` — reproducible project configuration.

Further modules follow the mathematical dependency structure of the manuscript rather than its page layout whenever that makes the formalization clearer.

## Goals and scope of the verification claim

The project has two complementary goals:

1. produce a reproducible Lean formalization of the manuscript's mathematical claims;
2. detect hidden assumptions, indexing issues, normalization errors, or proof gaps before publication.

Lean verification does not by itself establish novelty, literature priority, bibliographic completeness, or editorial quality. Those remain separate scientific and publication checks.

## Release and citation

The first archival software release is **v1.0.0**, preserved on Zenodo.

- **Software DOI:** `10.5281/zenodo.22046413`
- **Associated manuscript DOI:** `10.5281/zenodo.22033635`
- **GitHub release tag:** `v1.0.0`
- **Release commit:** `24ad78e423893f700ca45f40817c36aae851e101`
- **Toolchain:** Lean 4.32.1, mathlib v4.32.1
- **License:** MIT

The software DOI identifies the archived Lean artifact and is intentionally distinct from the manuscript DOI. Machine-readable citation metadata are provided in [`CITATION.cff`](CITATION.cff).
