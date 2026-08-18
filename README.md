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

**Stage 7: six manuscript result blocks verified.** The project contains the manuscript-level definitions of the half-integer moments, full-support moment weights, the cross-boundary determinant, the canonical normalization, the two crossing kernels, and the cross-boundary probability laws.

The following manuscript results have complete end-to-end Lean proofs and have passed `lake build --wfail` together with `leanchecker`:

- **Lemma 3.1 — strict moment log-convexity:**
  \(I_{k+1}^2 < I_k I_{k+2}\) for every \(k \ge 0\), together with the strict increase of \(\gamma_k = I_{k+1}/I_k\).
- **Theorem 2.2(i) — positive cross-boundary representation:** for every \(u>0\), `K_k(u)` is represented by the cross-boundary integral over \(0<y\le u<z\), and \(K_k(u)>0\). The repository also proves the manuscript-exact integrand identity
  \((yz)^{k-1/2}(z-y)h(y)h(z)\) and the corresponding iterated-integral formula.
- **Theorem 2.2(ii)–(iii) — quadratic derivative law and universal one-crossing geometry:** for every manuscript index \(k\ge1\), the derivative quadratic has strictly positive discriminant and two distinct positive roots \(0<\xi_{k,-}<\xi_{k,+}\). The crossing kernel `R_k` is locally absolutely continuous on the positive half-line and satisfies, almost everywhere,
  \[
  R_k'(x)=2I_{k+1}x^{k-1/2}h(x)Q_k(x).
  \]
  There is a unique positive zero \(u_k^*\in(\xi_{k,-},\xi_{k,+})\); both `R_k` and the normalized kernel `Rhat_k` are strictly positive before \(u_k^*\) and strictly negative after it.
- **Theorem 2.2(iv) — strict total positivity of order two:** for every \(k\ge1\), the adjacent normalized quotient \(u\mapsto Z_{k+1}(u)/Z_k(u)\) is strictly increasing on \((0,\infty)\). Consequently, for every pair of manuscript indices \(1\le m<n\) and every \(0<u<v\),
  \[
  Z_m(u)Z_n(v)-Z_n(u)Z_m(v)>0.
  \]
  The Lean proof kernel-checks the manuscript derivative ratio \(Z'_{k+1}=C_k\phi_k Z'_k\), the strict monotonicity of \(\phi_k\) on both sides of its pole, the three ratio regions, and the iteration from adjacent indices to arbitrary \(m<n\).
- **Theorem 2.2(v) — truncated Gram/variance decomposition:** for every \(k\ge1\) and \(u>0\), with
  \[
  \mu_k(u)=\frac{J_{k+2}(u)}{J_{k+1}(u)},\qquad
  v_k(u)=\frac{J_{k+3}(u)}{J_{k+1}(u)}-\mu_k(u)^2,
  \]
  the repository proves the exact identity
  \[
  \frac{R_{k+1}(u)}{2I_{k+2}J_{k+1}(u)}
  =v_k(u)+Q_{k+1}(\mu_k(u)),
  \]
  the strict inequality \(v_k(u)>0\), its Hankel-ratio form, and the manuscript-exact symmetrized Gram formula
  \[
  J_{k+1}J_{k+3}-J_{k+2}^2
  =\frac12\int_0^u\int_0^u
  (yz)^{k+1/2}(y-z)^2h(y)h(z)\,dy\,dz.
  \]
- **Theorem 2.2(vi) — multiplicative size-bias hierarchy:** for every \(k\ge0\) and \(u>0\), the manuscript density
  \[
  d\nu_{k,u}(y,z)=\frac{(yz)^{k-1/2}(z-y)h(y)h(z)}{K_k(u)}\,dy\,dz,
  \qquad 0<y\le u<z,
  \]
  is formalized as an actual probability measure. For \(X=YZ\), Lean proves for every integer \(m\ge0\)
  \[
  \mathbb E_{k,u}[X^m]=\frac{K_{k+m}(u)}{K_k(u)},
  \]
  and the exact Radon--Nikodym size-bias identity
  \[
  d\nu_{k+1,u}=\frac{X}{\mathbb E_{k,u}X}\,d\nu_{k,u}.
  \]
  Writing \(M_k(u)=\mathbb E_{k,u}X=K_{k+1}(u)/K_k(u)\), the formalization establishes \(X\in L^2(\nu_{k,u})\), identifies the genuine `ProbabilityTheory.variance`, and proves
  \[
  M_{k+1}(u)-M_k(u)
  =\frac{\operatorname{Var}_{k,u}(X)}{M_k(u)}>0.
  \]

The one-crossing development also kernel-checks the integrated derivative law and the exact upper-tail identity for `R_k`. These replace the informal endpoint-limit passages inside the Lean proof while preserving the manuscript statement and hypotheses. The three monotonicity phases are made strict directly from the manuscript full-support condition, not from a stronger assumption that `h` is pointwise positive everywhere.

Likewise, the strict-TP2 development uses exact lower-primitive, difference, and upper-tail identities for `Z_k`. The lower and upper ratio zones are proved by strict gap integrals supported on positive-measure subintervals supplied by the manuscript full-support hypothesis; no stronger pointwise positivity or smoothness assumption on `h` is introduced.

For the truncated Gram block, strictness is again obtained from the manuscript full-support hypothesis. The formal proof places two disjoint positive-measure support slices inside `(0,u)` and uses their product rectangle to force the symmetrized square integrand to have positive integral. No pointwise positivity or additional regularity assumption on `h` is introduced.

For the multiplicative size-bias block, strict variance positivity is likewise proved without pointwise positivity of `h`. A two-copy Gram identity gives
\[
K_k(u)K_{k+2}(u)-K_{k+1}(u)^2
=\frac12\iint f_k(p)f_k(q)\bigl(X(p)-X(q)\bigr)^2\,d\mu(p)\,d\mu(q)>0,
\]
and full support supplies two positive-measure cross-boundary rectangles on which the product variable `X = YZ` has separated ranges. This proves non-degeneracy and the strict variance drift using exactly the manuscript support hypothesis.

All headline proofs retain the mathematical argument through local `have` and `calc` blocks. The verified proofs contain no `sorry` placeholders.

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
- `CrossBoundaryMomentKernels/OneCrossing.lean` — the crossing quadratic, discriminant, roots, and their sign geometry;
- `CrossBoundaryMomentKernels/OneCrossingAnalysis.lean` — integrable derivative-density normal form;
- `CrossBoundaryMomentKernels/OneCrossingPrimitive.lean` — integrated derivative, difference, and upper-tail identities;
- `CrossBoundaryMomentKernels/OneCrossingSigns.lean` — strict derivative-integral signs and the three strict monotonicity phases;
- `CrossBoundaryMomentKernels/OneCrossingRegularity.lean` — local absolute continuity and the a.e. derivative law;
- `CrossBoundaryMomentKernels/OneCrossingGeometry.lean` — unique canonical crossing and global sign pattern;
- `CrossBoundaryMomentKernels/OneCrossingManuscriptForm.lean` — manuscript-exact a.e. derivative statement;
- `CrossBoundaryMomentKernels/TotalPositivity.lean` — integrable derivative normal form and exact primitive/difference/tail identities for `Z_k`;
- `CrossBoundaryMomentKernels/TotalPositivityRatio.lean` — the manuscript functions `C_k`, `φ_k`, their algebra, derivative-ratio law, and strict derivative-mass lemmas;
- `CrossBoundaryMomentKernels/TotalPositivityAdjacent.lean` — strict monotonicity of every adjacent quotient `Z_{k+1}/Z_k` across all three gamma regions;
- `CrossBoundaryMomentKernels/TotalPositivityHierarchy.lean` — iteration to arbitrary index pairs and the strict TP2 determinant theorem;
- `CrossBoundaryMomentKernels/GramDecomposition.lean` — positivity of truncated moments, strict truncated Hankel log-convexity, the factorized Gram square, and the exact Gram-plus-transport identity;
- `CrossBoundaryMomentKernels/GramManuscriptForm.lean` — manuscript-exact `(yz)^{k+1/2}(y-z)^2h(y)h(z)` integrand and iterated double-integral form;
- `CrossBoundaryMomentKernels/SizeBias.lean` — the cross-boundary base measure and probability density, normalization, general `X^m` moment identity, and mean formula;
- `CrossBoundaryMomentKernels/SizeBiasShift.lean` — exact multiplicative Radon--Nikodym size-bias step from index `k` to `k+1`;
- `CrossBoundaryMomentKernels/CrossBoundaryKGram.lean` — two-copy Gram identity and strict index log-convexity of the cross-boundary `K` hierarchy;
- `CrossBoundaryMomentKernels/SizeBiasVariance.lean` — `L²` integrability, genuine probabilistic variance, strict variance positivity, and the mean drift formula;
- `CrossBoundaryMomentKernels/SizeBiasManuscriptForm.lean` — exact identification of the formal probability law with the density printed in Theorem 2.2(vi);
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
