# Manuscript Verification Matrix

This file maps the mathematical manuscript

**Cross-Boundary Moment Kernels: One-Crossing Geometry, Total Positivity, Size Bias, and Curvature**

to its publication-facing Lean declarations. It is intended to make the scope of the formal verification auditable without requiring a reader to reconstruct the dependency graph from the source tree.

## Verification standard

A manuscript result is marked **Lean-verified** here only when all of the following hold:

1. the Lean statement has been checked against the manuscript statement and index range;
2. the formal proof does not silently replace a manuscript hypothesis by a stronger convenience hypothesis;
3. the result is imported by the root module `CrossBoundaryMomentKernels.lean`;
4. the pull-request CI has passed both `lake build --wfail` and `leanchecker` for the relevant state; and
5. on pull requests, both the GitHub merge-ref job and the separate exact-PR-head job pass.

The formalization verifies mathematical statements and proof dependencies. It does **not** by itself verify novelty, literature priority, exposition, bibliography, or claims about the historical provenance of the results.

## Foundational manuscript definitions

| Manuscript item | Lean object | File | Matching note |
|---|---|---|---|
| Definition 2.1 — full-support moment weight | `FullSupportMomentWeight` | `CrossBoundaryMomentKernels/Basic.lean` | Mirrors measurability, nonnegativity on `(0,∞)`, positive mass on every nonempty compact subinterval, integrability of every half-integer moment density, and positivity of every global moment. |
| Global/truncated moments | `halfExponent`, `momentIntegrand`, `I`, `J` | `CrossBoundaryMomentKernels/Basic.lean` | Uses restricted Lebesgue measure on `(0,∞)` and `(0,u]`; half-integer powers are represented with `Real.rpow`. |
| Cross-boundary hierarchy | `K`, `N`, `Z`, `tau`, `R`, `Rhat` | `CrossBoundaryMomentKernels/Basic.lean` | Direct formal counterparts of the manuscript definitions. |

## Main result mapping

| Manuscript result | Publication-facing / headline Lean declaration(s) | Principal file(s) | Hypothesis audit | Status |
|---|---|---|---|---|
| Theorem 2.2(i) — positive cross-boundary representation | `crossBoundary_representation_and_pos`; `K_eq_manuscriptCrossBoundaryIntegral` | `CrossBoundaryRepresentation.lean`; `CrossBoundaryManuscriptForm.lean` | Uses only `FullSupportMomentWeight` and `u>0`; the manuscript integrand `(yz)^(k-1/2)(z-y)h(y)h(z)` is identified explicitly. | **Lean-verified** |
| Theorem 2.2(ii)–(iii) — derivative quadratic and universal one-crossing | `universal_one_crossing`; `R_ae_hasDerivAt_manuscript` | `OneCrossingGeometry.lean`; `OneCrossingManuscriptForm.lean` | Manuscript range `k≥1`; no pointwise positivity or smoothness of `h` is added. The derivative statement is correctly formulated almost everywhere under the measurable-weight hypotheses. | **Lean-verified** |
| Theorem 2.2(iv) — strict TP2 | `universal_strict_tp2` | `TotalPositivityHierarchy.lean` | Manuscript ranges `k≥1` and `1≤m<n`; strictness is derived from full support rather than pointwise positivity. | **Lean-verified** |
| Theorem 2.2(v) — truncated Gram/variance decomposition | `universal_truncated_gram_decomposition`; `truncated_hankel_gram_identity_manuscript` | `GramManuscriptForm.lean` | Manuscript range `k≥1`, `u>0`; exact Gram integrand and iterated double integral are exposed. | **Lean-verified** |
| Theorem 2.2(vi) — multiplicative size bias | `theorem_2_2_vi_multiplicative_size_bias` | `SizeBiasManuscriptForm.lean` | Manuscript range `k≥0`, `u>0`; the printed density is identified with an actual probability measure, and the moment, size-bias, variance, and strict drift statements are proved. | **Lean-verified** |
| Theorem 2.3 — six-way inter-order equivalence | `six_way_inter_order_equivalence`; `crossing_order_iff_Lambda_lt_Omega` | `InterOrderEquivalence.lean` | Manuscript range `k≥1`; all six conditions are connected by proved equivalences rather than by exclusion. | **Lean-verified** |
| Corollary 2.4 — necessary normalization curvature | `crossing_order_implies_one_lt_Omega` | `InterOrderTrichotomy.lean` | From `u_k^*<u_{k+1}^*` and Theorem 2.3, together with the proved universal inequality `Lambda_k(u)>1`; no extra hypothesis. | **Lean-verified** |
| Theorem 2.5 — curvature pairing | `curvature_theorem_2_5` | `CurvatureManuscriptForm.lean` | Public theorem exposes the manuscript hypotheses individually: `k≥1`; `h=exp(-V)` on `(0,∞)`; `V∈C²(0,∞)`; boundary and weighted-`V'` assumptions at `a_k,b_k,c_k`; and the printed absolute envelope integrability condition. | **Lean-verified** |
| Corollary 2.6 — curvature balance for log-concave weights | `curvature_corollary_2_6` | `CurvatureManuscriptForm.lean` | Exactly the Theorem 2.5 assumptions plus `V''≥0` on `(0,∞)`. The corollary invokes the public Theorem 2.5 endpoint explicitly. | **Lean-verified** |
| Theorem 2.7 — Gamma model | `gamma_theorem_2_7_all_index`; `gamma_theorem_2_7_crossing` | `GammaManuscriptForm.lean` | Split deliberately preserves the manuscript index ranges: the moment/determinant identities are all-index, while the crossing assertions use `k≥1`. | **Lean-verified** |
| Corollary 2.8 — strict log-concavity does not force crossing order | `gamma_corollary_2_8` | `GammaManuscriptForm.lean` | Uses the manuscript parameter range `a>0`; identifies the logarithmic profile with the actual log-weight on `(0,∞)` and includes the explicit reversed-crossing witness. | **Lean-verified** |
| Corollary 2.9 — positive moment curvature does not force crossing order | `gamma_corollary_2_9` | `GammaManuscriptForm.lean` | Uses `a>0`, `k≥1`; proves the exact scale and curvature formulas, positivity, and the reversed-crossing witness. | **Lean-verified** |
| Proposition 2.10 — exact Gamma product law | `gamma_proposition_2_10`; `gamma_proposition_2_10_variance_at_crossing` | `GammaManuscriptForm.lean` | The distributional statement is all-index (`k≥0`, `u>0`). The variance-at-crossing statement is separated and uses `k≥1`, matching the manuscript domain of the canonical crossing. | **Lean-verified** |
| Lemma 3.1 — strict moment log-convexity | `strict_moment_logConvexity_and_gamma_lt` | `MomentLogConvexity.lean` | Uses only `FullSupportMomentWeight`; strictness is forced from full support on separated positive-measure intervals. | **Lean-verified** |
| Remark 4.1 — equality/reversed inter-order trichotomy | `inter_order_curvature_trichotomy`; `inter_order_variance_trichotomy` | `InterOrderTrichotomy.lean` | Equality and reversed inequalities are proved as direct equivalences, not inferred merely from the strict case. | **Lean-verified** |

## Curvature proof architecture

Theorem 2.5 is intentionally split into small kernel-checked modules. The publication-facing theorem in `CurvatureManuscriptForm.lean` follows the causal chain actually used in the proof:

`Lemma 5.1 / tilted law / covariance` → `two-copy formula` → `symmetry + C² FTC` → `absolute Tonelli gate` → `signed Fubini` → `R_k`.

The absolute-convergence stage is established before signed Fubini. Internally, measurable representatives of `V''` and of the signed density are used only to satisfy measure-theoretic interfaces; they do not strengthen the public manuscript hypotheses.

There is a single publication-facing curvature theorem/corollary API: `curvature_theorem_2_5` and `curvature_corollary_2_6`. Helper results remain in the lower-level curvature modules and are not parallel manuscript endpoints.

## Formalization choices that preserve the manuscript hypotheses

- Full support is used to obtain strictness; the formalization does not replace it by the stronger assumption `h(y)>0` at every point.
- The one-crossing derivative law is an a.e. statement, appropriate for a merely measurable weight.
- The Gamma theorem is split into all-index and crossing blocks so that `k≥1` is not imposed where the manuscript does not require it.
- The curvature identity derives `h'=-V'h` from `h=exp(-V)` and `V∈C²` on the positive half-line instead of assuming differentiability of `h` separately.
- The curvature Fubini rearrangement is preceded by an explicit finite absolute Tonelli estimate using the manuscript envelope `A_k`.

## CI and provenance

The root module imports the entire formal development, including the Gamma and curvature manuscript-facing modules. Pull-request CI has two relevant jobs:

- `build`: GitHub's normal pull-request checkout, which checks the synthetic merge ref against `main`;
- `build-pr-head`: an explicit checkout of `github.event.pull_request.head.sha`, which checks the immutable submitted PR head.

Both jobs run `lake build --wfail` and `leanchecker`.

Because a file cannot contain the SHA of the commit that contains itself without creating a new commit, this matrix does not claim a self-referential “current SHA”. Immutable verification provenance should be taken from the successful exact-head CI run associated with the PR state or, for a publication release, from the release tag/archived DOI. A final release record should pin the tag, commit SHA, Lean/mathlib versions, and CI run.

## What remains outside the Lean claim

Even when every row above is green in CI, the formal verification does not certify manuscript novelty, literature completeness, priority, bibliographic accuracy, or the quality of the prose exposition. Those are separate scientific and editorial checks.
