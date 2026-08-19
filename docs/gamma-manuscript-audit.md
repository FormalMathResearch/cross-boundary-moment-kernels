# Gamma manuscript audit — Theorem 2.7 through Proposition 2.10

Manuscript basis: **Cross-Boundary Moment Kernels**, revised draft of 18 August 2026, pp. 7–8.

This note records the theorem-by-theorem correspondence between the printed Gamma block and the Lean development.  Its purpose is to prevent a successful formal proof from being obtained by silently strengthening hypotheses, narrowing index ranges, or replacing a printed assertion by a nearby but different statement.

## Theorem 2.7 — Gamma model and sharpness

The manuscript assumes

- `h_a(y) = y^a exp(-y)`,
- `a > -1/2`,
- `α_k = k + a + 1/2`.

It first states the moment and determinant identities without imposing the later crossing-index restriction:

- `I_k = Γ(α_k)`,
- `K_k(u) = I_k u^{α_k} exp(-u)`.

Lean wrapper: `gamma_theorem_2_7_all_index`.

This wrapper deliberately accepts arbitrary `k : ℕ`; it does **not** add `k ≥ 1`.  The determinant statement is used for `u > 0`, the manuscript domain of the canonical kernels.  The underlying lemma `gamma_K_eq` is slightly stronger and also covers `u = 0`.

The manuscript then says **for every `k ≥ 1`** that the unique crossing is

`u_k* = ((2k+3)/(2k-1)) (k+a-1/2)`,

and gives the exact formulas for `R_k`, `Rhat_k`, `Z_{k+1}/Z_k`, the consecutive-crossing difference, and the sharp threshold.

Lean wrapper: `gamma_theorem_2_7_crossing`.

Supporting headline lemmas include:

- `gamma_uStar_eq`,
- `gamma_R_eq`,
- `gamma_Rhat_eq`,
- `gamma_Z_succ_div_Z`,
- `gammaCrossing_succ_sub`,
- `gamma_uStar_order_iff`,
- `gamma_uStar_eq_iff_threshold`,
- `gamma_uStar_reverse_order_iff`.

Thus all three cases printed in the theorem are explicit in Lean:

- increasing order exactly below `(4k^2-1)/8`,
- equality exactly at `(4k^2-1)/8`,
- reversed order exactly above `(4k^2-1)/8`.

## Corollary 2.8 — strict log-concavity does not force crossing order

The manuscript states that for `a > 0`, `h_a` is strictly log-concave, and gives the witness

`u_1* = 15/2 > 35/6 = u_2*`

at `a = 1`.

Lean wrapper: `gamma_corollary_2_8`.

The semantic bridge is formalized explicitly rather than left as notation:

- `gammaLogProfile_eq_log_gammaModelWeight` proves on `(0,∞)` that
  `gammaLogProfile a y = log (gammaModelWeight a y)`;
- `gammaLogProfile_strictConcaveOn_Ioi` proves strict concavity of this logarithm for `a > 0`;
- `gamma_a_one_reversed_crossing` proves the exact numerical crossing reversal.

Hence the formal statement is about the actual logarithm of the manuscript weight, not merely an auxiliary function with the same derivative.

## Corollary 2.9 — positive moment-ratio curvature is insufficient

For `k ≥ 1`, the manuscript states

- `s_k = 1 + a/(k-1/2)`,
- `κ_k = 16a / ((2k-1)(2k+1)(2k+3))`,
- therefore `κ_k > 0` for every `a > 0`, while crossing order may still reverse.

Lean wrapper: `gamma_corollary_2_9`.

The wrapper contains the two exact formulas, positivity under `a > 0`, and the explicit `a = 1` reversed-crossing witness.  No stronger regularity or positivity assumption is introduced.

## Proposition 2.10 — exact Gamma product law

The manuscript range is `k ≥ 0`, `u > 0`.  If `(Y,Z) ~ ν_{k,u}` and `X = YZ`, it states

`X/u ~ Γ(α_k, rate 1)`

and consequently

- `E[X] = α_k u`,
- `Var(X) = α_k u^2`.

Lean wrapper: `gamma_proposition_2_10`.

The distributional conclusion is formalized as equality of pushforward probability measures:

`(ν_{k,u}).map (X/u) = gammaMeasure α_k 1`.

This is stronger than bare moment matching in the logically relevant sense: the proof first establishes the moment/MGF identities, then uses analytic continuation and characteristic-function uniqueness to identify the measures.

The manuscript also prints the specialization at the canonical crossing

`Var_{k,u_k*}(X) = τ_k^2 / α_k`.

Lean theorem: `gamma_proposition_2_10_variance_at_crossing`.

Here Lean makes `k ≥ 1` explicit because Theorem 2.7 introduces the canonical crossing only in that range.  This is an indexing clarification, not an extra mathematical hypothesis on Proposition 2.10 itself.

## Audit conclusion

For pp. 7–8, the Lean wrappers now preserve the manuscript's mathematical content and index ranges theorem by theorem.  In particular:

1. the all-index `I_k` and `K_k` formulas are not artificially restricted to `k ≥ 1`;
2. the crossing formulas retain exactly the manuscript restriction `k ≥ 1`;
3. strict log-concavity is tied explicitly to `log h_a`, not inferred from an unnamed proxy;
4. the exact Gamma product law is equality of probability distributions, not only equality of moments;
5. the final variance-at-crossing clause records explicitly the index condition under which `u_k*` is defined in the manuscript.

The Gamma block should be called **Lean-verified** only at a commit for which both `lake build --wfail` and `leanchecker` pass.  The next mathematical block after this audit is Theorem 2.5 / Corollary 2.6, the curvature-pairing argument with its boundary terms, weighted `V'` integrability, and absolute Tonelli/Fubini control.
