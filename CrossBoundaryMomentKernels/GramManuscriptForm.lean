import CrossBoundaryMomentKernels.GramDecomposition

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- The exact two-variable Gram integrand printed in Theorem 2.2(v). -/
def truncatedGramManuscriptIntegrand
    (h : ℝ → ℝ) (k : ℕ) (y z : ℝ) : ℝ :=
  Real.rpow (y * z) ((k : ℝ) + (1 / 2 : ℝ)) * (y - z) ^ 2 * h y * h z

/-- On the positive quadrant the factorized Gram integrand is exactly the manuscript integrand. -/
lemma truncatedGramIntegrand_eq_manuscript
    (h : FullSupportMomentWeight) (k : ℕ) {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    truncatedGramIntegrand h (k + 1) (y, z) =
      truncatedGramManuscriptIntegrand h k y z := by
  have hexp : halfExponent (k + 1) = (k : ℝ) + (1 / 2 : ℝ) := by
    simp [halfExponent]
    ring
  rw [truncatedGramIntegrand, momentIntegrand, momentIntegrand, hexp,
    truncatedGramManuscriptIntegrand, Real.mul_rpow hy.le hz.le]
  ring

/-- Manuscript-exact iterated double-integral representation of the truncated Hankel minor. -/
theorem truncated_hankel_gram_identity_manuscript
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    J h (k + 1) u * J h (k + 3) u - (J h (k + 2) u) ^ 2 =
      (1 / 2 : ℝ) *
        ∫ y, (∫ z, truncatedGramManuscriptIntegrand h k y z
          ∂(volume.restrict (Ioc (0 : ℝ) u)))
          ∂(volume.restrict (Ioc (0 : ℝ) u)) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) u)
  have hcore := truncated_hankel_gram_identity h (k + 1) hu
  have hInt : Integrable (truncatedGramIntegrand h (k + 1)) (μ.prod μ) := by
    simpa [μ] using truncatedGramIntegrand_integrable h (k + 1) hu
  have hfubini :
      (∫ p, truncatedGramIntegrand h (k + 1) p ∂(μ.prod μ)) =
        ∫ y, (∫ z, truncatedGramIntegrand h (k + 1) (y, z) ∂μ) ∂μ :=
    integral_prod _ hInt
  have hμpos : ∀ᵐ x ∂μ, 0 < x := by
    dsimp [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hx.1
  have hiter :
      (∫ y, (∫ z, truncatedGramIntegrand h (k + 1) (y, z) ∂μ) ∂μ) =
        ∫ y, (∫ z, truncatedGramManuscriptIntegrand h k y z ∂μ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hμpos] with y hy
    apply integral_congr_ae
    filter_upwards [hμpos] with z hz
    exact truncatedGramIntegrand_eq_manuscript h k hy hz
  calc
    J h (k + 1) u * J h (k + 3) u - (J h (k + 2) u) ^ 2 =
        (1 / 2 : ℝ) * ∫ p, truncatedGramIntegrand h (k + 1) p ∂(μ.prod μ) := by
      simpa [μ] using hcore
    _ = (1 / 2 : ℝ) *
        ∫ y, (∫ z, truncatedGramIntegrand h (k + 1) (y, z) ∂μ) ∂μ := by
      rw [hfubini]
    _ = (1 / 2 : ℝ) *
        ∫ y, (∫ z, truncatedGramManuscriptIntegrand h k y z ∂μ) ∂μ := by
      rw [hiter]
    _ = (1 / 2 : ℝ) *
        ∫ y, (∫ z, truncatedGramManuscriptIntegrand h k y z
          ∂(volume.restrict (Ioc (0 : ℝ) u)))
          ∂(volume.restrict (Ioc (0 : ℝ) u)) := by
      rfl

/-- **Manuscript Theorem 2.2(v).** The next crossing kernel is the sum of the positive
truncated Gram variance and the explicit quadratic transport term, with the exact
Hankel-ratio and double-integral forms printed in the manuscript. -/
theorem universal_truncated_gram_decomposition
    (h : FullSupportMomentWeight) :
    ∀ ⦃k : ℕ⦄, 1 ≤ k → ∀ ⦃u : ℝ⦄, 0 < u →
      R h (k + 1) u / (2 * I h (k + 2) * J h (k + 1) u) =
          truncatedVar h k u + crossingQ h (k + 1) (truncatedMu h k u) ∧
      truncatedVar h k u =
          (J h (k + 1) u * J h (k + 3) u - (J h (k + 2) u) ^ 2) /
            (J h (k + 1) u) ^ 2 ∧
      0 < truncatedVar h k u ∧
      J h (k + 1) u * J h (k + 3) u - (J h (k + 2) u) ^ 2 =
        (1 / 2 : ℝ) *
          ∫ y, (∫ z, truncatedGramManuscriptIntegrand h k y z
            ∂(volume.restrict (Ioc (0 : ℝ) u)))
            ∂(volume.restrict (Ioc (0 : ℝ) u)) := by
  intro k hk u hu
  exact ⟨crossing_kernel_succ_gram_decomposition h hk hu,
    truncatedVar_eq_hankel_ratio h k hu,
    truncatedVar_pos h k hu,
    truncated_hankel_gram_identity_manuscript h k hu⟩

end CrossBoundaryMomentKernels
