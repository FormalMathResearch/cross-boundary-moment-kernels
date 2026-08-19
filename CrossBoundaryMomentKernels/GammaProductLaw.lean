import CrossBoundaryMomentKernels.GammaCorollaries
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace CrossBoundaryMomentKernels

/-- The product variable normalized by the truncation level, `X/u`. -/
def gammaNormalizedProduct (u : ℝ) (p : ℝ × ℝ) : ℝ :=
  crossBoundaryProduct p / u

lemma gammaAlpha_add_index (a : ℝ) (k m : ℕ) :
    gammaAlpha a (k + m) = gammaAlpha a k + (m : ℝ) := by
  rw [gammaAlpha, gammaAlpha]
  push_cast
  ring

/-- In the Gamma family, adjacent index shifts of the cross-boundary kernel give the exact
normalized moment factor. -/
lemma gamma_K_add_ratio {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k m : ℕ) {u : ℝ}
    (hu : 0 < u) :
    K (gammaFullSupportWeight a ha) (k + m) u /
        K (gammaFullSupportWeight a ha) k u =
      (I (gammaFullSupportWeight a ha) (k + m) /
          I (gammaFullSupportWeight a ha) k) * u ^ m := by
  have hIk : I (gammaFullSupportWeight a ha) k ≠ 0 :=
    ne_of_gt ((gammaFullSupportWeight a ha).momentPositive k)
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hexp : Real.exp (-u) ≠ 0 := Real.exp_ne_zero (-u)
  rw [gamma_K_eq ha (k + m) hu.le, gamma_K_eq ha k hu.le,
    gammaAlpha_add_index]
  rw [Real.rpow_add hu, Real.rpow_natCast]
  field_simp [hIk, hu0, hexp]

/-- **Normalized Gamma cross-boundary moments.** Under `ν_{k,u}`, the variable `X/u` has
moments `Γ(α_k+m)/Γ(α_k)`. -/
theorem gamma_normalizedProduct_moment {a : ℝ} (ha : -(1 / 2 : ℝ) < a)
    (k m : ℕ) {u : ℝ} (hu : 0 < u) :
    ∫ p, (gammaNormalizedProduct u p) ^ m
        ∂crossBoundaryMeasure (gammaFullSupportWeight a ha) k u =
      Real.Gamma (gammaAlpha a (k + m)) / Real.Gamma (gammaAlpha a k) := by
  have hu0 : u ≠ 0 := ne_of_gt hu
  calc
    ∫ p, (gammaNormalizedProduct u p) ^ m
        ∂crossBoundaryMeasure (gammaFullSupportWeight a ha) k u =
        u⁻¹ ^ m *
          ∫ p, (crossBoundaryProduct p) ^ m
            ∂crossBoundaryMeasure (gammaFullSupportWeight a ha) k u := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with p
      simp [gammaNormalizedProduct, div_eq_mul_inv, mul_pow, mul_comm]
    _ = u⁻¹ ^ m *
        (K (gammaFullSupportWeight a ha) (k + m) u /
          K (gammaFullSupportWeight a ha) k u) := by
      rw [crossBoundary_moment_identity (gammaFullSupportWeight a ha) k m hu]
    _ = I (gammaFullSupportWeight a ha) (k + m) /
        I (gammaFullSupportWeight a ha) k := by
      rw [gamma_K_add_ratio ha k m hu]
      calc
        u⁻¹ ^ m *
            ((I (gammaFullSupportWeight a ha) (k + m) /
                I (gammaFullSupportWeight a ha) k) * u ^ m) =
            (I (gammaFullSupportWeight a ha) (k + m) /
                I (gammaFullSupportWeight a ha) k) * (u⁻¹ ^ m * u ^ m) := by ring
        _ = I (gammaFullSupportWeight a ha) (k + m) /
            I (gammaFullSupportWeight a ha) k := by
          rw [← mul_pow, inv_mul_cancel₀ hu0, one_pow, mul_one]
    _ = Real.Gamma (gammaAlpha a (k + m)) / Real.Gamma (gammaAlpha a k) := by
      change I (gammaModelWeight a) (k + m) / I (gammaModelWeight a) k = _
      rw [gamma_I_eq_Gamma ha (k + m), gamma_I_eq_Gamma ha k]

/-- Integer moments of a unit-rate Gamma law. -/
theorem gammaMeasure_moment {α : ℝ} (hα : 0 < α) (m : ℕ) :
    ∫ x : ℝ, x ^ m ∂ProbabilityTheory.gammaMeasure α 1 =
      Real.Gamma (α + m) / Real.Gamma α := by
  have hpdf_nonneg : ∀ x : ℝ, 0 ≤ ProbabilityTheory.gammaPDFReal α 1 x :=
    ProbabilityTheory.gammaPDFReal_nonneg hα (by norm_num)
  have hmeas : AEMeasurable (ProbabilityTheory.gammaPDF α 1) volume := by
    exact (ProbabilityTheory.measurable_gammaPDFReal α 1).ennreal_ofReal.aemeasurable
  have htop : ∀ᵐ x ∂volume, ProbabilityTheory.gammaPDF α 1 x < ∞ := by
    filter_upwards with x
    exact ENNReal.ofReal_lt_top
  rw [ProbabilityTheory.gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas htop]
  simp_rw [ProbabilityTheory.gammaPDF, ENNReal.toReal_ofReal (hpdf_nonneg _), smul_eq_mul]
  calc
    ∫ x : ℝ, ProbabilityTheory.gammaPDFReal α 1 x * x ^ m =
        ∫ x : ℝ in Ici 0, ProbabilityTheory.gammaPDFReal α 1 x * x ^ m := by
      rw [← integral_indicator measurableSet_Ici]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : 0 ≤ x
      · simp [Set.mem_Ici, hx]
      · simp [Set.mem_Ici, hx, ProbabilityTheory.gammaPDFReal]
    _ = ∫ x : ℝ in Ioi 0,
        (1 / Real.Gamma α) * x ^ (α + m - 1) * Real.exp (-x) := by
      rw [integral_Ici_eq_integral_Ioi]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change 0 < x at hx
      simp [ProbabilityTheory.gammaPDFReal, hx.le]
      rw [show α + (m : ℝ) - 1 = (α - 1) + (m : ℝ) by ring,
        Real.rpow_add hx, Real.rpow_natCast]
      ring
    _ = (1 / Real.Gamma α) *
        ∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ ((α + m) - 1) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      ring
    _ = Real.Gamma (α + m) / Real.Gamma α := by
      rw [(Real.Gamma_eq_integral (by positivity : 0 < α + m)).symm]
      ring

end CrossBoundaryMomentKernels
