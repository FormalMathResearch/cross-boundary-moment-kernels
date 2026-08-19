import CrossBoundaryMomentKernels.CurvatureCovariance
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- The symmetric two-copy kernel used for the covariance at moment index `j`. -/
def curvatureCovarianceTwoCopyKernel
    (h : FullSupportMomentWeight) (V : ℝ → ℝ) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  momentIntegrand h j p.1 * momentIntegrand h j p.2 *
    (p.1 - p.2) * (deriv V p.1 - deriv V p.2)

lemma halfExponent_succ_eq_momentB (k : ℕ) :
    halfExponent (k + 1) = momentB k := by
  rw [halfExponent, momentB]
  push_cast
  ring

lemma halfExponent_add_two_eq_momentC (k : ℕ) :
    halfExponent (k + 2) = momentC k := by
  rw [halfExponent, momentC]
  push_cast
  ring

/-- Absolute weighted-derivative integrability at `a_k`, written in moment-integrand form. -/
theorem CurvaturePairingHypotheses.momentIntegrand_mul_deriv_integrable_at_A
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    Integrable (fun y : ℝ => momentIntegrand h k y * deriv V y)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hn := H.weightedWeightDerivative_integrableOn H.atA
  have hneg := hn.neg
  refine hneg.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simp only [Pi.neg_apply, momentIntegrand, halfExponent, momentA, Real.rpow_eq_pow]
  ring_nf

/-- Absolute weighted-derivative integrability at `b_k`, written in moment-integrand form. -/
theorem CurvaturePairingHypotheses.momentIntegrand_mul_deriv_integrable_at_B
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    Integrable (fun y : ℝ => momentIntegrand h (k + 1) y * deriv V y)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hn := H.weightedWeightDerivative_integrableOn H.atB
  have hneg := hn.neg
  refine hneg.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simp only [Pi.neg_apply, momentIntegrand, halfExponent_succ_eq_momentB, Real.rpow_eq_pow]
  ring_nf

/-- Absolute weighted-derivative integrability at `c_k`, written in moment-integrand form. -/
theorem CurvaturePairingHypotheses.momentIntegrand_mul_deriv_integrable_at_C
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    Integrable (fun y : ℝ => momentIntegrand h (k + 2) y * deriv V y)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hn := H.weightedWeightDerivative_integrableOn H.atC
  have hneg := hn.neg
  refine hneg.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simp only [Pi.neg_apply, momentIntegrand, halfExponent_add_two_eq_momentC, Real.rpow_eq_pow]
  ring_nf

/-- The `a_k` integration-by-parts identity in moment-integrand notation. -/
theorem CurvaturePairingHypotheses.integral_momentIntegrand_mul_deriv_at_A
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    ∫ y, momentIntegrand h k y * deriv V y
        ∂(volume.restrict (Ioi (0 : ℝ))) =
      momentA k * I h (k - 1) := by
  calc
    (∫ y, momentIntegrand h k y * deriv V y
        ∂(volume.restrict (Ioi (0 : ℝ)))) =
        ∫ y in Ioi (0 : ℝ), y ^ momentA k * deriv V y * h y := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
          simp only [momentIntegrand, halfExponent, momentA, Real.rpow_eq_pow]
          ring_nf
    _ = momentA k * I h (k - 1) := H.ibp_at_A

/-- The `b_k` integration-by-parts identity in moment-integrand notation. -/
theorem CurvaturePairingHypotheses.integral_momentIntegrand_mul_deriv_at_B
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    ∫ y, momentIntegrand h (k + 1) y * deriv V y
        ∂(volume.restrict (Ioi (0 : ℝ))) =
      momentB k * I h k := by
  calc
    (∫ y, momentIntegrand h (k + 1) y * deriv V y
        ∂(volume.restrict (Ioi (0 : ℝ)))) =
        ∫ y in Ioi (0 : ℝ), y ^ momentB k * deriv V y * h y := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
          simp only [momentIntegrand, halfExponent_succ_eq_momentB, Real.rpow_eq_pow]
          ring_nf
    _ = momentB k * I h k := H.ibp_at_B

/-- The `c_k` integration-by-parts identity in moment-integrand notation. -/
theorem CurvaturePairingHypotheses.integral_momentIntegrand_mul_deriv_at_C
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    ∫ y, momentIntegrand h (k + 2) y * deriv V y
        ∂(volume.restrict (Ioi (0 : ℝ))) =
      momentC k * I h (k + 1) := by
  calc
    (∫ y, momentIntegrand h (k + 2) y * deriv V y
        ∂(volume.restrict (Ioi (0 : ℝ)))) =
        ∫ y in Ioi (0 : ℝ), y ^ momentC k * deriv V y * h y := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
          simp only [momentIntegrand, halfExponent_add_two_eq_momentC, Real.rpow_eq_pow]
          ring_nf
    _ = momentC k * I h (k + 1) := H.ibp_at_C

private lemma ae_positive_prod :
    ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))),
      p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
  refine (Measure.ae_prod_mem_iff_ae_ae_mem
    (measurableSet_Ioi.prod measurableSet_Ioi)).2 ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact ⟨hy, hz⟩

/-- The covariance two-copy kernel at index `k` is absolutely integrable.  This is the formal
absolute-convergence statement behind the manuscript bound
`2 (I_k M_{b_k} + I_{k+1} M_{a_k}) < ∞`. -/
theorem CurvaturePairingHypotheses.curvatureCovarianceTwoCopyKernel_integrable
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    Integrable (curvatureCovarianceTwoCopyKernel h V k)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let f0 : ℝ → ℝ := momentIntegrand h k
  let f1 : ℝ → ℝ := momentIntegrand h (k + 1)
  let q0 : ℝ → ℝ := fun y => momentIntegrand h k y * deriv V y
  let q1 : ℝ → ℝ := fun y => momentIntegrand h (k + 1) y * deriv V y
  have hf0 : Integrable f0 μ := by simpa [μ, f0, IntegrableOn] using h.momentIntegrable k
  have hf1 : Integrable f1 μ := by simpa [μ, f1, IntegrableOn] using h.momentIntegrable (k + 1)
  have hq0 : Integrable q0 μ := by simpa [μ, q0] using H.momentIntegrand_mul_deriv_integrable_at_A
  have hq1 : Integrable q1 μ := by simpa [μ, q1] using H.momentIntegrand_mul_deriv_integrable_at_B
  let E : ℝ × ℝ → ℝ := fun p =>
    q1 p.1 * f0 p.2 - f1 p.1 * q0 p.2 - q0 p.1 * f1 p.2 + f0 p.1 * q1 p.2
  have hE : Integrable E (μ.prod μ) := by
    dsimp [E]
    exact (((hq1.mul_prod hf0).sub (hf1.mul_prod hq0)).sub
      (hq0.mul_prod hf1)).add (hf0.mul_prod hq1)
  have hEq : E =ᵐ[μ.prod μ] curvatureCovarianceTwoCopyKernel h V k := by
    filter_upwards [ae_positive_prod] with p hp
    have hsY := momentIntegrand_succ h k hp.1
    have hsZ := momentIntegrand_succ h k hp.2
    dsimp [E, f0, f1, q0, q1, curvatureCovarianceTwoCopyKernel]
    rw [hsY, hsZ]
    ring
  simpa [μ] using hE.congr hEq

/-- The exact double-integral evaluation underlying `C_k`. -/
theorem CurvaturePairingHypotheses.integral_curvatureCovarianceTwoCopyKernel
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    ∫ p, curvatureCovarianceTwoCopyKernel h V k p
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) =
      2 * (momentB k * (I h k)^2 - momentA k * I h (k - 1) * I h (k + 1)) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let f0 : ℝ → ℝ := momentIntegrand h k
  let f1 : ℝ → ℝ := momentIntegrand h (k + 1)
  let q0 : ℝ → ℝ := fun y => momentIntegrand h k y * deriv V y
  let q1 : ℝ → ℝ := fun y => momentIntegrand h (k + 1) y * deriv V y
  let E : ℝ × ℝ → ℝ := fun p =>
    q1 p.1 * f0 p.2 - f1 p.1 * q0 p.2 - q0 p.1 * f1 p.2 + f0 p.1 * q1 p.2
  have hf0 : Integrable f0 μ := by simpa [μ, f0, IntegrableOn] using h.momentIntegrable k
  have hf1 : Integrable f1 μ := by simpa [μ, f1, IntegrableOn] using h.momentIntegrable (k + 1)
  have hq0 : Integrable q0 μ := by simpa [μ, q0] using H.momentIntegrand_mul_deriv_integrable_at_A
  have hq1 : Integrable q1 μ := by simpa [μ, q1] using H.momentIntegrand_mul_deriv_integrable_at_B
  have h1 := hq1.mul_prod hf0
  have h2 := hf1.mul_prod hq0
  have h3 := hq0.mul_prod hf1
  have h4 := hf0.mul_prod hq1
  have hEq : E =ᵐ[μ.prod μ] curvatureCovarianceTwoCopyKernel h V k := by
    filter_upwards [ae_positive_prod] with p hp
    have hsY := momentIntegrand_succ h k hp.1
    have hsZ := momentIntegrand_succ h k hp.2
    dsimp [E, f0, f1, q0, q1, curvatureCovarianceTwoCopyKernel]
    rw [hsY, hsZ]
    ring
  rw [← integral_congr_ae hEq]
  change
    ∫ p,
      (((fun p : ℝ × ℝ => q1 p.1 * f0 p.2) - (fun p => f1 p.1 * q0 p.2) -
        (fun p => q0 p.1 * f1 p.2) + (fun p => f0 p.1 * q1 p.2)) p) ∂(μ.prod μ) = _
  rw [integral_add ((h1.sub h2).sub h3) h4, integral_sub (h1.sub h2) h3,
    integral_sub h1 h2]
  simp only [integral_prod_mul]
  change
    (∫ y, momentIntegrand h (k + 1) y * deriv V y ∂μ) * I h k -
      I h (k + 1) * (∫ y, momentIntegrand h k y * deriv V y ∂μ) -
      (∫ y, momentIntegrand h k y * deriv V y ∂μ) * I h (k + 1) +
      I h k * (∫ y, momentIntegrand h (k + 1) y * deriv V y ∂μ) = _
  rw [show (∫ y, momentIntegrand h k y * deriv V y ∂μ) =
        momentA k * I h (k - 1) by simpa [μ] using H.integral_momentIntegrand_mul_deriv_at_A,
      show (∫ y, momentIntegrand h (k + 1) y * deriv V y ∂μ) =
        momentB k * I h k by simpa [μ] using H.integral_momentIntegrand_mul_deriv_at_B]
  ring

/-- Manuscript two-copy formula for `C_k`:
`C_k = (2 I_k^2)^{-1} ∬ (yz)^{a_k}h(y)h(z)(y-z)(V'(y)-V'(z)) dy dz`. -/
theorem CurvaturePairingHypotheses.curvatureCovariance_eq_twoCopy
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    curvatureCovariance h V k =
      (2 * (I h k)^2)⁻¹ *
        ∫ p, curvatureCovarianceTwoCopyKernel h V k p
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [H.curvatureCovariance_eq, H.integral_curvatureCovarianceTwoCopyKernel]
  rw [momentRatioScale, momentRatioScale, ← momentB_eq_A_succ]
  have hk : k + 1 - 1 = k := by omega
  rw [hk]
  field_simp [ne_of_gt (h.momentPositive k), ne_of_gt (h.momentPositive (k - 1)),
    ne_of_gt (momentA_pos H.index), ne_of_gt (show 0 < momentB k by rw [momentB]; positivity)]

end CrossBoundaryMomentKernels