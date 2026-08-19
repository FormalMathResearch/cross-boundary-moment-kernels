import CrossBoundaryMomentKernels.CurvatureTwoCopy

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- The covariance two-copy kernel at the next index is absolutely integrable.  This is the
manuscript's second absolute-convergence estimate, using the `b_k` and `c_k` weighted-derivative
hypotheses and no stronger assumption. -/
theorem CurvaturePairingHypotheses.curvatureCovarianceTwoCopyKernel_integrable_succ
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    Integrable (curvatureCovarianceTwoCopyKernel h V (k + 1))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let f1 : ℝ → ℝ := momentIntegrand h (k + 1)
  let f2 : ℝ → ℝ := momentIntegrand h (k + 2)
  let q1 : ℝ → ℝ := fun y => momentIntegrand h (k + 1) y * deriv V y
  let q2 : ℝ → ℝ := fun y => momentIntegrand h (k + 2) y * deriv V y
  have hf1 : Integrable f1 μ := by simpa [μ, f1, IntegrableOn] using h.momentIntegrable (k + 1)
  have hf2 : Integrable f2 μ := by simpa [μ, f2, IntegrableOn] using h.momentIntegrable (k + 2)
  have hq1 : Integrable q1 μ := by simpa [μ, q1] using H.momentIntegrand_mul_deriv_integrable_at_B
  have hq2 : Integrable q2 μ := by simpa [μ, q2] using H.momentIntegrand_mul_deriv_integrable_at_C
  let E : ℝ × ℝ → ℝ := fun p =>
    q2 p.1 * f1 p.2 - f2 p.1 * q1 p.2 - q1 p.1 * f2 p.2 + f1 p.1 * q2 p.2
  have hE : Integrable E (μ.prod μ) := by
    dsimp [E]
    exact (((hq2.mul_prod hf1).sub (hf2.mul_prod hq1)).sub
      (hq1.mul_prod hf2)).add (hf1.mul_prod hq2)
  have hEq : E =ᵐ[μ.prod μ] curvatureCovarianceTwoCopyKernel h V (k + 1) := by
    filter_upwards [ae_positive_prod] with p hp
    have hsY := momentIntegrand_succ h (k + 1) hp.1
    have hsZ := momentIntegrand_succ h (k + 1) hp.2
    dsimp [E, f1, f2, q1, q2, curvatureCovarianceTwoCopyKernel]
    rw [hsY, hsZ]
    ring
  simpa [μ] using hE.congr hEq

/-- Exact evaluation of the next-index covariance two-copy integral. -/
theorem CurvaturePairingHypotheses.integral_curvatureCovarianceTwoCopyKernel_succ
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    ∫ p, curvatureCovarianceTwoCopyKernel h V (k + 1) p
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) =
      2 * (momentC k * (I h (k + 1))^2 -
        momentB k * I h k * I h (k + 2)) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let f1 : ℝ → ℝ := momentIntegrand h (k + 1)
  let f2 : ℝ → ℝ := momentIntegrand h (k + 2)
  let q1 : ℝ → ℝ := fun y => momentIntegrand h (k + 1) y * deriv V y
  let q2 : ℝ → ℝ := fun y => momentIntegrand h (k + 2) y * deriv V y
  let E : ℝ × ℝ → ℝ := fun p =>
    q2 p.1 * f1 p.2 - f2 p.1 * q1 p.2 - q1 p.1 * f2 p.2 + f1 p.1 * q2 p.2
  have hf1 : Integrable f1 μ := by simpa [μ, f1, IntegrableOn] using h.momentIntegrable (k + 1)
  have hf2 : Integrable f2 μ := by simpa [μ, f2, IntegrableOn] using h.momentIntegrable (k + 2)
  have hq1 : Integrable q1 μ := by simpa [μ, q1] using H.momentIntegrand_mul_deriv_integrable_at_B
  have hq2 : Integrable q2 μ := by simpa [μ, q2] using H.momentIntegrand_mul_deriv_integrable_at_C
  have h1 := hq2.mul_prod hf1
  have h2 := hf2.mul_prod hq1
  have h3 := hq1.mul_prod hf2
  have h4 := hf1.mul_prod hq2
  have hEq : E =ᵐ[μ.prod μ] curvatureCovarianceTwoCopyKernel h V (k + 1) := by
    filter_upwards [ae_positive_prod] with p hp
    have hsY := momentIntegrand_succ h (k + 1) hp.1
    have hsZ := momentIntegrand_succ h (k + 1) hp.2
    dsimp [E, f1, f2, q1, q2, curvatureCovarianceTwoCopyKernel]
    rw [hsY, hsZ]
    ring
  rw [← integral_congr_ae hEq]
  have hEfun : E =
      (fun p : ℝ × ℝ => q2 p.1 * f1 p.2) -
      (fun p : ℝ × ℝ => f2 p.1 * q1 p.2) -
      (fun p : ℝ × ℝ => q1 p.1 * f2 p.2) +
      (fun p : ℝ × ℝ => f1 p.1 * q2 p.2) := by
    funext p
    rfl
  rw [hEfun]
  have hadd :
      (∫ p, (q2 p.1 * f1 p.2 - f2 p.1 * q1 p.2 - q1 p.1 * f2 p.2) +
          f1 p.1 * q2 p.2 ∂(μ.prod μ)) =
        (∫ p, q2 p.1 * f1 p.2 - f2 p.1 * q1 p.2 - q1 p.1 * f2 p.2
            ∂(μ.prod μ)) +
          ∫ p, f1 p.1 * q2 p.2 ∂(μ.prod μ) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      (integral_add ((h1.sub h2).sub h3) h4)
  have hsub3 :
      (∫ p, q2 p.1 * f1 p.2 - f2 p.1 * q1 p.2 - q1 p.1 * f2 p.2
          ∂(μ.prod μ)) =
        (∫ p, q2 p.1 * f1 p.2 - f2 p.1 * q1 p.2 ∂(μ.prod μ)) -
          ∫ p, q1 p.1 * f2 p.2 ∂(μ.prod μ) := by
    simpa only [Pi.sub_apply] using integral_sub (h1.sub h2) h3
  have hsub2 :
      (∫ p, q2 p.1 * f1 p.2 - f2 p.1 * q1 p.2 ∂(μ.prod μ)) =
        (∫ p, q2 p.1 * f1 p.2 ∂(μ.prod μ)) -
          ∫ p, f2 p.1 * q1 p.2 ∂(μ.prod μ) := by
    simpa only [Pi.sub_apply] using integral_sub h1 h2
  change
    (∫ p, q2 p.1 * f1 p.2 - f2 p.1 * q1 p.2 - q1 p.1 * f2 p.2 +
        f1 p.1 * q2 p.2 ∂(μ.prod μ)) = _
  rw [hadd, hsub3, hsub2]
  simp only [integral_prod_mul]
  change
    (∫ y, momentIntegrand h (k + 2) y * deriv V y ∂μ) * I h (k + 1) -
      I h (k + 2) * (∫ y, momentIntegrand h (k + 1) y * deriv V y ∂μ) -
      (∫ y, momentIntegrand h (k + 1) y * deriv V y ∂μ) * I h (k + 2) +
      I h (k + 1) * (∫ y, momentIntegrand h (k + 2) y * deriv V y ∂μ) = _
  rw [show (∫ y, momentIntegrand h (k + 1) y * deriv V y ∂μ) =
        momentB k * I h k by simpa [μ] using H.integral_momentIntegrand_mul_deriv_at_B,
      show (∫ y, momentIntegrand h (k + 2) y * deriv V y ∂μ) =
        momentC k * I h (k + 1) by simpa [μ] using H.integral_momentIntegrand_mul_deriv_at_C]
  ring

/-- The manuscript two-copy formula for `C_{k+1}`. -/
theorem CurvaturePairingHypotheses.curvatureCovariance_succ_eq_twoCopy
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    curvatureCovariance h V (k + 1) =
      (2 * (I h (k + 1))^2)⁻¹ *
        ∫ p, curvatureCovarianceTwoCopyKernel h V (k + 1) p
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [H.curvatureCovariance_succ_eq, H.integral_curvatureCovarianceTwoCopyKernel_succ]
  rw [momentRatioScale, momentRatioScale, ← momentC_eq_A_add_two, ← momentB_eq_A_succ]
  have hk1 : k + 1 - 1 = k := by omega
  have hk2 : k + 2 - 1 = k + 1 := by omega
  rw [hk1, hk2]
  field_simp [ne_of_gt (h.momentPositive k), ne_of_gt (h.momentPositive (k + 1)),
    ne_of_gt (h.momentPositive (k + 2)),
    ne_of_gt (show 0 < momentB k by rw [momentB]; positivity),
    ne_of_gt (show 0 < momentC k by rw [momentC]; positivity)]

/-- The manuscript scale ratio in the form needed to combine the two covariance integrals:
`τ_k = c_k I_{k+1} / (a_k I_{k-1})`. -/
theorem tau_eq_curvature_moment_ratio
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    tau h k = momentC k * I h (k + 1) / (momentA k * I h (k - 1)) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hminus : (2 : ℝ) * (k : ℝ) - 1 ≠ 0 := by linarith
  have hplus : (2 : ℝ) * (k : ℝ) + 1 ≠ 0 := by linarith
  have hplus3 : (2 : ℝ) * (k : ℝ) + 3 ≠ 0 := by linarith
  have hkidx : k + 1 - 1 = k := by omega
  rw [tau, N, N, hkidx, momentA, momentC]
  push_cast
  field_simp [hminus, hplus, hplus3, ne_of_gt (h.momentPositive (k - 1)),
    ne_of_gt (h.momentPositive k), ne_of_gt (h.momentPositive (k + 1))]
  ring

/-- The exact combined two-copy integrand before replacing the `V'` difference by an integral of
`V''`.  On the positive quadrant it is the manuscript integrand written with moment densities. -/
def curvatureCombinedTwoCopyKernel
    (h : FullSupportMomentWeight) (V : ℝ → ℝ) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  tau h k * curvatureCovarianceTwoCopyKernel h V k p -
    curvatureCovarianceTwoCopyKernel h V (k + 1) p

/-- The next-index two-copy kernel is multiplication of the current kernel by `yz`. -/
theorem curvatureCovarianceTwoCopyKernel_succ_eq_product
    (h : FullSupportMomentWeight) (V : ℝ → ℝ) (k : ℕ) {p : ℝ × ℝ}
    (hy : 0 < p.1) (hz : 0 < p.2) :
    curvatureCovarianceTwoCopyKernel h V (k + 1) p =
      (p.1 * p.2) * curvatureCovarianceTwoCopyKernel h V k p := by
  have hsY := momentIntegrand_succ h k hy
  have hsZ := momentIntegrand_succ h k hz
  rw [curvatureCovarianceTwoCopyKernel, curvatureCovarianceTwoCopyKernel, hsY, hsZ]
  ring

/-- Absolute convergence of the exact combined two-copy integral. -/
theorem CurvaturePairingHypotheses.curvatureCombinedTwoCopyKernel_integrable
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    Integrable (curvatureCombinedTwoCopyKernel h V k)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  exact (H.curvatureCovarianceTwoCopyKernel_integrable.const_mul (tau h k)).sub
    H.curvatureCovarianceTwoCopyKernel_integrable_succ

/-- The combined integral is `τ_k` times the `C_k` two-copy integral minus its next-index
counterpart. -/
theorem CurvaturePairingHypotheses.integral_curvatureCombinedTwoCopyKernel
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    ∫ p, curvatureCombinedTwoCopyKernel h V k p
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) =
      tau h k *
        ∫ p, curvatureCovarianceTwoCopyKernel h V k p
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) -
        ∫ p, curvatureCovarianceTwoCopyKernel h V (k + 1) p
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [curvatureCombinedTwoCopyKernel]
  rw [integral_sub H.curvatureCovarianceTwoCopyKernel_integrable.const_mul
    H.curvatureCovarianceTwoCopyKernel_integrable_succ]
  rw [integral_const_mul]

/-- Exact two-copy representation of manuscript `κ_k`, before the fundamental-theorem/Fubini
step.  This is algebraically the printed double integral with the common denominator
`2 b_k c_k I_k I_{k+1}`. -/
theorem CurvaturePairingHypotheses.momentCurvature_eq_combinedTwoCopy
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    momentCurvature h k =
      (2 * momentB k * momentC k * I h k * I h (k + 1))⁻¹ *
        ∫ p, curvatureCombinedTwoCopyKernel h V k p
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [H.momentCurvature_eq_covariance_difference,
    H.curvatureCovariance_eq_twoCopy, H.curvatureCovariance_succ_eq_twoCopy,
    H.integral_curvatureCombinedTwoCopyKernel]
  rw [momentRatioScale, momentRatioScale, tau_eq_curvature_moment_ratio h H.index]
  have hk1 : k + 1 - 1 = k := by omega
  rw [hk1]
  field_simp [ne_of_gt (h.momentPositive (k - 1)), ne_of_gt (h.momentPositive k),
    ne_of_gt (h.momentPositive (k + 1)), ne_of_gt (momentA_pos H.index),
    ne_of_gt (show 0 < momentB k by rw [momentB]; positivity),
    ne_of_gt (show 0 < momentC k by rw [momentC]; positivity)]
  ring

end CrossBoundaryMomentKernels