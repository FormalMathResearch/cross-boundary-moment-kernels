import CrossBoundaryMomentKernels.CurvatureTwoCopyKappa

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

private lemma ae_positive_prod_manuscript :
    ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))),
      p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
  refine (Measure.ae_prod_mem_iff_ae_ae_mem
    (measurableSet_Ioi.prod measurableSet_Ioi)).2 ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact ⟨hy, hz⟩

/-- On the positive quadrant, the combined moment-density two-copy kernel is exactly the
signed integrand printed in manuscript Section 5.  This is only an algebraic identification:
no new analytic assumption is introduced. -/
theorem curvatureCombinedTwoCopyKernel_eq_manuscript
    (h : FullSupportMomentWeight) (V : ℝ → ℝ) (k : ℕ)
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    curvatureCombinedTwoCopyKernel h V k (y, z) =
      curvatureTwoCopyIntegrand h V k y z := by
  rw [curvatureCombinedTwoCopyKernel,
    curvatureCovarianceTwoCopyKernel_succ_eq_product h V k hy hz,
    curvatureCovarianceTwoCopyKernel, curvatureTwoCopyIntegrand]
  rw [Real.mul_rpow hy.le hz.le]
  simp only [momentIntegrand, halfExponent, momentA, Real.rpow_eq_pow]
  ring_nf

/-- The manuscript's exact signed two-copy integrand is absolutely integrable on
`(0,∞) × (0,∞)`.  This is inherited from the two covariance estimates already proved from the
stated weighted-`V'` assumptions. -/
theorem CurvaturePairingHypotheses.curvatureTwoCopyIntegrand_integrable
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    Integrable (fun p : ℝ × ℝ => curvatureTwoCopyIntegrand h V k p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  refine H.curvatureCombinedTwoCopyKernel_integrable.congr ?_
  filter_upwards [ae_positive_prod_manuscript] with p hp
  exact curvatureCombinedTwoCopyKernel_eq_manuscript h V k hp.1 hp.2

/-- **Exact manuscript two-copy representation of `κ_k`.**
Before the fundamental-theorem and Tonelli/Fubini step, manuscript Section 5 has
`κ_k = (2 b_k c_k I_k I_{k+1})⁻¹ ∬ (yz)^{a_k} h(y) h(z)
  (y-z) (V'(y)-V'(z)) (τ_k-yz) dy dz`.
This theorem is that formula verbatim, with the double integral represented by the product
Lebesgue measure restricted to the positive quadrant. -/
theorem CurvaturePairingHypotheses.momentCurvature_eq_twoCopy_manuscript
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    momentCurvature h k =
      (2 * momentB k * momentC k * I h k * I h (k + 1))⁻¹ *
        ∫ p, curvatureTwoCopyIntegrand h V k p.1 p.2
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [H.momentCurvature_eq_combinedTwoCopy]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_positive_prod_manuscript] with p hp
  exact curvatureCombinedTwoCopyKernel_eq_manuscript h V k hp.1 hp.2

end CrossBoundaryMomentKernels