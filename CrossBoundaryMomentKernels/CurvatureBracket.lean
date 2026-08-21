import CrossBoundaryMomentKernels.CurvatureAbsoluteIntegrability
import CrossBoundaryMomentKernels.CrossBoundaryRepresentation

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- The signed cross-boundary density left after the FTC/Fubini step in manuscript Section 5. -/
def curvatureSignedEnvelopeDensity
    (h : FullSupportMomentWeight) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  (p.1 * p.2) ^ (momentA k) * (p.2 - p.1) *
    (tau h k - p.1 * p.2) * h p.1 * h p.2

/-- On the positive quadrant, the signed curvature density is exactly
`τ_k` times the `K_k` cross-boundary density minus the `K_{k+1}` density. -/
theorem curvatureSignedEnvelopeDensity_eq_crossBoundary_difference
    (h : FullSupportMomentWeight) (k : ℕ) {y z : ℝ}
    (hy : 0 < y) (hz : 0 < z) :
    curvatureSignedEnvelopeDensity h k (y, z) =
      tau h k * crossBoundaryIntegrand h k (y, z) -
        crossBoundaryIntegrand h (k + 1) (y, z) := by
  have hy1 := momentIntegrand_succ h k hy
  have hz1 := momentIntegrand_succ h k hz
  rw [curvatureSignedEnvelopeDensity, crossBoundaryIntegrand, crossBoundaryIntegrand,
    hy1, hz1]
  rw [Real.mul_rpow hy.le hz.le]
  simp only [momentIntegrand, halfExponent, momentA, Real.rpow_eq_pow]
  ring_nf

/-- The cross-boundary kernel is integrable on every manuscript rectangle
`0 < y ≤ u < z`, solely from the moment assumptions. -/
theorem crossBoundaryIntegrand_integrable_rectangle
    (h : FullSupportMomentWeight) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    Integrable (crossBoundaryIntegrand h j)
      ((volume.restrict (Ioc (0 : ℝ) u)).prod (volume.restrict (Ioi u))) := by
  let μL : Measure ℝ := volume.restrict (Ioc (0 : ℝ) u)
  let μR : Measure ℝ := volume.restrict (Ioi u)
  let D : ℝ × ℝ → ℝ := fun p =>
    momentIntegrand h j p.1 * momentIntegrand h (j + 1) p.2 -
      momentIntegrand h (j + 1) p.1 * momentIntegrand h j p.2
  have hjL : Integrable (momentIntegrand h j) μL := by
    simpa [μL, IntegrableOn] using
      (h.momentIntegrable j).mono_set (by
        intro y hy
        exact hy.1)
  have hj1L : Integrable (momentIntegrand h (j + 1)) μL := by
    simpa [μL, IntegrableOn] using
      (h.momentIntegrable (j + 1)).mono_set (by
        intro y hy
        exact hy.1)
  have hjR : Integrable (momentIntegrand h j) μR := by
    simpa [μR, IntegrableOn] using
      (h.momentIntegrable j).mono_set (by
        intro z hz
        exact lt_trans hu hz)
  have hj1R : Integrable (momentIntegrand h (j + 1)) μR := by
    simpa [μR, IntegrableOn] using
      (h.momentIntegrable (j + 1)).mono_set (by
        intro z hz
        exact lt_trans hu hz)
  have hD : Integrable D (μL.prod μR) := by
    dsimp [D]
    exact (hjL.mul_prod hj1R).sub (hj1L.mul_prod hjR)
  have hleft : ∀ᵐ y ∂μL, y ∈ Ioc (0 : ℝ) u := by
    dsimp [μL]
    exact ae_restrict_mem measurableSet_Ioc
  have hright : ∀ᵐ z ∂μR, z ∈ Ioi u := by
    dsimp [μR]
    exact ae_restrict_mem measurableSet_Ioi
  have hrect : ∀ᵐ p ∂(μL.prod μR), p ∈ Ioc (0 : ℝ) u ×ˢ Ioi u := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioc.prod measurableSet_Ioi)).2 ?_
    filter_upwards [hleft] with y hy
    filter_upwards [hright] with z hz
    exact ⟨hy, hz⟩
  have heq : D =ᵐ[μL.prod μR] crossBoundaryIntegrand h j := by
    filter_upwards [hrect] with p hp
    have hy : 0 < p.1 := hp.1.1
    have hz : 0 < p.2 := lt_trans hu hp.2
    have hy1 := momentIntegrand_succ h j hy
    have hz1 := momentIntegrand_succ h j hz
    dsimp [D, crossBoundaryIntegrand]
    rw [hy1, hz1]
    ring
  simpa [μL, μR] using hD.congr heq

/-- **Inner-bracket identification from manuscript Section 5.**
For every `u>0`, the signed rectangle integral obtained after Fubini is
`τ_k K_k(u) - K_{k+1}(u) = R_k(u)/2`. -/
theorem curvatureSignedEnvelopeIntegral_eq_R_half
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    (∫ p, curvatureSignedEnvelopeDensity h k p
      ∂((volume.restrict (Ioc (0 : ℝ) u)).prod (volume.restrict (Ioi u)))) =
      R h k u / 2 := by
  let μL : Measure ℝ := volume.restrict (Ioc (0 : ℝ) u)
  let μR : Measure ℝ := volume.restrict (Ioi u)
  have hk : Integrable (crossBoundaryIntegrand h k) (μL.prod μR) := by
    simpa [μL, μR] using crossBoundaryIntegrand_integrable_rectangle h k hu
  have hk1 : Integrable (crossBoundaryIntegrand h (k + 1)) (μL.prod μR) := by
    simpa [μL, μR] using crossBoundaryIntegrand_integrable_rectangle h (k + 1) hu
  have hleft : ∀ᵐ y ∂μL, y ∈ Ioc (0 : ℝ) u := by
    dsimp [μL]
    exact ae_restrict_mem measurableSet_Ioc
  have hright : ∀ᵐ z ∂μR, z ∈ Ioi u := by
    dsimp [μR]
    exact ae_restrict_mem measurableSet_Ioi
  have hrect : ∀ᵐ p ∂(μL.prod μR), p ∈ Ioc (0 : ℝ) u ×ˢ Ioi u := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioc.prod measurableSet_Ioi)).2 ?_
    filter_upwards [hleft] with y hy
    filter_upwards [hright] with z hz
    exact ⟨hy, hz⟩
  have heq :
      curvatureSignedEnvelopeDensity h k =ᵐ[μL.prod μR]
        (fun p => tau h k * crossBoundaryIntegrand h k p -
          crossBoundaryIntegrand h (k + 1) p) := by
    filter_upwards [hrect] with p hp
    exact curvatureSignedEnvelopeDensity_eq_crossBoundary_difference h k
      hp.1.1 (lt_trans hu hp.2)
  have hK := K_eq_crossBoundaryIntegral h k hu
  have hK1 := K_eq_crossBoundaryIntegral h (k + 1) hu
  change (∫ p, curvatureSignedEnvelopeDensity h k p ∂(μL.prod μR)) = _
  calc
    (∫ p, curvatureSignedEnvelopeDensity h k p ∂(μL.prod μR)) =
        ∫ p, tau h k * crossBoundaryIntegrand h k p -
          crossBoundaryIntegrand h (k + 1) p ∂(μL.prod μR) :=
      integral_congr_ae heq
    _ = tau h k * (∫ p, crossBoundaryIntegrand h k p ∂(μL.prod μR)) -
        ∫ p, crossBoundaryIntegrand h (k + 1) p ∂(μL.prod μR) := by
      rw [integral_sub (hk.const_mul (tau h k)) hk1, integral_const_mul]
    _ = tau h k * K h k u - K h (k + 1) u := by
      rw [← hK, ← hK1]
    _ = R h k u / 2 := by
      rw [R]
      ring

end CrossBoundaryMomentKernels
