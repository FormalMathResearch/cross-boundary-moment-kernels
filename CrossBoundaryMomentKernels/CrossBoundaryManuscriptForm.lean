import CrossBoundaryMomentKernels.CrossBoundaryRepresentation

noncomputable section

open MeasureTheory Set

namespace CrossBoundaryMomentKernels

/-- The cross-boundary integrand written exactly in the notation of manuscript Theorem 2.2(i). -/
def manuscriptCrossBoundaryIntegrand (h : ℝ → ℝ) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  Real.rpow (p.1 * p.2) (halfExponent k) * (p.2 - p.1) * h p.1 * h p.2

/-- On the positive quadrant, the robust factorized Lean integrand is exactly the integrand
printed in Theorem 2.2(i). -/
lemma crossBoundaryIntegrand_eq_manuscript
    (h : ℝ → ℝ) (k : ℕ) {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    crossBoundaryIntegrand h k (y, z) = manuscriptCrossBoundaryIntegrand h k (y, z) := by
  change
    (y ^ halfExponent k * h y) * (z ^ halfExponent k * h z) * (z - y) =
      (y * z) ^ halfExponent k * (z - y) * h y * h z
  calc
    (y ^ halfExponent k * h y) * (z ^ halfExponent k * h z) * (z - y) =
        (y ^ halfExponent k * z ^ halfExponent k) * (z - y) * h y * h z := by ring
    _ = (y * z) ^ halfExponent k * (z - y) * h y * h z := by
      rw [← Real.mul_rpow hy.le hz.le]

/-- Manuscript-exact iterated-integral statement of Theorem 2.2(i). -/
theorem K_eq_manuscriptCrossBoundaryIntegral
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    K h k u =
      ∫ y, ∫ z, manuscriptCrossBoundaryIntegrand h k (y, z)
        ∂(volume.restrict (Ioi u)) ∂(volume.restrict (Ioc (0 : ℝ) u)) := by
  calc
    K h k u =
        ∫ y, ∫ z, crossBoundaryIntegrand h k (y, z)
          ∂(volume.restrict (Ioi u)) ∂(volume.restrict (Ioc (0 : ℝ) u)) :=
      (crossBoundary_representation_and_pos h k hu).2.1
    _ =
        ∫ y, ∫ z, manuscriptCrossBoundaryIntegrand h k (y, z)
          ∂(volume.restrict (Ioi u)) ∂(volume.restrict (Ioc (0 : ℝ) u)) := by
      refine integral_congr_ae ?_
      have hleft_ae : ∀ᵐ y ∂(volume.restrict (Ioc (0 : ℝ) u)), y ∈ Ioc (0 : ℝ) u :=
        ae_restrict_mem measurableSet_Ioc
      filter_upwards [hleft_ae] with y hy
      refine integral_congr_ae ?_
      have hright_ae : ∀ᵐ z ∂(volume.restrict (Ioi u)), z ∈ Ioi u :=
        ae_restrict_mem measurableSet_Ioi
      filter_upwards [hright_ae] with z hz
      exact crossBoundaryIntegrand_eq_manuscript h k hy.1 (lt_trans hu hz)

end CrossBoundaryMomentKernels
