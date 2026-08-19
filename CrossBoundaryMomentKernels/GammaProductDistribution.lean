import CrossBoundaryMomentKernels.GammaProductMGF

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ProbabilityTheory Topology

namespace CrossBoundaryMomentKernels

/-- The normalized cross-boundary product and the corresponding unit-rate Gamma law have the
same moment-generating function on a neighborhood of zero. This is the determinacy step missing
from bare equality of all integer moments. -/
theorem gammaNormalizedProduct_mgf_eventuallyEq
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    ProbabilityTheory.mgf (gammaNormalizedProduct u)
        (crossBoundaryMeasure (gammaFullSupportWeight a ha) k u) =ᶠ[𝓝 (0 : ℝ)]
      ProbabilityTheory.mgf id
        (ProbabilityTheory.gammaMeasure (gammaAlpha a k) 1) := by
  let μ := crossBoundaryMeasure (gammaFullSupportWeight a ha) k u
  let ν := ProbabilityTheory.gammaMeasure (gammaAlpha a k) 1
  have h0X :
      0 ∈ interior (ProbabilityTheory.integrableExpSet (gammaNormalizedProduct u) μ) := by
    apply gammaNormalizedProduct_Ioo_subset_interior_integrableExpSet ha k hu
    norm_num
  have h0G : 0 ∈ interior (ProbabilityTheory.integrableExpSet id ν) := by
    apply gammaMeasure_Ioo_subset_interior_integrableExpSet (gammaAlpha_pos ha k)
    norm_num
  have hpsX := ProbabilityTheory.hasFPowerSeriesAt_mgf
    (X := gammaNormalizedProduct u) (μ := μ) h0X
  have hpsG := ProbabilityTheory.hasFPowerSeriesAt_mgf
    (X := id) (μ := ν) h0G
  simp only [zero_mul, Real.exp_zero, mul_one, id_eq] at hpsX hpsG
  have hseries :
      FormalMultilinearSeries.ofScalars ℝ
          (fun n ↦ ((∫ p, gammaNormalizedProduct u p ^ n ∂μ) : ℝ) /
            (Nat.factorial n : ℝ)) =
        FormalMultilinearSeries.ofScalars ℝ
          (fun n ↦ ((∫ x : ℝ, x ^ n ∂ν) : ℝ) /
            (Nat.factorial n : ℝ)) := by
    rw [FormalMultilinearSeries.ofScalars_series_eq_iff]
    funext n
    rw [gamma_normalizedProduct_moment_eq_gammaMeasure ha k n hu]
  rw [hseries] at hpsX
  filter_upwards [hpsX.eventually_hasSum_sub, hpsG.eventually_hasSum_sub] with t hX hG
  exact hX.unique hG

end CrossBoundaryMomentKernels
