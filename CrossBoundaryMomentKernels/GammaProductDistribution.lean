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

/-- Equality of complex moment-generating functions on the vertical strip
`-1/2 < re z < 1/2`. The proof upgrades the local real MGF identity by holomorphic uniqueness. -/
theorem gammaNormalizedProduct_complexMGF_eqOn_strip
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    Set.EqOn
      (ProbabilityTheory.complexMGF (gammaNormalizedProduct u)
        (crossBoundaryMeasure (gammaFullSupportWeight a ha) k u))
      (ProbabilityTheory.complexMGF id
        (ProbabilityTheory.gammaMeasure (gammaAlpha a k) 1))
      {z : ℂ | z.re ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)} := by
  let h := gammaFullSupportWeight a ha
  let μ := crossBoundaryMeasure h k u
  let ν := ProbabilityTheory.gammaMeasure (gammaAlpha a k) 1
  change Set.EqOn
    (ProbabilityTheory.complexMGF (gammaNormalizedProduct u) μ)
    (ProbabilityTheory.complexMGF id ν)
    {z : ℂ | z.re ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)}
  have hX : AnalyticOnNhd ℂ
      (ProbabilityTheory.complexMGF (gammaNormalizedProduct u) μ)
      {z : ℂ | z.re ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)} := by
    intro z hz
    apply ProbabilityTheory.analyticAt_complexMGF
    have hz' := gammaNormalizedProduct_Ioo_subset_interior_integrableExpSet ha k hu hz
    simpa [μ, h] using hz'
  have hG : AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF id ν)
      {z : ℂ | z.re ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)} := by
    intro z hz
    apply ProbabilityTheory.analyticAt_complexMGF
    have hz' := gammaMeasure_Ioo_subset_interior_integrableExpSet
      (gammaAlpha_pos ha k) hz
    simpa [ν] using hz'
  have hpre : IsPreconnected {z : ℂ | z.re ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)} := by
    exact ((convex_Ioo (𝕜 := ℝ) (-(1 / 2 : ℝ)) (1 / 2 : ℝ)).linear_preimage
      Complex.reLm).isPreconnected
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hX hG hpre
    (z₀ := (0 : ℂ)) (by norm_num) ?_
  have hlocal :
      ProbabilityTheory.mgf (gammaNormalizedProduct u) μ =ᶠ[𝓝 (0 : ℝ)]
        ProbabilityTheory.mgf id ν := by
    simpa [μ, h, ν] using gammaNormalizedProduct_mgf_eventuallyEq ha k hu
  have hlocal' : ∀ᶠ (x : ℝ) in 𝓝[≠] (0 : ℝ),
      ProbabilityTheory.complexMGF (gammaNormalizedProduct u) μ (x : ℂ) =
        ProbabilityTheory.complexMGF id ν (x : ℂ) := by
    have hm : ∀ᶠ (x : ℝ) in 𝓝[≠] (0 : ℝ),
        ProbabilityTheory.mgf (gammaNormalizedProduct u) μ x =
          ProbabilityTheory.mgf id ν x :=
      hlocal.filter_mono inf_le_left
    filter_upwards [hm] with x hx
    simpa [ProbabilityTheory.complexMGF_ofReal] using hx
  have hreal : ∃ᶠ (x : ℝ) in 𝓝[≠] (0 : ℝ),
      ProbabilityTheory.complexMGF (gammaNormalizedProduct u) μ (x : ℂ) =
        ProbabilityTheory.complexMGF id ν (x : ℂ) := hlocal'.frequently
  rw [frequently_iff_seq_forall] at hreal ⊢
  obtain ⟨xs, hx_tendsto, hx_eq⟩ := hreal
  refine ⟨fun n ↦ (xs n : ℂ), ?_, fun n ↦ ?_⟩
  · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · change Tendsto (fun n => (xs n : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ))
      rw [tendsto_ofReal_iff]
      exact hx_tendsto.1
    · simpa using hx_tendsto.2
  · simpa using hx_eq n

end CrossBoundaryMomentKernels
