import CrossBoundaryMomentKernels.CrossBoundaryKGram

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace CrossBoundaryMomentKernels

/-- The multiplicative observable `X = YZ` is measurable. -/
lemma crossBoundaryProduct_measurable : Measurable crossBoundaryProduct := by
  change Measurable (fun p : ℝ × ℝ ↦ p.1 * p.2)
  exact measurable_fst.mul measurable_snd

/-- The square of `X` is integrable under the cross-boundary probability law. -/
lemma crossBoundaryProduct_sq_integrable
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    Integrable (fun p ↦ (crossBoundaryProduct p) ^ 2) (crossBoundaryMeasure h k u) := by
  let μ : Measure (ℝ × ℝ) := crossBoundaryBaseMeasure u
  let f : ℝ × ℝ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (crossBoundaryDensity h k u p)
  have hf : AEMeasurable f μ := by
    dsimp [f, μ]
    exact (crossBoundaryDensity_integrable h k hu).aemeasurable.ennreal_ofReal
  have htop : ∀ᵐ p ∂μ, f p < ∞ := by
    filter_upwards with p
    exact ENNReal.ofReal_lt_top
  change Integrable (fun p ↦ (crossBoundaryProduct p) ^ 2) (μ.withDensity f)
  rw [integrable_withDensity_iff_integrable_smul₀' hf htop]
  have htarget : Integrable
      (fun p ↦ (K h k u)⁻¹ * crossBoundaryIntegrand h (k + 2) p) μ := by
    exact (crossBoundaryIntegrand_integrable_base h (k + 2) hu).const_mul _
  apply htarget.congr
  filter_upwards [crossBoundaryDensity_nonneg_ae h k hu, ae_mem_crossBoundaryRect u]
    with p hden hp
  have hz : 0 < p.2 := lt_trans hu hp.2
  have hadd := crossBoundaryIntegrand_add_index h k 2 hp.1.1 hz
  dsimp [f]
  rw [ENNReal.toReal_ofReal hden, crossBoundaryDensity, hadd]
  simp only [smul_eq_mul]
  ring

/-- The observable `X` belongs to `L²(ν_{k,u})`. -/
lemma crossBoundaryProduct_memLp_two
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    MemLp crossBoundaryProduct 2 (crossBoundaryMeasure h k u) := by
  have hmeas : AEStronglyMeasurable crossBoundaryProduct (crossBoundaryMeasure h k u) :=
    crossBoundaryProduct_measurable.aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hmeas).2 (crossBoundaryProduct_sq_integrable h k hu)

/-- The genuine probabilistic variance of `X = YZ` under `ν_{k,u}`. -/
def crossBoundaryVariance
    (h : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  ProbabilityTheory.variance crossBoundaryProduct (crossBoundaryMeasure h k u)

/-- Exact second-moment formula for the probabilistic variance. -/
theorem crossBoundaryVariance_eq_K
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    crossBoundaryVariance h k u =
      K h (k + 2) u / K h k u - (K h (k + 1) u / K h k u) ^ 2 := by
  letI : IsProbabilityMeasure (crossBoundaryMeasure h k u) :=
    crossBoundaryMeasure_isProbability h k hu
  rw [crossBoundaryVariance, ProbabilityTheory.variance_eq_sub
    (crossBoundaryProduct_memLp_two h k hu)]
  change
    (∫ p, (crossBoundaryProduct p) ^ 2 ∂crossBoundaryMeasure h k u) -
      (∫ p, crossBoundaryProduct p ∂crossBoundaryMeasure h k u) ^ 2 = _
  rw [crossBoundary_moment_identity h k 2 hu]
  rw [show (∫ p, crossBoundaryProduct p ∂crossBoundaryMeasure h k u) =
      K h (k + 1) u / K h k u by
    simpa [crossBoundaryMean] using crossBoundaryMean_eq_K_ratio h k hu]

/-- The cross-boundary variance is strictly positive. -/
theorem crossBoundaryVariance_pos
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    0 < crossBoundaryVariance h k u := by
  have hK : 0 < K h k u := K_pos h k hu
  have hnum : 0 < K h k u * K h (k + 2) u - (K h (k + 1) u) ^ 2 :=
    sub_pos.mpr (strict_crossBoundary_K_logConvexity h k hu)
  rw [crossBoundaryVariance_eq_K h k hu]
  have heq :
      K h (k + 2) u / K h k u - (K h (k + 1) u / K h k u) ^ 2 =
        (K h k u * K h (k + 2) u - (K h (k + 1) u) ^ 2) / (K h k u) ^ 2 := by
    field_simp [ne_of_gt hK]
    ring
  rw [heq]
  exact div_pos hnum (sq_pos_of_pos hK)

/-- **Variance drift identity from manuscript Theorem 2.2(vi).** -/
theorem crossBoundaryMean_succ_sub_eq_variance_div_mean
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    crossBoundaryMean h (k + 1) u - crossBoundaryMean h k u =
      crossBoundaryVariance h k u / crossBoundaryMean h k u := by
  have hK : K h k u ≠ 0 := ne_of_gt (K_pos h k hu)
  have hK1 : K h (k + 1) u ≠ 0 := ne_of_gt (K_pos h (k + 1) hu)
  rw [crossBoundaryMean_eq_K_ratio h (k + 1) hu,
    crossBoundaryMean_eq_K_ratio h k hu,
    crossBoundaryVariance_eq_K h k hu]
  field_simp [hK, hK1]
  ring

/-- Consecutive cross-boundary means increase strictly. -/
theorem crossBoundaryMean_strictMono_index
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    crossBoundaryMean h k u < crossBoundaryMean h (k + 1) u := by
  have hvar : 0 < crossBoundaryVariance h k u := crossBoundaryVariance_pos h k hu
  have hmean : 0 < crossBoundaryMean h k u := crossBoundaryMean_pos h k hu
  have hdrift := crossBoundaryMean_succ_sub_eq_variance_div_mean h k hu
  have hpos : 0 < crossBoundaryMean h (k + 1) u - crossBoundaryMean h k u := by
    rw [hdrift]
    exact div_pos hvar hmean
  linarith

/-- Complete kernel-checked probabilistic hierarchy from manuscript Theorem 2.2(vi),
except for the separate manuscript-syntax translation of its density. -/
theorem universal_multiplicative_size_bias
    (h : FullSupportMomentWeight) :
    ∀ (k : ℕ) ⦃u : ℝ⦄, 0 < u →
      IsProbabilityMeasure (crossBoundaryMeasure h k u) ∧
      (∀ m : ℕ,
        ∫ p, (crossBoundaryProduct p) ^ m ∂crossBoundaryMeasure h k u =
          K h (k + m) u / K h k u) ∧
      crossBoundaryMeasure h (k + 1) u =
        (crossBoundaryMeasure h k u).withDensity (multiplicativeBiasDensity h k u) ∧
      crossBoundaryMean h (k + 1) u - crossBoundaryMean h k u =
        crossBoundaryVariance h k u / crossBoundaryMean h k u ∧
      0 < crossBoundaryVariance h k u ∧
      crossBoundaryMean h k u < crossBoundaryMean h (k + 1) u := by
  intro k u hu
  exact ⟨crossBoundaryMeasure_isProbability h k hu,
    fun m ↦ crossBoundary_moment_identity h k m hu,
    crossBoundaryMeasure_succ_sizeBias h k hu,
    crossBoundaryMean_succ_sub_eq_variance_div_mean h k hu,
    crossBoundaryVariance_pos h k hu,
    crossBoundaryMean_strictMono_index h k hu⟩

end CrossBoundaryMomentKernels
