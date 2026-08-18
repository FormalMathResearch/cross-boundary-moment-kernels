import CrossBoundaryMomentKernels.GramManuscriptForm
import Mathlib.Probability.Moments.Variance

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace CrossBoundaryMomentKernels

/-- The product measure on the cross-boundary region `D_u = {0 < y ≤ u < z}`.
The endpoint convention at `y = u` is immaterial for Lebesgue integration. -/
def crossBoundaryBaseMeasure (u : ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc (0 : ℝ) u)).prod (volume.restrict (Ioi u))

/-- The multiplicative observable `X = Y Z`. -/
def crossBoundaryProduct (p : ℝ × ℝ) : ℝ := p.1 * p.2

/-- The real-valued normalized density of the cross-boundary probability law. -/
def crossBoundaryDensity
    (h : ℝ → ℝ) (k : ℕ) (u : ℝ) (p : ℝ × ℝ) : ℝ :=
  (K h k u)⁻¹ * crossBoundaryIntegrand h k p

/-- The cross-boundary law `ν_{k,u}` from Theorem 2.2(vi). -/
def crossBoundaryMeasure
    (h : ℝ → ℝ) (k : ℕ) (u : ℝ) : Measure (ℝ × ℝ) :=
  (crossBoundaryBaseMeasure u).withDensity
    (fun p ↦ ENNReal.ofReal (crossBoundaryDensity h k u p))

/-- Almost every point of the base measure lies in the cross-boundary rectangle. -/
lemma ae_mem_crossBoundaryRect (u : ℝ) :
    ∀ᵐ p ∂crossBoundaryBaseMeasure u, p ∈ Ioc (0 : ℝ) u ×ˢ Ioi u := by
  rw [crossBoundaryBaseMeasure]
  refine (Measure.ae_prod_mem_iff_ae_ae_mem
    (measurableSet_Ioc.prod measurableSet_Ioi)).2 ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact ⟨hy, hz⟩

/-- Advancing a moment index by `m` multiplies the integrand by `y^m`. -/
lemma momentIntegrand_add_index
    (h : ℝ → ℝ) (j m : ℕ) {y : ℝ} (hy : 0 < y) :
    momentIntegrand h (j + m) y = y ^ m * momentIntegrand h j y := by
  induction m with
  | zero => simp
  | succ m ihm =>
      have hs := momentIntegrand_succ h (j + m) hy
      have hidx : j + (m + 1) = (j + m) + 1 := by omega
      rw [hidx, hs, ihm, pow_succ]
      ring

/-- Raising the cross-boundary index by `m` is multiplication by `X^m`. -/
lemma crossBoundaryIntegrand_add_index
    (h : ℝ → ℝ) (k m : ℕ) {p : ℝ × ℝ} (hy : 0 < p.1) (hz : 0 < p.2) :
    crossBoundaryIntegrand h (k + m) p =
      (crossBoundaryProduct p) ^ m * crossBoundaryIntegrand h k p := by
  rw [crossBoundaryIntegrand, crossBoundaryIntegrand,
    momentIntegrand_add_index h k m hy, momentIntegrand_add_index h k m hz,
    crossBoundaryProduct, mul_pow]
  ring

/-- The cross-boundary kernel is integrable on its defining product domain. -/
lemma crossBoundaryIntegrand_integrable_base
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    Integrable (crossBoundaryIntegrand h k) (crossBoundaryBaseMeasure u) := by
  let μL : Measure ℝ := volume.restrict (Ioc (0 : ℝ) u)
  let μR : Measure ℝ := volume.restrict (Ioi u)
  let D : ℝ × ℝ → ℝ := fun p ↦
    momentIntegrand h k p.1 * momentIntegrand h (k + 1) p.2 -
      momentIntegrand h (k + 1) p.1 * momentIntegrand h k p.2
  have hkL : Integrable (momentIntegrand h k) μL := by
    simpa [μL, IntegrableOn] using
      (h.momentIntegrable k).mono_set (by intro y hy; exact hy.1)
  have hk1L : Integrable (momentIntegrand h (k + 1)) μL := by
    simpa [μL, IntegrableOn] using
      (h.momentIntegrable (k + 1)).mono_set (by intro y hy; exact hy.1)
  have hkR : Integrable (momentIntegrand h k) μR := by
    simpa [μR, IntegrableOn] using
      (h.momentIntegrable k).mono_set (by intro z hz; exact lt_trans hu hz)
  have hk1R : Integrable (momentIntegrand h (k + 1)) μR := by
    simpa [μR, IntegrableOn] using
      (h.momentIntegrable (k + 1)).mono_set (by intro z hz; exact lt_trans hu hz)
  have hD : Integrable D (μL.prod μR) := by
    dsimp [D]
    exact (hkL.mul_prod hk1R).sub (hk1L.mul_prod hkR)
  have hrect : ∀ᵐ p ∂(μL.prod μR), p ∈ Ioc (0 : ℝ) u ×ˢ Ioi u := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioc.prod measurableSet_Ioi)).2 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact ⟨hy, hz⟩
  have hEq : D =ᵐ[μL.prod μR] crossBoundaryIntegrand h k := by
    filter_upwards [hrect] with p hp
    have hy : 0 < p.1 := hp.1.1
    have hz : 0 < p.2 := lt_trans hu hp.2
    have hyS := momentIntegrand_succ h k hy
    have hzS := momentIntegrand_succ h k hz
    dsimp [D, crossBoundaryIntegrand]
    rw [hyS, hzS]
    ring
  simpa [crossBoundaryBaseMeasure, μL, μR] using hD.congr hEq

/-- The normalized real density is integrable. -/
lemma crossBoundaryDensity_integrable
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    Integrable (crossBoundaryDensity h k u) (crossBoundaryBaseMeasure u) := by
  exact (crossBoundaryIntegrand_integrable_base h k hu).const_mul _

/-- The normalized real density is nonnegative almost everywhere. -/
lemma crossBoundaryDensity_nonneg_ae
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    0 ≤ᵐ[crossBoundaryBaseMeasure u] crossBoundaryDensity h k u := by
  have hK : 0 ≤ (K h k u)⁻¹ := inv_nonneg.mpr (K_pos h k hu).le
  filter_upwards [ae_mem_crossBoundaryRect u] with p hp
  have hz : 0 < p.2 := lt_trans hu hp.2
  have hyz : p.1 < p.2 := lt_of_le_of_lt hp.1.2 hp.2
  rw [crossBoundaryDensity, crossBoundaryIntegrand]
  exact mul_nonneg hK <| mul_nonneg
    (mul_nonneg (momentIntegrand_nonneg h k hp.1.1) (momentIntegrand_nonneg h k hz))
    (sub_nonneg.mpr hyz.le)

/-- The normalized density integrates to one. -/
lemma integral_crossBoundaryDensity
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    ∫ p, crossBoundaryDensity h k u p ∂crossBoundaryBaseMeasure u = 1 := by
  have hKint :
      ∫ p, crossBoundaryIntegrand h k p ∂crossBoundaryBaseMeasure u = K h k u := by
    simpa [crossBoundaryBaseMeasure] using (K_eq_crossBoundaryIntegral h k hu).symm
  change ∫ p, (K h k u)⁻¹ * crossBoundaryIntegrand h k p
      ∂crossBoundaryBaseMeasure u = 1
  rw [integral_const_mul, hKint]
  exact inv_mul_cancel₀ (ne_of_gt (K_pos h k hu))

/-- The manuscript density really defines a probability measure. -/
theorem crossBoundaryMeasure_isProbability
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    IsProbabilityMeasure (crossBoundaryMeasure h k u) := by
  constructor
  rw [crossBoundaryMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (crossBoundaryDensity_integrable h k hu) (crossBoundaryDensity_nonneg_ae h k hu)]
  rw [integral_crossBoundaryDensity h k hu]
  simp

/-- Integration against `ν_{k,u}` is normalized integration against the cross-boundary kernel. -/
theorem integral_crossBoundaryMeasure
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) (g : ℝ × ℝ → ℝ) :
    ∫ p, g p ∂crossBoundaryMeasure h k u =
      ∫ p, crossBoundaryDensity h k u p * g p ∂crossBoundaryBaseMeasure u := by
  have hdenInt := crossBoundaryDensity_integrable h k hu
  have hmeas : AEMeasurable
      (fun p ↦ ENNReal.ofReal (crossBoundaryDensity h k u p))
      (crossBoundaryBaseMeasure u) :=
    hdenInt.1.aemeasurable.ennreal_ofReal
  have htop : ∀ᵐ p ∂crossBoundaryBaseMeasure u,
      ENNReal.ofReal (crossBoundaryDensity h k u p) < ∞ := by
    filter_upwards with p
    exact ENNReal.ofReal_lt_top
  rw [crossBoundaryMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas htop]
  apply integral_congr_ae
  filter_upwards [crossBoundaryDensity_nonneg_ae h k hu] with p hp
  simp [ENNReal.toReal_ofReal hp, smul_eq_mul]

/-- **Moment identity from manuscript Theorem 2.2(vi).** For every integer `m ≥ 0`,
`E_{k,u}[X^m] = K_{k+m}(u) / K_k(u)`. -/
theorem crossBoundary_moment_identity
    (h : FullSupportMomentWeight) (k m : ℕ) {u : ℝ} (hu : 0 < u) :
    ∫ p, (crossBoundaryProduct p) ^ m ∂crossBoundaryMeasure h k u =
      K h (k + m) u / K h k u := by
  rw [integral_crossBoundaryMeasure h k hu]
  have hEq :
      (fun p ↦ crossBoundaryDensity h k u p * (crossBoundaryProduct p) ^ m) =ᵐ[
        crossBoundaryBaseMeasure u]
      (fun p ↦ (K h k u)⁻¹ * crossBoundaryIntegrand h (k + m) p) := by
    filter_upwards [ae_mem_crossBoundaryRect u] with p hp
    have hz : 0 < p.2 := lt_trans hu hp.2
    rw [crossBoundaryDensity, crossBoundaryIntegrand_add_index h k m hp.1.1 hz]
    ring
  rw [integral_congr_ae hEq, integral_const_mul]
  have hKm :
      ∫ p, crossBoundaryIntegrand h (k + m) p ∂crossBoundaryBaseMeasure u =
        K h (k + m) u := by
    simpa [crossBoundaryBaseMeasure] using
      (K_eq_crossBoundaryIntegral h (k + m) hu).symm
  rw [hKm]
  simp [div_eq_mul_inv, mul_comm]

/-- The mean `M_k(u) = E_{k,u}[X]`. -/
def crossBoundaryMean
    (h : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  ∫ p, crossBoundaryProduct p ∂crossBoundaryMeasure h k u

/-- Manuscript formula `M_k(u) = K_{k+1}(u) / K_k(u)`. -/
theorem crossBoundaryMean_eq_K_ratio
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    crossBoundaryMean h k u = K h (k + 1) u / K h k u := by
  simpa [crossBoundaryMean] using crossBoundary_moment_identity h k 1 hu

/-- The mean is strictly positive. -/
theorem crossBoundaryMean_pos
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    0 < crossBoundaryMean h k u := by
  rw [crossBoundaryMean_eq_K_ratio h k hu]
  exact div_pos (K_pos h (k + 1) hu) (K_pos h k hu)

end CrossBoundaryMomentKernels
