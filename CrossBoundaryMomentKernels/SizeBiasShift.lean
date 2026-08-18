import CrossBoundaryMomentKernels.SizeBias

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace CrossBoundaryMomentKernels

/-- The Radon--Nikodym factor `X / M_k(u)` in the multiplicative size-bias step. -/
def multiplicativeBiasDensity
    (h : ℝ → ℝ) (k : ℕ) (u : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (crossBoundaryProduct p / crossBoundaryMean h k u)

/-- The size-bias factor is measurable. -/
lemma multiplicativeBiasDensity_measurable
    (h : ℝ → ℝ) (k : ℕ) (u : ℝ) :
    Measurable (multiplicativeBiasDensity h k u) := by
  have hX : Measurable crossBoundaryProduct := by
    simpa [crossBoundaryProduct] using measurable_fst.mul measurable_snd
  exact (hX.div_const _).ennreal_ofReal

/-- On the cross-boundary domain, the real normalized densities satisfy
`d_{k+1} = d_k * X / M_k`. -/
lemma crossBoundaryDensity_succ_eq_mul
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    crossBoundaryDensity h (k + 1) u =ᵐ[crossBoundaryBaseMeasure u]
      fun p ↦ crossBoundaryDensity h k u p *
        (crossBoundaryProduct p / crossBoundaryMean h k u) := by
  have hK : K h k u ≠ 0 := ne_of_gt (K_pos h k hu)
  have hK1 : K h (k + 1) u ≠ 0 := ne_of_gt (K_pos h (k + 1) hu)
  filter_upwards [ae_mem_crossBoundaryRect u] with p hp
  have hz : 0 < p.2 := lt_trans hu hp.2
  rw [crossBoundaryDensity, crossBoundaryDensity,
    crossBoundaryIntegrand_add_index h k 1 hp.1.1 hz,
    crossBoundaryMean_eq_K_ratio h k hu]
  simp only [pow_one]
  field_simp [hK, hK1]
  ring

/-- The ENNReal densities satisfy the exact multiplication law needed by `withDensity`. -/
lemma crossBoundaryENNRealDensity_succ_eq_mul
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    (fun p ↦ ENNReal.ofReal (crossBoundaryDensity h (k + 1) u p)) =ᵐ[
        crossBoundaryBaseMeasure u]
      fun p ↦ ENNReal.ofReal (crossBoundaryDensity h k u p) *
        multiplicativeBiasDensity h k u p := by
  have hM : 0 < crossBoundaryMean h k u := crossBoundaryMean_pos h k hu
  filter_upwards [crossBoundaryDensity_succ_eq_mul h k hu,
    crossBoundaryDensity_nonneg_ae h k hu, ae_mem_crossBoundaryRect u] with p hdens hden0 hp
  have hX0 : 0 ≤ crossBoundaryProduct p := by
    rw [crossBoundaryProduct]
    exact mul_nonneg hp.1.1.le (le_trans hu.le hp.2.le)
  have hbias0 : 0 ≤ crossBoundaryProduct p / crossBoundaryMean h k u :=
    div_nonneg hX0 hM.le
  rw [multiplicativeBiasDensity]
  calc
    ENNReal.ofReal (crossBoundaryDensity h (k + 1) u p) =
        ENNReal.ofReal
          (crossBoundaryDensity h k u p *
            (crossBoundaryProduct p / crossBoundaryMean h k u)) := by rw [hdens]
    _ = ENNReal.ofReal (crossBoundaryDensity h k u p) *
        ENNReal.ofReal (crossBoundaryProduct p / crossBoundaryMean h k u) :=
      ENNReal.ofReal_mul hden0

/-- **Multiplicative size bias from manuscript Theorem 2.2(vi).**
The law at index `k+1` is obtained from the law at index `k` by tilting with `X / E[X]`. -/
theorem crossBoundaryMeasure_succ_sizeBias
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    crossBoundaryMeasure h (k + 1) u =
      (crossBoundaryMeasure h k u).withDensity (multiplicativeBiasDensity h k u) := by
  have hf : AEMeasurable
      (fun p ↦ ENNReal.ofReal (crossBoundaryDensity h k u p))
      (crossBoundaryBaseMeasure u) :=
    (crossBoundaryDensity_integrable h k hu).aemeasurable.ennreal_ofReal
  have hg : AEMeasurable (multiplicativeBiasDensity h k u)
      (crossBoundaryBaseMeasure u) :=
    (multiplicativeBiasDensity_measurable h k u).aemeasurable
  change
    (crossBoundaryBaseMeasure u).withDensity
        (fun p ↦ ENNReal.ofReal (crossBoundaryDensity h (k + 1) u p)) =
      ((crossBoundaryBaseMeasure u).withDensity
        (fun p ↦ ENNReal.ofReal (crossBoundaryDensity h k u p))).withDensity
          (multiplicativeBiasDensity h k u)
  rw [← withDensity_mul₀ hf hg]
  exact withDensity_congr_ae (crossBoundaryENNRealDensity_succ_eq_mul h k hu)

end CrossBoundaryMomentKernels
