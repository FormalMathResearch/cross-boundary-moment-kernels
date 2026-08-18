import CrossBoundaryMomentKernels.SizeBiasVariance
import CrossBoundaryMomentKernels.CrossBoundaryManuscriptForm

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace CrossBoundaryMomentKernels

/-- The probability density printed in manuscript Theorem 2.2(vi):
`(yz)^(k-1/2) (z-y) h(y) h(z) / K_k(u)`. -/
def manuscriptCrossBoundaryDensity
    (h : ℝ → ℝ) (k : ℕ) (u : ℝ) (p : ℝ × ℝ) : ℝ :=
  manuscriptCrossBoundaryIntegrand h k p / K h k u

/-- On the cross-boundary domain, the robust normalized density is exactly the density
printed in Theorem 2.2(vi). -/
lemma crossBoundaryDensity_eq_manuscript_ae
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    crossBoundaryDensity h k u =ᵐ[crossBoundaryBaseMeasure u]
      manuscriptCrossBoundaryDensity h k u := by
  filter_upwards [ae_mem_crossBoundaryRect u] with p hp
  have hz : 0 < p.2 := lt_trans hu hp.2
  rw [crossBoundaryDensity, manuscriptCrossBoundaryDensity,
    crossBoundaryIntegrand_eq_manuscript h k hp.1.1 hz]
  simp [div_eq_mul_inv, mul_comm]

/-- The measure used in the probabilistic formalization is literally the manuscript law
when its printed density is interpreted with respect to the restricted cross-boundary
Lebesgue product measure. -/
theorem crossBoundaryMeasure_eq_manuscript
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    crossBoundaryMeasure h k u =
      (crossBoundaryBaseMeasure u).withDensity
        (fun p ↦ ENNReal.ofReal (manuscriptCrossBoundaryDensity h k u p)) := by
  change
    (crossBoundaryBaseMeasure u).withDensity
        (fun p ↦ ENNReal.ofReal (crossBoundaryDensity h k u p)) =
      (crossBoundaryBaseMeasure u).withDensity
        (fun p ↦ ENNReal.ofReal (manuscriptCrossBoundaryDensity h k u p))
  apply withDensity_congr_ae
  filter_upwards [crossBoundaryDensity_eq_manuscript_ae h k hu] with p hp
  rw [hp]

/-- **Manuscript Theorem 2.2(vi).** The cross-boundary law has exactly the printed density,
is a probability measure, has moments `E[X^m] = K_{k+m}/K_k`, advances by multiplicative
size bias, and its mean obeys the strict variance drift formula. -/
theorem theorem_2_2_vi_multiplicative_size_bias
    (h : FullSupportMomentWeight) :
    ∀ (k : ℕ) ⦃u : ℝ⦄, 0 < u →
      crossBoundaryMeasure h k u =
        (crossBoundaryBaseMeasure u).withDensity
          (fun p ↦ ENNReal.ofReal (manuscriptCrossBoundaryDensity h k u p)) ∧
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
  exact ⟨crossBoundaryMeasure_eq_manuscript h k hu,
    crossBoundaryMeasure_isProbability h k hu,
    fun m ↦ crossBoundary_moment_identity h k m hu,
    crossBoundaryMeasure_succ_sizeBias h k hu,
    crossBoundaryMean_succ_sub_eq_variance_div_mean h k hu,
    crossBoundaryVariance_pos h k hu,
    crossBoundaryMean_strictMono_index h k hu⟩

end CrossBoundaryMomentKernels
