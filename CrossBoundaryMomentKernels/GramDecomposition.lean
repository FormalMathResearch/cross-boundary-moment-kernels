import CrossBoundaryMomentKernels.TotalPositivityHierarchy

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- The truncated mean `μ_k(u) = J_{k+2}(u) / J_{k+1}(u)` from Theorem 2.2(v). -/
def truncatedMu (h : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  J h (k + 2) u / J h (k + 1) u

/-- The truncated variance term
`v_k(u) = J_{k+3}(u) / J_{k+1}(u) - μ_k(u)^2` from Theorem 2.2(v). -/
def truncatedVar (h : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  J h (k + 3) u / J h (k + 1) u - (truncatedMu h k u) ^ 2

/-- Every truncated half-integer moment is strictly positive at a positive truncation point. -/
lemma J_pos (h : FullSupportMomentWeight) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    0 < J h j u := by
  have hInt : IntegrableOn (momentIntegrand h j) (Ioc (0 : ℝ) u) :=
    (h.momentIntegrable j).mono_set (by intro x hx; exact hx.1)
  have hNonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) u)] momentIntegrand h j := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    exact momentIntegrand_nonneg h j hx.1
  have hsupp :
      Function.support (h : ℝ → ℝ) ∩ Ioc (u / 2) u ⊆
        Function.support (momentIntegrand h j) ∩ Ioc (0 : ℝ) u := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.2.1, hu]
    refine ⟨?_, ⟨hx0, hx.2.2⟩⟩
    exact ne_of_gt (momentIntegrand_pos_of_mem_support h j hx0 hx.1)
  have hSuppPos :
      0 < volume (Function.support (momentIntegrand h j) ∩ Ioc (0 : ℝ) u) := by
    have hinner :
        0 < volume (Function.support (h : ℝ → ℝ) ∩ Ioc (u / 2) u) :=
      support_h_measure_pos_Ioc h (by linarith [hu]) (by linarith [hu])
    exact lt_of_lt_of_le hinner (measure_mono hsupp)
  have hpos :
      0 < ∫ x, momentIntegrand h j x ∂(volume.restrict (Ioc (0 : ℝ) u)) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hNonneg hInt).2 hSuppPos
  simpa [J] using hpos

/-- Algebraic Hankel-ratio form of the truncated variance term. -/
lemma truncatedVar_eq_hankel_ratio
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    truncatedVar h k u =
      (J h (k + 1) u * J h (k + 3) u - (J h (k + 2) u) ^ 2) /
        (J h (k + 1) u) ^ 2 := by
  have hJ : J h (k + 1) u ≠ 0 := ne_of_gt (J_pos h (k + 1) hu)
  rw [truncatedVar, truncatedMu]
  field_simp
  ring

/-- Exact Gram-plus-transport decomposition from manuscript Theorem 2.2(v). -/
theorem crossing_kernel_succ_gram_decomposition
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 < u) :
    R h (k + 1) u / (2 * I h (k + 2) * J h (k + 1) u) =
      truncatedVar h k u + crossingQ h (k + 1) (truncatedMu h k u) := by
  have hI : I h (k + 2) ≠ 0 := ne_of_gt (h.momentPositive (k + 2))
  have hJ : J h (k + 1) u ≠ 0 := ne_of_gt (J_pos h (k + 1) hu)
  rw [R, K, K, truncatedVar, truncatedMu, crossingQ, crossingA]
  field_simp
  ring

end CrossBoundaryMomentKernels
