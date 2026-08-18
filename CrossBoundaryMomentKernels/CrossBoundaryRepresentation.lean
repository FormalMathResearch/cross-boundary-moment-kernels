import CrossBoundaryMomentKernels.MomentLogConvexity

noncomputable section

open MeasureTheory Set

namespace CrossBoundaryMomentKernels

/-- The tail moment `T_j(u) = I_j - J_j(u)` from the manuscript proof of Theorem 2.2(i). -/
def T (h : ℝ → ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  ∫ y, momentIntegrand h j y ∂(volume.restrict (Ioi u))

/-- Factorized cross-boundary integrand. On `0 < y < u < z` this is exactly
`(yz)^(k-1/2) (z-y) h(y) h(z)` from Theorem 2.2(i). -/
def crossBoundaryIntegrand (h : ℝ → ℝ) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  momentIntegrand h k p.1 * momentIntegrand h k p.2 * (p.2 - p.1)

/-- Splitting the positive half-line at `u` gives `I_j = J_j(u) + T_j(u)`. -/
lemma I_eq_J_add_T (h : FullSupportMomentWeight) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    I h j = J h j u + T h j u := by
  have hleft_int : IntegrableOn (momentIntegrand h j) (Ioc (0 : ℝ) u) :=
    (h.momentIntegrable j).mono_set (by
      intro y hy
      exact hy.1)
  have hright_int : IntegrableOn (momentIntegrand h j) (Ioi u) :=
    (h.momentIntegrable j).mono_set (by
      intro y hy
      exact lt_trans hu hy)
  have hdisj : Disjoint (Ioc (0 : ℝ) u) (Ioi u) := by
    refine disjoint_left.2 ?_
    intro y hy_left hy_right
    exact (not_lt_of_ge hy_left.2) hy_right
  have hunion : Ioc (0 : ℝ) u ∪ Ioi u = Ioi (0 : ℝ) := by
    ext y
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (hy | hy)
      · exact hy.1
      · exact lt_trans hu hy
    · intro hy
      rcases le_or_gt y u with hyu | huy
      · exact Or.inl ⟨hy, hyu⟩
      · exact Or.inr huy
  have hsplit := setIntegral_union hdisj measurableSet_Ioi hleft_int hright_int
  rw [hunion] at hsplit
  simpa [I, J, T] using hsplit

end CrossBoundaryMomentKernels
