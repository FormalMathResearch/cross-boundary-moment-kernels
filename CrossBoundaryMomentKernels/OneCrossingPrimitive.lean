import CrossBoundaryMomentKernels.OneCrossingAnalysis

noncomputable section

open MeasureTheory Set

namespace CrossBoundaryMomentKernels

/-- The crossing kernel is the lower primitive of the linear derivative normal form. -/
lemma R_eq_setIntegral_rLinearIntegrand
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    R h k u =
      ∫ x, rLinearIntegrand h k x ∂(volume.restrict (Ioc (0 : ℝ) u)) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) u)
  have hk : Integrable (momentIntegrand h k) μ := by
    simpa [μ, IntegrableOn] using
      (h.momentIntegrable k).mono_set (by
        intro x hx
        exact hx.1)
  have hk₁ : Integrable (momentIntegrand h (k + 1)) μ := by
    simpa [μ, IntegrableOn] using
      (h.momentIntegrable (k + 1)).mono_set (by
        intro x hx
        exact hx.1)
  have hk₂ : Integrable (momentIntegrand h (k + 2)) μ := by
    simpa [μ, IntegrableOn] using
      (h.momentIntegrable (k + 2)).mono_set (by
        intro x hx
        exact hx.1)
  have ht₀ : Integrable
      (fun x ↦ tau h k * I h (k + 1) * momentIntegrand h k x) μ :=
    hk.const_mul _
  have ht₁ : Integrable
      (fun x ↦ I h (k + 1) * momentIntegrand h (k + 2) x) μ :=
    hk₂.const_mul _
  have ht₂ : Integrable
      (fun x ↦ (tau h k * I h k + I h (k + 2)) * momentIntegrand h (k + 1) x) μ :=
    hk₁.const_mul _
  have hIntegral :
      (∫ x, rLinearIntegrand h k x ∂μ) =
        2 *
          (tau h k * I h (k + 1) * J h k u +
            I h (k + 1) * J h (k + 2) u -
            (tau h k * I h k + I h (k + 2)) * J h (k + 1) u) := by
    change
      (∫ x,
        2 *
          (tau h k * I h (k + 1) * momentIntegrand h k x +
            I h (k + 1) * momentIntegrand h (k + 2) x -
            (tau h k * I h k + I h (k + 2)) * momentIntegrand h (k + 1) x) ∂μ) = _
    rw [integral_const_mul,
      integral_sub (ht₀.add ht₁) ht₂, integral_add ht₀ ht₁]
    simp only [integral_const_mul]
    simp [J, μ]
  have hAlgebra :
      R h k u =
        2 *
          (tau h k * I h (k + 1) * J h k u +
            I h (k + 1) * J h (k + 2) u -
            (tau h k * I h k + I h (k + 2)) * J h (k + 1) u) := by
    simp [R, K, Nat.add_assoc]
    ring
  simpa [μ] using hAlgebra.trans hIntegral.symm

/-- **Integrated derivative identity.** For `u > 0`, `R_k(u)` is exactly the integral of
`2 I_{k+1} x^(k-1/2) h(x) Q_k(x)` from `0` to `u`. -/
theorem R_eq_setIntegral_rDerivativeIntegrand
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    R h k u =
      ∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioc (0 : ℝ) u)) := by
  calc
    R h k u =
        ∫ x, rLinearIntegrand h k x ∂(volume.restrict (Ioc (0 : ℝ) u)) :=
      R_eq_setIntegral_rLinearIntegrand h k hu
    _ = ∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioc (0 : ℝ) u)) := by
      apply integral_congr_ae
      have hmem : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) u)), x ∈ Ioc (0 : ℝ) u :=
        ae_restrict_mem measurableSet_Ioc
      filter_upwards [hmem] with x hx
      exact rLinearIntegrand_eq_rDerivativeIntegrand h k hx.1

/-- The derivative density has total integral zero on the positive half-line. -/
lemma integral_rDerivativeIntegrand_Ioi_eq_zero
    (h : FullSupportMomentWeight) (k : ℕ) :
    ∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioi (0 : ℝ))) = 0 := by
  have hk : Integrable (momentIntegrand h k) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using h.momentIntegrable k
  have hk₁ : Integrable (momentIntegrand h (k + 1)) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using h.momentIntegrable (k + 1)
  have hk₂ : Integrable (momentIntegrand h (k + 2)) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using h.momentIntegrable (k + 2)
  have ht₀ : Integrable
      (fun x ↦ tau h k * I h (k + 1) * momentIntegrand h k x)
      (volume.restrict (Ioi (0 : ℝ))) :=
    hk.const_mul _
  have ht₁ : Integrable
      (fun x ↦ I h (k + 1) * momentIntegrand h (k + 2) x)
      (volume.restrict (Ioi (0 : ℝ))) :=
    hk₂.const_mul _
  have ht₂ : Integrable
      (fun x ↦ (tau h k * I h k + I h (k + 2)) * momentIntegrand h (k + 1) x)
      (volume.restrict (Ioi (0 : ℝ))) :=
    hk₁.const_mul _
  have hlinear :
      ∫ x, rLinearIntegrand h k x ∂(volume.restrict (Ioi (0 : ℝ))) = 0 := by
    change
      (∫ x,
        2 *
          (tau h k * I h (k + 1) * momentIntegrand h k x +
            I h (k + 1) * momentIntegrand h (k + 2) x -
            (tau h k * I h k + I h (k + 2)) * momentIntegrand h (k + 1) x)
          ∂(volume.restrict (Ioi (0 : ℝ)))) = 0
    rw [integral_const_mul,
      integral_sub (ht₀.add ht₁) ht₂, integral_add ht₀ ht₁]
    simp only [integral_const_mul]
    simp [I]
    ring
  calc
    ∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioi (0 : ℝ))) =
        ∫ x, rLinearIntegrand h k x ∂(volume.restrict (Ioi (0 : ℝ))) := by
      apply integral_congr_ae
      have hmem : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), 0 < x :=
        ae_restrict_mem measurableSet_Ioi
      filter_upwards [hmem] with x hx
      exact (rLinearIntegrand_eq_rDerivativeIntegrand h k hx).symm
    _ = 0 := hlinear

/-- The derivative density is integrable on every measurable subset of the positive half-line. -/
lemma rDerivativeIntegrand_integrableOn_mono_Ioi
    (h : FullSupportMomentWeight) (k : ℕ) {s : Set ℝ}
    (hs : s ⊆ Ioi (0 : ℝ)) :
    IntegrableOn (rDerivativeIntegrand h k) s := by
  have hglobal : IntegrableOn (rDerivativeIntegrand h k) (Ioi (0 : ℝ)) := by
    simpa [IntegrableOn] using rDerivativeIntegrand_integrable h k
  exact hglobal.mono_set hs

/-- **Integrated derivative difference law.** This is the form used to make all three
monotonicity intervals strict under the manuscript full-support hypothesis. -/
theorem R_sub_R_eq_setIntegral_rDerivativeIntegrand
    (h : FullSupportMomentWeight) (k : ℕ) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    R h k v - R h k u =
      ∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioc u v)) := by
  have hleft : IntegrableOn (rDerivativeIntegrand h k) (Ioc (0 : ℝ) u) :=
    rDerivativeIntegrand_integrableOn_mono_Ioi h k (by
      intro x hx
      exact hx.1)
  have hmid : IntegrableOn (rDerivativeIntegrand h k) (Ioc u v) :=
    rDerivativeIntegrand_integrableOn_mono_Ioi h k (by
      intro x hx
      exact lt_trans hu hx.1)
  have hdisj : Disjoint (Ioc (0 : ℝ) u) (Ioc u v) := by
    refine disjoint_left.2 ?_
    intro x hx₁ hx₂
    exact (not_lt_of_ge hx₁.2) hx₂.1
  have hunion : Ioc (0 : ℝ) u ∪ Ioc u v = Ioc (0 : ℝ) v := by
    ext x
    simp only [mem_union, mem_Ioc]
    constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, hx.2.trans huv.le⟩
      · exact ⟨lt_trans hu hx.1, hx.2⟩
    · intro hx
      rcases le_or_gt x u with hxu | hux
      · exact Or.inl ⟨hx.1, hxu⟩
      · exact Or.inr ⟨hux, hx.2⟩
  have hsplit := setIntegral_union hdisj measurableSet_Ioc hleft hmid
  rw [hunion] at hsplit
  rw [R_eq_setIntegral_rDerivativeIntegrand h k (lt_trans hu huv),
    R_eq_setIntegral_rDerivativeIntegrand h k hu, hsplit]
  ring

/-- Exact upper-tail form of the crossing kernel. It is the integral counterpart of the
manuscript endpoint limit `R_k(u) → 0` as `u → ∞`. -/
theorem R_eq_neg_tailIntegral_rDerivativeIntegrand
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    R h k u =
      - ∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioi u)) := by
  have hleft : IntegrableOn (rDerivativeIntegrand h k) (Ioc (0 : ℝ) u) :=
    rDerivativeIntegrand_integrableOn_mono_Ioi h k (by
      intro x hx
      exact hx.1)
  have hright : IntegrableOn (rDerivativeIntegrand h k) (Ioi u) :=
    rDerivativeIntegrand_integrableOn_mono_Ioi h k (by
      intro x hx
      exact lt_trans hu hx)
  have hdisj : Disjoint (Ioc (0 : ℝ) u) (Ioi u) := by
    refine disjoint_left.2 ?_
    intro x hx₁ hx₂
    exact (not_lt_of_ge hx₁.2) hx₂
  have hunion : Ioc (0 : ℝ) u ∪ Ioi u = Ioi (0 : ℝ) := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact lt_trans hu hx
    · intro hx
      rcases le_or_gt x u with hxu | hux
      · exact Or.inl ⟨hx, hxu⟩
      · exact Or.inr hux
  have hsplit := setIntegral_union hdisj measurableSet_Ioi hleft hright
  rw [hunion] at hsplit
  have htotal := integral_rDerivativeIntegrand_Ioi_eq_zero h k
  have hR := R_eq_setIntegral_rDerivativeIntegrand h k hu
  linarith

end CrossBoundaryMomentKernels
