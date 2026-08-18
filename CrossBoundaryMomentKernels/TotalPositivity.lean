import CrossBoundaryMomentKernels.OneCrossingManuscriptForm

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- Linear integrable normal form of the manuscript derivative of `Z_k`. -/
def zLinearIntegrand (h : ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (N h k)⁻¹ *
    (I h (k + 1) * momentIntegrand h k x - I h k * momentIntegrand h (k + 1) x)

/-- Manuscript derivative density
`(I_k / N_k) x^(k-1/2) h(x) (γ_k - x)` for the normalized determinant `Z_k`. -/
def zDerivativeIntegrand (h : ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (I h k / N h k) * momentIntegrand h k x * (gamma h k - x)

/-- On the positive half-line the linear normal form is exactly the manuscript derivative density. -/
lemma zLinearIntegrand_eq_zDerivativeIntegrand
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 < x) :
    zLinearIntegrand h k x = zDerivativeIntegrand h k x := by
  have hIk : I h k ≠ 0 := ne_of_gt (h.momentPositive k)
  have hNk : N h k ≠ 0 := ne_of_gt (N_pos h hk)
  rw [zLinearIntegrand, zDerivativeIntegrand, gamma, momentIntegrand_succ h k hx]
  field_simp

/-- The linear derivative normal form is globally integrable on the positive half-line. -/
lemma zLinearIntegrand_integrable
    (h : FullSupportMomentWeight) (k : ℕ) :
    Integrable (zLinearIntegrand h k) (volume.restrict (Ioi (0 : ℝ))) := by
  have hk : Integrable (momentIntegrand h k) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using h.momentIntegrable k
  have hk₁ : Integrable (momentIntegrand h (k + 1)) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using h.momentIntegrable (k + 1)
  have ht₀ : Integrable
      (fun x ↦ I h (k + 1) * momentIntegrand h k x)
      (volume.restrict (Ioi (0 : ℝ))) :=
    hk.const_mul _
  have ht₁ : Integrable
      (fun x ↦ I h k * momentIntegrand h (k + 1) x)
      (volume.restrict (Ioi (0 : ℝ))) :=
    hk₁.const_mul _
  change Integrable
    (fun x ↦ (N h k)⁻¹ *
      (I h (k + 1) * momentIntegrand h k x - I h k * momentIntegrand h (k + 1) x))
    (volume.restrict (Ioi (0 : ℝ)))
  exact (ht₀.sub ht₁).const_mul _

/-- The manuscript derivative density is integrable on the positive half-line. -/
lemma zDerivativeIntegrand_integrable
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (zDerivativeIntegrand h k) (volume.restrict (Ioi (0 : ℝ))) := by
  exact (zLinearIntegrand_integrable h k).congr (by
    have hmem : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), 0 < x :=
      ae_restrict_mem measurableSet_Ioi
    filter_upwards [hmem] with x hx
    exact zLinearIntegrand_eq_zDerivativeIntegrand h hk hx)

/-- `Z_k` is the lower primitive of the linear derivative normal form. -/
lemma Z_eq_setIntegral_zLinearIntegrand
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (_hu : 0 < u) :
    Z h k u = ∫ x, zLinearIntegrand h k x ∂(volume.restrict (Ioc (0 : ℝ) u)) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) u)
  have hkInt : Integrable (momentIntegrand h k) μ := by
    simpa [μ, IntegrableOn] using
      (h.momentIntegrable k).mono_set (by intro x hx; exact hx.1)
  have hk₁Int : Integrable (momentIntegrand h (k + 1)) μ := by
    simpa [μ, IntegrableOn] using
      (h.momentIntegrable (k + 1)).mono_set (by intro x hx; exact hx.1)
  have ht₀ : Integrable (fun x ↦ I h (k + 1) * momentIntegrand h k x) μ :=
    hkInt.const_mul _
  have ht₁ : Integrable (fun x ↦ I h k * momentIntegrand h (k + 1) x) μ :=
    hk₁Int.const_mul _
  have hIntegral :
      (∫ x, zLinearIntegrand h k x ∂μ) =
        (N h k)⁻¹ * (I h (k + 1) * J h k u - I h k * J h (k + 1) u) := by
    change
      (∫ x, (N h k)⁻¹ *
        (I h (k + 1) * momentIntegrand h k x - I h k * momentIntegrand h (k + 1) x) ∂μ) = _
    rw [integral_const_mul, integral_sub ht₀ ht₁]
    simp only [integral_const_mul]
    simp [J, μ]
  have hNk : N h k ≠ 0 := ne_of_gt (N_pos h hk)
  rw [Z, K]
  simpa [μ, div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using hIntegral.symm

/-- Exact lower-primitive identity for the manuscript derivative density of `Z_k`. -/
theorem Z_eq_setIntegral_zDerivativeIntegrand
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 < u) :
    Z h k u = ∫ x, zDerivativeIntegrand h k x ∂(volume.restrict (Ioc (0 : ℝ) u)) := by
  calc
    Z h k u = ∫ x, zLinearIntegrand h k x ∂(volume.restrict (Ioc (0 : ℝ) u)) :=
      Z_eq_setIntegral_zLinearIntegrand h hk hu
    _ = ∫ x, zDerivativeIntegrand h k x ∂(volume.restrict (Ioc (0 : ℝ) u)) := by
      apply integral_congr_ae
      have hmem : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) u)), x ∈ Ioc (0 : ℝ) u :=
        ae_restrict_mem measurableSet_Ioc
      filter_upwards [hmem] with x hx
      exact zLinearIntegrand_eq_zDerivativeIntegrand h hk hx.1

/-- The derivative density of `Z_k` has total integral zero on `(0,∞)`. -/
lemma integral_zDerivativeIntegrand_Ioi_eq_zero
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    ∫ x, zDerivativeIntegrand h k x ∂(volume.restrict (Ioi (0 : ℝ))) = 0 := by
  have hkInt : Integrable (momentIntegrand h k) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using h.momentIntegrable k
  have hk₁Int : Integrable (momentIntegrand h (k + 1)) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using h.momentIntegrable (k + 1)
  have ht₀ : Integrable
      (fun x ↦ I h (k + 1) * momentIntegrand h k x)
      (volume.restrict (Ioi (0 : ℝ))) := hkInt.const_mul _
  have ht₁ : Integrable
      (fun x ↦ I h k * momentIntegrand h (k + 1) x)
      (volume.restrict (Ioi (0 : ℝ))) := hk₁Int.const_mul _
  have hlinear :
      ∫ x, zLinearIntegrand h k x ∂(volume.restrict (Ioi (0 : ℝ))) = 0 := by
    change
      (∫ x, (N h k)⁻¹ *
        (I h (k + 1) * momentIntegrand h k x - I h k * momentIntegrand h (k + 1) x)
        ∂(volume.restrict (Ioi (0 : ℝ)))) = 0
    rw [integral_const_mul, integral_sub ht₀ ht₁]
    simp only [integral_const_mul]
    change (N h k)⁻¹ * (I h (k + 1) * I h k - I h k * I h (k + 1)) = 0
    ring
  calc
    ∫ x, zDerivativeIntegrand h k x ∂(volume.restrict (Ioi (0 : ℝ))) =
        ∫ x, zLinearIntegrand h k x ∂(volume.restrict (Ioi (0 : ℝ))) := by
      apply integral_congr_ae
      have hmem : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), 0 < x :=
        ae_restrict_mem measurableSet_Ioi
      filter_upwards [hmem] with x hx
      exact (zLinearIntegrand_eq_zDerivativeIntegrand h hk hx).symm
    _ = 0 := hlinear

/-- The derivative density is integrable on every measurable subset of the positive half-line. -/
lemma zDerivativeIntegrand_integrableOn_mono_Ioi
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {s : Set ℝ}
    (hs : s ⊆ Ioi (0 : ℝ)) :
    IntegrableOn (zDerivativeIntegrand h k) s := by
  have hglobal : IntegrableOn (zDerivativeIntegrand h k) (Ioi (0 : ℝ)) := by
    simpa [IntegrableOn] using zDerivativeIntegrand_integrable h hk
  exact hglobal.mono_set hs

/-- Exact difference law for the normalized determinant. -/
theorem Z_sub_Z_eq_setIntegral_zDerivativeIntegrand
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    Z h k v - Z h k u =
      ∫ x, zDerivativeIntegrand h k x ∂(volume.restrict (Ioc u v)) := by
  have hleft : IntegrableOn (zDerivativeIntegrand h k) (Ioc (0 : ℝ) u) :=
    zDerivativeIntegrand_integrableOn_mono_Ioi h hk (by intro x hx; exact hx.1)
  have hmid : IntegrableOn (zDerivativeIntegrand h k) (Ioc u v) :=
    zDerivativeIntegrand_integrableOn_mono_Ioi h hk (by
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
  rw [Z_eq_setIntegral_zDerivativeIntegrand h hk (lt_trans hu huv),
    Z_eq_setIntegral_zDerivativeIntegrand h hk hu, hsplit]
  ring

/-- Exact upper-tail form of `Z_k`, replacing the manuscript endpoint limit by an identity. -/
theorem Z_eq_neg_tailIntegral_zDerivativeIntegrand
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 < u) :
    Z h k u = - ∫ x, zDerivativeIntegrand h k x ∂(volume.restrict (Ioi u)) := by
  have hleft : IntegrableOn (zDerivativeIntegrand h k) (Ioc (0 : ℝ) u) :=
    zDerivativeIntegrand_integrableOn_mono_Ioi h hk (by intro x hx; exact hx.1)
  have hright : IntegrableOn (zDerivativeIntegrand h k) (Ioi u) :=
    zDerivativeIntegrand_integrableOn_mono_Ioi h hk (by intro x hx; exact lt_trans hu hx)
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
  have htotal := integral_zDerivativeIntegrand_Ioi_eq_zero h hk
  have hZ := Z_eq_setIntegral_zDerivativeIntegrand h hk hu
  linarith

/-- Positivity of the normalized determinant at every manuscript point. -/
lemma Z_pos
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 < u) :
    0 < Z h k u := by
  rw [Z]
  exact div_pos (K_pos h k hu) (N_pos h hk)

end CrossBoundaryMomentKernels
