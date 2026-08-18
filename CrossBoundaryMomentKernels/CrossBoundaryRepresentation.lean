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

/-- **Positive cross-boundary representation (manuscript Theorem 2.2(i)).**

For every full-support moment weight, every `k ≥ 0`, and every `u > 0`, the determinant
`K_k(u)` is the integral of the positive cross-boundary kernel over `0 < y ≤ u < z`.
The theorem records both the product-measure and iterated-integral forms and proves strict
positivity in the same end-to-end proof.
-/
theorem crossBoundary_representation_and_pos
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    K h k u =
        ∫ p, crossBoundaryIntegrand h k p
          ∂((volume.restrict (Ioc (0 : ℝ) u)).prod (volume.restrict (Ioi u))) ∧
      K h k u =
        ∫ y, ∫ z, crossBoundaryIntegrand h k (y, z)
          ∂(volume.restrict (Ioi u)) ∂(volume.restrict (Ioc (0 : ℝ) u)) ∧
      0 < K h k u := by
  let μL : Measure ℝ := volume.restrict (Ioc (0 : ℝ) u)
  let μR : Measure ℝ := volume.restrict (Ioi u)
  let D : ℝ × ℝ → ℝ := fun p ↦
    momentIntegrand h k p.1 * momentIntegrand h (k + 1) p.2 -
      momentIntegrand h (k + 1) p.1 * momentIntegrand h k p.2

  have hkL : Integrable (momentIntegrand h k) μL := by
    simpa [μL, IntegrableOn] using
      (h.momentIntegrable k).mono_set (by
        intro y hy
        exact hy.1)
  have hk1L : Integrable (momentIntegrand h (k + 1)) μL := by
    simpa [μL, IntegrableOn] using
      (h.momentIntegrable (k + 1)).mono_set (by
        intro y hy
        exact hy.1)
  have hkR : Integrable (momentIntegrand h k) μR := by
    simpa [μR, IntegrableOn] using
      (h.momentIntegrable k).mono_set (by
        intro z hz
        exact lt_trans hu hz)
  have hk1R : Integrable (momentIntegrand h (k + 1)) μR := by
    simpa [μR, IntegrableOn] using
      (h.momentIntegrable (k + 1)).mono_set (by
        intro z hz
        exact lt_trans hu hz)

  have hterm₁ : Integrable
      (fun p : ℝ × ℝ ↦ momentIntegrand h k p.1 * momentIntegrand h (k + 1) p.2)
      (μL.prod μR) :=
    hkL.mul_prod hk1R
  have hterm₂ : Integrable
      (fun p : ℝ × ℝ ↦ momentIntegrand h (k + 1) p.1 * momentIntegrand h k p.2)
      (μL.prod μR) :=
    hk1L.mul_prod hkR
  have hD_integrable : Integrable D (μL.prod μR) := by
    dsimp [D]
    exact hterm₁.sub hterm₂

  have hleft_ae : ∀ᵐ y ∂μL, y ∈ Ioc (0 : ℝ) u := by
    dsimp [μL]
    exact ae_restrict_mem measurableSet_Ioc
  have hright_ae : ∀ᵐ z ∂μR, z ∈ Ioi u := by
    dsimp [μR]
    exact ae_restrict_mem measurableSet_Ioi
  have hrect_ae : ∀ᵐ p ∂(μL.prod μR), p ∈ Ioc (0 : ℝ) u ×ˢ Ioi u := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioc.prod measurableSet_Ioi)).2 ?_
    filter_upwards [hleft_ae] with y hy
    filter_upwards [hright_ae] with z hz
    exact ⟨hy, hz⟩

  have hD_eq_cross : D =ᵐ[μL.prod μR] crossBoundaryIntegrand h k := by
    filter_upwards [hrect_ae] with p hp
    have hy_pos : 0 < p.1 := hp.1.1
    have hz_pos : 0 < p.2 := lt_trans hu hp.2
    have hy_shift := momentIntegrand_succ h k hy_pos
    have hz_shift := momentIntegrand_succ h k hz_pos
    dsimp [D, crossBoundaryIntegrand]
    rw [hy_shift, hz_shift]
    ring

  have hcross_integrable : Integrable (crossBoundaryIntegrand h k) (μL.prod μR) :=
    hD_integrable.congr hD_eq_cross

  have hK_tail :
      K h k u = J h k u * T h (k + 1) u - J h (k + 1) u * T h k u := by
    rw [K, I_eq_J_add_T h (k + 1) hu, I_eq_J_add_T h k hu]
    ring

  have hD_integral :
      (∫ p, D p ∂(μL.prod μR)) =
        J h k u * T h (k + 1) u - J h (k + 1) u * T h k u := by
    dsimp [D]
    rw [integral_sub hterm₁ hterm₂, integral_prod_mul, integral_prod_mul]
    rfl

  have hK_prod : K h k u = ∫ p, crossBoundaryIntegrand h k p ∂(μL.prod μR) := by
    calc
      K h k u = J h k u * T h (k + 1) u - J h (k + 1) u * T h k u := hK_tail
      _ = ∫ p, D p ∂(μL.prod μR) := hD_integral.symm
      _ = ∫ p, crossBoundaryIntegrand h k p ∂(μL.prod μR) :=
        integral_congr_ae hD_eq_cross

  have hK_iter :
      K h k u = ∫ y, ∫ z, crossBoundaryIntegrand h k (y, z) ∂μR ∂μL := by
    calc
      K h k u = ∫ p, crossBoundaryIntegrand h k p ∂(μL.prod μR) := hK_prod
      _ = ∫ y, ∫ z, crossBoundaryIntegrand h k (y, z) ∂μR ∂μL :=
        integral_prod _ hcross_integrable

  have hcross_nonneg : 0 ≤ᵐ[μL.prod μR] crossBoundaryIntegrand h k := by
    filter_upwards [hrect_ae] with p hp
    have hz_pos : 0 < p.2 := lt_trans hu hp.2
    have hyz : p.1 < p.2 := lt_of_le_of_lt hp.1.2 hp.2
    dsimp [crossBoundaryIntegrand]
    exact mul_nonneg
      (mul_nonneg (momentIntegrand_nonneg h k hp.1.1) (momentIntegrand_nonneg h k hz_pos))
      (sub_nonneg.mpr hyz.le)

  have hfull_A :
      0 < ∫ y, h y ∂(volume.restrict (Ioc (u / 4) (u / 2))) :=
    h.fullSupport (by nlinarith) (by nlinarith)
  have hfull_B :
      0 < ∫ z, h z ∂(volume.restrict (Ioc (2 * u) (3 * u))) :=
    h.fullSupport (by nlinarith) (by nlinarith)

  have hh_int_A : IntegrableOn (h : ℝ → ℝ) (Ioc (u / 4) (u / 2)) := by
    by_contra hnot
    have hzero : ∫ y, h y ∂(volume.restrict (Ioc (u / 4) (u / 2))) = 0 :=
      integral_undef hnot
    linarith
  have hh_int_B : IntegrableOn (h : ℝ → ℝ) (Ioc (2 * u) (3 * u)) := by
    by_contra hnot
    have hzero : ∫ z, h z ∂(volume.restrict (Ioc (2 * u) (3 * u))) = 0 :=
      integral_undef hnot
    linarith

  have hh_nonneg_A : 0 ≤ᵐ[volume.restrict (Ioc (u / 4) (u / 2))] (h : ℝ → ℝ) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with y hy
    exact h.nonneg (by nlinarith [hy.1])
  have hh_nonneg_B : 0 ≤ᵐ[volume.restrict (Ioc (2 * u) (3 * u))] (h : ℝ → ℝ) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with z hz
    exact h.nonneg (by nlinarith [hz.1])

  have hsupp_A_vol :
      0 < volume (Function.support (h : ℝ → ℝ) ∩ Ioc (u / 4) (u / 2)) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hh_nonneg_A hh_int_A).mp hfull_A
  have hsupp_B_vol :
      0 < volume (Function.support (h : ℝ → ℝ) ∩ Ioc (2 * u) (3 * u)) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hh_nonneg_B hh_int_B).mp hfull_B

  let A : Set ℝ := Function.support (h : ℝ → ℝ) ∩ Ioc (u / 4) (u / 2)
  let B : Set ℝ := Function.support (h : ℝ → ℝ) ∩ Ioc (2 * u) (3 * u)

  have hμLA : 0 < μL A := by
    dsimp [μL, A]
    rw [Measure.restrict_apply' measurableSet_Ioc]
    have hsub :
        Function.support (h : ℝ → ℝ) ∩ Ioc (u / 4) (u / 2) ⊆ Ioc (0 : ℝ) u := by
      intro y hy
      constructor <;> nlinarith [hy.2.1, hy.2.2]
    rw [inter_eq_left.2 hsub]
    exact hsupp_A_vol
  have hμRB : 0 < μR B := by
    dsimp [μR, B]
    rw [Measure.restrict_apply' measurableSet_Ioi]
    have hsub : Function.support (h : ℝ → ℝ) ∩ Ioc (2 * u) (3 * u) ⊆ Ioi u := by
      intro z hz
      exact show u < z by nlinarith [hz.2.1]
    rw [inter_eq_left.2 hsub]
    exact hsupp_B_vol

  have hrect_pos : 0 < (μL.prod μR) (A ×ˢ B) := by
    rw [Measure.prod_prod, CanonicallyOrderedAdd.mul_pos]
    exact ⟨hμLA, hμRB⟩

  have hrect_support : A ×ˢ B ⊆ Function.support (crossBoundaryIntegrand h k) := by
    intro p hp
    rcases hp with ⟨hyA, hzB⟩
    change p.1 ∈ Function.support (h : ℝ → ℝ) ∩ Ioc (u / 4) (u / 2) at hyA
    change p.2 ∈ Function.support (h : ℝ → ℝ) ∩ Ioc (2 * u) (3 * u) at hzB
    have hy_pos : 0 < p.1 := by nlinarith [hyA.2.1]
    have hz_pos : 0 < p.2 := by nlinarith [hzB.2.1]
    have hyz : p.1 < p.2 := by nlinarith [hyA.2.2, hzB.2.1]
    have hfy_pos := momentIntegrand_pos_of_mem_support h k hy_pos hyA.1
    have hfz_pos := momentIntegrand_pos_of_mem_support h k hz_pos hzB.1
    have hgap_pos : 0 < p.2 - p.1 := sub_pos.mpr hyz
    show crossBoundaryIntegrand h k p ≠ 0
    dsimp [crossBoundaryIntegrand]
    exact ne_of_gt (mul_pos (mul_pos hfy_pos hfz_pos) hgap_pos)

  have hcross_support_pos :
      0 < (μL.prod μR) (Function.support (crossBoundaryIntegrand h k)) :=
    lt_of_lt_of_le hrect_pos (measure_mono hrect_support)

  have hcross_pos : 0 < ∫ p, crossBoundaryIntegrand h k p ∂(μL.prod μR) :=
    (integral_pos_iff_support_of_nonneg_ae hcross_nonneg hcross_integrable).2 hcross_support_pos

  have hK_pos : 0 < K h k u := by
    rw [hK_prod]
    exact hcross_pos

  simpa [μL, μR] using And.intro hK_prod (And.intro hK_iter hK_pos)

/-- Manuscript-facing product-measure form of Theorem 2.2(i). -/
theorem K_eq_crossBoundaryIntegral
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    K h k u =
      ∫ p, crossBoundaryIntegrand h k p
        ∂((volume.restrict (Ioc (0 : ℝ) u)).prod (volume.restrict (Ioi u))) :=
  (crossBoundary_representation_and_pos h k hu).1

/-- Strict positivity conclusion of manuscript Theorem 2.2(i). -/
theorem K_pos (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    0 < K h k u :=
  (crossBoundary_representation_and_pos h k hu).2.2

end CrossBoundaryMomentKernels
