import CrossBoundaryMomentKernels.OneCrossingPrimitive

noncomputable section

open MeasureTheory Set

namespace CrossBoundaryMomentKernels

/-- Full support transfers strict positivity from the weight to any nonnegative integrable
integrand that is strictly positive wherever the weight is nonzero. -/
lemma setIntegral_pos_of_fullSupport
    (h : FullSupportMomentWeight) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {f : ℝ → ℝ} (hfint : IntegrableOn f (Ioc a b))
    (hfnonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] f)
    (hfpos : ∀ x ∈ Function.support (h : ℝ → ℝ) ∩ Ioc a b, 0 < f x) :
    0 < ∫ x, f x ∂(volume.restrict (Ioc a b)) := by
  have hfull : 0 < ∫ x, h x ∂(volume.restrict (Ioc a b)) := h.fullSupport ha hab
  have hh_int : IntegrableOn (h : ℝ → ℝ) (Ioc a b) := by
    by_contra hnot
    have hzero : ∫ x, h x ∂(volume.restrict (Ioc a b)) = 0 := integral_undef hnot
    linarith
  have hh_nonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] (h : ℝ → ℝ) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    exact h.nonneg (lt_trans ha hx.1)
  have hsupp_h :
      0 < volume (Function.support (h : ℝ → ℝ) ∩ Ioc a b) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hh_nonneg hh_int).mp hfull
  have hsupp_f : 0 < volume (Function.support f ∩ Ioc a b) := by
    refine lt_of_lt_of_le hsupp_h (measure_mono ?_)
    intro x hx
    exact ⟨ne_of_gt (hfpos x hx), hx.2⟩
  exact (setIntegral_pos_iff_support_of_nonneg_ae hfnonneg hfint).2 hsupp_f

/-- The manuscript derivative density is pointwise nonnegative to the left of the smaller root. -/
lemma rDerivativeIntegrand_nonneg_left
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx₀ : 0 < x) (hx : x ≤ xiMinus h k) :
    0 ≤ rDerivativeIntegrand h k x := by
  have hQ : 0 ≤ crossingQ h k x := by
    rw [crossingQ_factor h hk]
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx)
      (sub_nonpos.mpr (hx.trans (xiMinus_lt_xiPlus h hk).le))
  rw [rDerivativeIntegrand]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (h.momentPositive (k + 1)).le)
      (momentIntegrand_nonneg h k hx₀)) hQ

/-- On the support of the weight the derivative density is strictly positive left of `ξ₋`. -/
lemma rDerivativeIntegrand_pos_left
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx₀ : 0 < x) (hx : x < xiMinus h k)
    (hsupp : x ∈ Function.support (h : ℝ → ℝ)) :
    0 < rDerivativeIntegrand h k x := by
  rw [rDerivativeIntegrand]
  exact mul_pos
    (mul_pos (mul_pos (by norm_num) (h.momentPositive (k + 1)))
      (momentIntegrand_pos_of_mem_support h k hx₀ hsupp))
    (crossingQ_pos_of_lt_xiMinus h hk hx)

/-- The manuscript derivative density is pointwise nonpositive between the two roots. -/
lemma rDerivativeIntegrand_nonpos_middle
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx₁ : xiMinus h k ≤ x) (hx₂ : x ≤ xiPlus h k) :
    rDerivativeIntegrand h k x ≤ 0 := by
  have hQ : crossingQ h k x ≤ 0 := by
    rw [crossingQ_factor h hk]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx₁) (sub_nonpos.mpr hx₂)
  have hx₀ : 0 < x := lt_of_lt_of_le (xiMinus_pos h hk) hx₁
  rw [rDerivativeIntegrand]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (by norm_num) (h.momentPositive (k + 1)).le)
      (momentIntegrand_nonneg h k hx₀)) hQ

/-- On the support of the weight the derivative density is strictly negative between the roots. -/
lemma rDerivativeIntegrand_neg_middle
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx₁ : xiMinus h k < x) (hx₂ : x < xiPlus h k)
    (hsupp : x ∈ Function.support (h : ℝ → ℝ)) :
    rDerivativeIntegrand h k x < 0 := by
  have hx₀ : 0 < x := lt_trans (xiMinus_pos h hk) hx₁
  rw [rDerivativeIntegrand]
  exact mul_neg_of_pos_of_neg
    (mul_pos (mul_pos (by norm_num) (h.momentPositive (k + 1)))
      (momentIntegrand_pos_of_mem_support h k hx₀ hsupp))
    (crossingQ_neg_between h hk hx₁ hx₂)

/-- The manuscript derivative density is pointwise nonnegative to the right of the larger root. -/
lemma rDerivativeIntegrand_nonneg_right
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : xiPlus h k ≤ x) :
    0 ≤ rDerivativeIntegrand h k x := by
  have hx₀ : 0 < x := lt_of_lt_of_le (xiPlus_pos h hk) hx
  have hQ : 0 ≤ crossingQ h k x := by
    rw [crossingQ_factor h hk]
    exact mul_nonneg (sub_nonneg.mpr ((xiMinus_lt_xiPlus h hk).le.trans hx))
      (sub_nonneg.mpr hx)
  rw [rDerivativeIntegrand]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (h.momentPositive (k + 1)).le)
      (momentIntegrand_nonneg h k hx₀)) hQ

/-- On the support of the weight the derivative density is strictly positive right of `ξ₊`. -/
lemma rDerivativeIntegrand_pos_right
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : xiPlus h k < x) (hsupp : x ∈ Function.support (h : ℝ → ℝ)) :
    0 < rDerivativeIntegrand h k x := by
  have hx₀ : 0 < x := lt_trans (xiPlus_pos h hk) hx
  rw [rDerivativeIntegrand]
  exact mul_pos
    (mul_pos (mul_pos (by norm_num) (h.momentPositive (k + 1)))
      (momentIntegrand_pos_of_mem_support h k hx₀ hsupp))
    (crossingQ_pos_of_xiPlus_lt h hk hx)

/-- Every nonempty interval strictly left of `ξ₋` has positive derivative integral. -/
lemma setIntegral_rDerivativeIntegrand_pos_left
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < xiMinus h k) :
    0 < ∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioc a b)) := by
  have hfint : IntegrableOn (rDerivativeIntegrand h k) (Ioc a b) :=
    rDerivativeIntegrand_integrableOn_mono_Ioi h k (by
      intro x hx
      exact lt_trans ha hx.1)
  have hfnonneg :
      0 ≤ᵐ[volume.restrict (Ioc a b)] rDerivativeIntegrand h k := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    exact rDerivativeIntegrand_nonneg_left h hk (lt_trans ha hx.1)
      (hx.2.trans (le_of_lt hb))
  apply setIntegral_pos_of_fullSupport h ha hab hfint hfnonneg
  intro x hx
  exact rDerivativeIntegrand_pos_left h hk (lt_trans ha hx.2.1)
    (lt_of_le_of_lt hx.2.2 hb) hx.1

/-- Every nonempty interval strictly between the two roots has negative derivative integral. -/
lemma setIntegral_rDerivativeIntegrand_neg_middle
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {a b : ℝ}
    (ha : xiMinus h k < a) (hab : a < b) (hb : b < xiPlus h k) :
    ∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioc a b)) < 0 := by
  have hfint : IntegrableOn (rDerivativeIntegrand h k) (Ioc a b) :=
    rDerivativeIntegrand_integrableOn_mono_Ioi h k (by
      intro x hx
      exact lt_trans (xiMinus_pos h hk) (lt_trans ha hx.1))
  have hnegint : IntegrableOn (fun x ↦ -rDerivativeIntegrand h k x) (Ioc a b) :=
    hfint.neg
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioc a b)] (fun x ↦ -rDerivativeIntegrand h k x) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    exact neg_nonneg.mpr (rDerivativeIntegrand_nonpos_middle h hk
      (le_of_lt (lt_trans ha hx.1)) (hx.2.trans (le_of_lt hb)))
  have hpos :
      0 < ∫ x, -rDerivativeIntegrand h k x ∂(volume.restrict (Ioc a b)) := by
    apply setIntegral_pos_of_fullSupport h (lt_trans (xiMinus_pos h hk) ha) hab hnegint hnonneg
    intro x hx
    exact neg_pos.mpr (rDerivativeIntegrand_neg_middle h hk
      (lt_trans ha hx.2.1) (lt_of_le_of_lt hx.2.2 hb) hx.1)
  rw [integral_neg] at hpos
  linarith

/-- Every nonempty interval strictly right of `ξ₊` has positive derivative integral. -/
lemma setIntegral_rDerivativeIntegrand_pos_right
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {a b : ℝ}
    (ha : xiPlus h k < a) (hab : a < b) :
    0 < ∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioc a b)) := by
  have ha₀ : 0 < a := lt_trans (xiPlus_pos h hk) ha
  have hfint : IntegrableOn (rDerivativeIntegrand h k) (Ioc a b) :=
    rDerivativeIntegrand_integrableOn_mono_Ioi h k (by
      intro x hx
      exact lt_trans ha₀ hx.1)
  have hfnonneg :
      0 ≤ᵐ[volume.restrict (Ioc a b)] rDerivativeIntegrand h k := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    exact rDerivativeIntegrand_nonneg_right h hk
      (le_of_lt (lt_trans ha hx.1))
  apply setIntegral_pos_of_fullSupport h ha₀ hab hfint hfnonneg
  intro x hx
  exact rDerivativeIntegrand_pos_right h hk (lt_trans ha hx.2.1) hx.1

/-- `R_k` is strictly increasing on the first quadratic-sign interval. -/
lemma R_strictMonoOn_left
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    StrictMonoOn (R h k) (Ioo (0 : ℝ) (xiMinus h k)) := by
  intro a ha b hb hab
  have hdiff := R_sub_R_eq_setIntegral_rDerivativeIntegrand h k ha.1 hab
  have hpos := setIntegral_rDerivativeIntegrand_pos_left h hk ha.1 hab hb.2
  linarith

/-- `R_k` is strictly decreasing between the two roots of `Q_k`. -/
lemma R_strictAntiOn_middle
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    StrictAntiOn (R h k) (Ioo (xiMinus h k) (xiPlus h k)) := by
  intro a ha b hb hab
  have hdiff := R_sub_R_eq_setIntegral_rDerivativeIntegrand h k
    (lt_trans (xiMinus_pos h hk) ha.1) hab
  have hneg := setIntegral_rDerivativeIntegrand_neg_middle h hk ha.1 hab hb.2
  linarith

/-- `R_k` is strictly increasing to the right of the larger root. -/
lemma R_strictMonoOn_right
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    StrictMonoOn (R h k) (Ioi (xiPlus h k)) := by
  intro a ha b hb hab
  have hdiff := R_sub_R_eq_setIntegral_rDerivativeIntegrand h k
    (lt_trans (xiPlus_pos h hk) ha) hab
  have hpos := setIntegral_rDerivativeIntegrand_pos_right h hk ha hab
  linarith

end CrossBoundaryMomentKernels
