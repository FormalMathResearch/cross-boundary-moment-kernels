import CrossBoundaryMomentKernels.OneCrossingRegularity

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- The crossing kernel is strictly positive up to and including the smaller quadratic root. -/
lemma R_pos_of_le_xiMinus
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u : ℝ}
    (hu : 0 < u) (huroot : u ≤ xiMinus h k) :
    0 < R h k u := by
  let a : ℝ := u / 4
  let b : ℝ := u / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hbu : b < u := by dsimp [b]; linarith
  have hbroot : b < xiMinus h k := lt_of_lt_of_le hbu huroot
  have hsmall :
      0 < ∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioc a b)) :=
    setIntegral_rDerivativeIntegrand_pos_left h hk ha hab hbroot
  have hbigInt : IntegrableOn (rDerivativeIntegrand h k) (Ioc (0 : ℝ) u) :=
    rDerivativeIntegrand_integrableOn_mono_Ioi h k (by
      intro x hx
      exact hx.1)
  have hbigNonneg :
      0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) u)] rDerivativeIntegrand h k := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    exact rDerivativeIntegrand_nonneg_left h hk hx.1 (hx.2.trans huroot)
  have hsmall_subset : Ioc a b ≤ᵐ[volume] Ioc (0 : ℝ) u :=
    Eventually.of_forall (by
      intro x hx
      exact ⟨lt_trans ha hx.1, hx.2.trans (le_of_lt hbu)⟩)
  have hmono :
      (∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioc a b))) ≤
        ∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioc (0 : ℝ) u)) :=
    setIntegral_mono_set hbigInt hbigNonneg hsmall_subset
  have hR := R_eq_setIntegral_rDerivativeIntegrand h k hu
  linarith

/-- The crossing kernel is strictly negative from the larger quadratic root onward. -/
lemma R_neg_of_xiPlus_le
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u : ℝ}
    (hrootu : xiPlus h k ≤ u) :
    R h k u < 0 := by
  have hu : 0 < u := lt_of_lt_of_le (xiPlus_pos h hk) hrootu
  let a : ℝ := 2 * u
  let b : ℝ := 3 * u
  have hua : u < a := by dsimp [a]; linarith
  have haRoot : xiPlus h k < a := lt_of_le_of_lt hrootu hua
  have hab : a < b := by dsimp [a, b]; linarith
  have hsmall :
      0 < ∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioc a b)) :=
    setIntegral_rDerivativeIntegrand_pos_right h hk haRoot hab
  have htailInt : IntegrableOn (rDerivativeIntegrand h k) (Ioi u) :=
    rDerivativeIntegrand_integrableOn_mono_Ioi h k (by
      intro x hx
      exact lt_trans hu hx)
  have htailNonneg :
      0 ≤ᵐ[volume.restrict (Ioi u)] rDerivativeIntegrand h k := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    filter_upwards with x hx
    exact rDerivativeIntegrand_nonneg_right h hk (hrootu.trans (le_of_lt hx))
  have hsmall_subset : Ioc a b ≤ᵐ[volume] Ioi u :=
    Eventually.of_forall (by
      intro x hx
      exact lt_trans hua hx.1)
  have hmono :
      (∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioc a b))) ≤
        ∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioi u)) :=
    setIntegral_mono_set htailInt htailNonneg hsmall_subset
  have hR := R_eq_neg_tailIntegral_rDerivativeIntegrand h k hu
  linarith

/-- There is exactly one zero of `R_k` between the two roots of its derivative quadratic. -/
theorem exists_unique_R_zero_between
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    ∃! u, u ∈ Ioo (xiMinus h k) (xiPlus h k) ∧ R h k u = 0 := by
  have hroots : xiMinus h k < xiPlus h k := xiMinus_lt_xiPlus h hk
  have hminusPos : 0 < R h k (xiMinus h k) :=
    R_pos_of_le_xiMinus h hk (xiMinus_pos h hk) le_rfl
  have hplusNeg : R h k (xiPlus h k) < 0 :=
    R_neg_of_xiPlus_le h hk le_rfl
  have hAC : AbsolutelyContinuousOnInterval (R h k) (xiMinus h k) (xiPlus h k) :=
    R_absolutelyContinuousOnInterval h k (xiMinus_pos h hk) hroots.le
  have hcont : ContinuousOn (R h k) (Icc (xiMinus h k) (xiPlus h k)) := by
    simpa [uIcc_of_le hroots.le] using hAC.continuousOn
  have hzero_mem :
      (0 : ℝ) ∈ Icc (R h k (xiPlus h k)) (R h k (xiMinus h k)) :=
    ⟨hplusNeg.le, hminusPos.le⟩
  have himage := intermediate_value_Icc' hroots.le hcont hzero_mem
  rcases himage with ⟨u, huIcc, huZero⟩
  have huLeft : xiMinus h k < u := by
    rcases huIcc.1.eq_or_lt with hEq | hlt
    · subst u
      linarith
    · exact hlt
  have huRight : u < xiPlus h k := by
    rcases huIcc.2.eq_or_lt with hEq | hlt
    · subst u
      linarith
    · exact hlt
  have hu : u ∈ Ioo (xiMinus h k) (xiPlus h k) := ⟨huLeft, huRight⟩
  refine ⟨u, ⟨hu, huZero⟩, ?_⟩
  intro v hv
  have hanti := R_strictAntiOn_middle h hk
  rcases lt_trichotomy v u with hvu | hvu | huv
  · have hlt := hanti hv.1 hu hvu
    linarith [hv.2, huZero]
  · exact hvu
  · have hlt := hanti hu hv.1 huv
    linarith [hv.2, huZero]

/-- The canonical crossing point `u_k^*` from Theorem 2.2(iii). -/
def uStar (h : FullSupportMomentWeight) (k : ℕ) : ℝ :=
  if hk : 1 ≤ k then Classical.choose (exists_unique_R_zero_between h hk).exists else 0

/-- The canonical crossing point lies strictly between the two quadratic roots and zeros `R_k`. -/
lemma uStar_spec
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    uStar h k ∈ Ioo (xiMinus h k) (xiPlus h k) ∧ R h k (uStar h k) = 0 := by
  rw [uStar, dif_pos hk]
  exact Classical.choose_spec (exists_unique_R_zero_between h hk).exists

/-- `R_k` is positive at every positive point before the canonical crossing. -/
lemma R_pos_before_uStar
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : 0 < x) (hxu : x < uStar h k) :
    0 < R h k x := by
  have hu := (uStar_spec h hk).1
  rcases le_or_gt x (xiMinus h k) with hxroot | hrootx
  · exact R_pos_of_le_xiMinus h hk hx hxroot
  · have hxmid : x ∈ Ioo (xiMinus h k) (xiPlus h k) :=
      ⟨hrootx, lt_trans hxu hu.2⟩
    have hanti := R_strictAntiOn_middle h hk hxmid hu hxu
    rw [(uStar_spec h hk).2] at hanti
    linarith

/-- `R_k` is negative at every point after the canonical crossing. -/
lemma R_neg_after_uStar
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hux : uStar h k < x) :
    R h k x < 0 := by
  have hu := (uStar_spec h hk).1
  rcases le_or_gt (xiPlus h k) x with hrootx | hxroot
  · exact R_neg_of_xiPlus_le h hk hrootx
  · have hxmid : x ∈ Ioo (xiMinus h k) (xiPlus h k) :=
      ⟨lt_trans hu.1 hux, hxroot⟩
    have hanti := R_strictAntiOn_middle h hk hu hxmid hux
    rw [(uStar_spec h hk).2] at hanti
    linarith

/-- The canonical crossing is the unique positive zero of `R_k`. -/
lemma R_eq_zero_iff_uStar
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 < x) :
    R h k x = 0 ↔ x = uStar h k := by
  constructor
  · intro hzero
    rcases lt_trichotomy x (uStar h k) with hlt | heq | hgt
    · linarith [R_pos_before_uStar h hk hx hlt]
    · exact heq
    · linarith [R_neg_after_uStar h hk hgt]
  · rintro rfl
    exact (uStar_spec h hk).2

/-- The normalized crossing kernel `Rhat_k` has the same positive-side sign pattern as `R_k`. -/
lemma Rhat_pos_before_uStar
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : 0 < x) (hxu : x < uStar h k) :
    0 < Rhat h k x := by
  rw [Rhat]
  exact div_pos (R_pos_before_uStar h hk hx hxu) (N_pos h (by omega))

/-- The normalized crossing kernel `Rhat_k` has the same negative-side sign pattern as `R_k`. -/
lemma Rhat_neg_after_uStar
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hux : uStar h k < x) :
    Rhat h k x < 0 := by
  rw [Rhat]
  exact div_neg_of_neg_of_pos (R_neg_after_uStar h hk hux) (N_pos h (by omega))

/-- **Universal one-crossing theorem (manuscript Theorem 2.2(ii)–(iii)).**

The quadratic derivative law has two distinct positive roots. `R_k` is locally absolutely
continuous and has the manuscript derivative almost everywhere. It has exactly one positive zero,
strictly between those roots, and `R_k` and `Rhat_k` are positive before and negative after that
canonical crossing.
-/
theorem universal_one_crossing
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    0 < crossingDisc h k ∧
      0 < xiMinus h k ∧ xiMinus h k < xiPlus h k ∧
      (∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → AbsolutelyContinuousOnInterval (R h k) a b) ∧
      (∀ᵐ x, 0 < x → HasDerivAt (R h k) (rDerivativeIntegrand h k x) x) ∧
      uStar h k ∈ Ioo (xiMinus h k) (xiPlus h k) ∧
      R h k (uStar h k) = 0 ∧
      (∀ x, 0 < x → x < uStar h k → 0 < R h k x ∧ 0 < Rhat h k x) ∧
      (∀ x, uStar h k < x → R h k x < 0 ∧ Rhat h k x < 0) := by
  have hdisc : 0 < crossingDisc h k := crossingDisc_pos h hk
  have hminus : 0 < xiMinus h k := xiMinus_pos h hk
  have hroots : xiMinus h k < xiPlus h k := xiMinus_lt_xiPlus h hk
  have hAC : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → AbsolutelyContinuousOnInterval (R h k) a b := by
    intro a b ha hab
    exact R_absolutelyContinuousOnInterval h k ha hab
  have hderiv : ∀ᵐ x, 0 < x → HasDerivAt (R h k) (rDerivativeIntegrand h k x) x :=
    R_ae_hasDerivAt h k
  have hu := uStar_spec h hk
  have hleft : ∀ x, 0 < x → x < uStar h k → 0 < R h k x ∧ 0 < Rhat h k x := by
    intro x hx hxu
    exact ⟨R_pos_before_uStar h hk hx hxu, Rhat_pos_before_uStar h hk hx hxu⟩
  have hright : ∀ x, uStar h k < x → R h k x < 0 ∧ Rhat h k x < 0 := by
    intro x hux
    exact ⟨R_neg_after_uStar h hk hux, Rhat_neg_after_uStar h hk hux⟩
  exact ⟨hdisc, hminus, hroots, hAC, hderiv, hu.1, hu.2, hleft, hright⟩

end CrossBoundaryMomentKernels
