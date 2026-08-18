import CrossBoundaryMomentKernels.TotalPositivityRatio

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- The positive derivative mass remains strict when the upper endpoint is `γ_k`. -/
lemma setIntegral_zDerivativeIntegrand_pos_below_gamma_le
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hbg : b ≤ gamma h k) :
    0 < ∫ x, zDerivativeIntegrand h k x ∂(volume.restrict (Ioc a b)) := by
  let c : ℝ := (a + b) / 2
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  have hcg : c < gamma h k := lt_of_lt_of_le hcb hbg
  have hinner :
      0 < ∫ x, zDerivativeIntegrand h k x ∂(volume.restrict (Ioc a c)) :=
    setIntegral_zDerivativeIntegrand_pos_below_gamma h hk ha hac hcg
  have hInt : IntegrableOn (zDerivativeIntegrand h k) (Ioc a b) :=
    zDerivativeIntegrand_integrableOn_mono_Ioi h hk (by
      intro x hx
      exact lt_trans ha hx.1)
  have hNonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] zDerivativeIntegrand h k := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    exact zDerivativeIntegrand_nonneg_below_gamma h hk
      (lt_trans ha hx.1) (le_trans hx.2 hbg)
  have hsubset : Ioc a c ≤ᵐ[volume] Ioc a b :=
    Eventually.of_forall (by
      intro x hx
      exact ⟨hx.1, hx.2.trans hcb.le⟩)
  have hmono :
      (∫ x, zDerivativeIntegrand h k x ∂(volume.restrict (Ioc a c))) ≤
        ∫ x, zDerivativeIntegrand h k x ∂(volume.restrict (Ioc a b)) :=
    setIntegral_mono_set hInt hNonneg hsubset
  linarith

/-- The negative derivative mass is strict already when the lower endpoint is `γ_k`. -/
lemma setIntegral_zDerivativeIntegrand_neg_above_gamma_le
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {a b : ℝ}
    (hga : gamma h k ≤ a) (hab : a < b) :
    ∫ x, zDerivativeIntegrand h k x ∂(volume.restrict (Ioc a b)) < 0 := by
  have ha : 0 < a := lt_of_lt_of_le (gamma_pos h k) hga
  have hInt : IntegrableOn (zDerivativeIntegrand h k) (Ioc a b) :=
    zDerivativeIntegrand_integrableOn_mono_Ioi h hk (by
      intro x hx
      exact lt_trans ha hx.1)
  have hNegInt : IntegrableOn (fun x ↦ - zDerivativeIntegrand h k x) (Ioc a b) := hInt.neg
  have hNonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] (fun x ↦ - zDerivativeIntegrand h k x) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    exact neg_nonneg.mpr (zDerivativeIntegrand_nonpos_above_gamma h hk
      (lt_trans ha hx.1) (le_trans hga hx.1.le))
  have hsupp :
      Function.support (h : ℝ → ℝ) ∩ Ioc a b ⊆
        Function.support (fun x ↦ - zDerivativeIntegrand h k x) ∩ Ioc a b := by
    intro x hx
    refine ⟨?_, hx.2⟩
    have hneg := zDerivativeIntegrand_neg_above_gamma_of_support h hk
      (lt_trans ha hx.2.1) (lt_of_le_of_lt hga hx.2.1) hx.1
    exact neg_ne_zero.mpr (ne_of_lt hneg)
  have hSuppPos :
      0 < volume (Function.support (fun x ↦ - zDerivativeIntegrand h k x) ∩ Ioc a b) :=
    lt_of_lt_of_le (support_h_measure_pos_Ioc h ha hab) (measure_mono hsupp)
  have hpos :
      0 < ∫ x, (- zDerivativeIntegrand h k x) ∂(volume.restrict (Ioc a b)) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hNonneg hNegInt).2 hSuppPos
  rw [integral_neg] at hpos
  linarith

lemma Z_lt_Z_below_gamma_le
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) (hvg : v ≤ gamma h k) :
    Z h k u < Z h k v := by
  have hdiff := Z_sub_Z_eq_setIntegral_zDerivativeIntegrand h hk hu huv
  have hpos := setIntegral_zDerivativeIntegrand_pos_below_gamma_le h hk hu huv hvg
  linarith

lemma Z_lt_Z_above_gamma_le
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u v : ℝ}
    (hgu : gamma h k ≤ u) (huv : u < v) :
    Z h k v < Z h k u := by
  have hu : 0 < u := lt_of_lt_of_le (gamma_pos h k) hgu
  have hdiff := Z_sub_Z_eq_setIntegral_zDerivativeIntegrand h hk hu huv
  have hneg := setIntegral_zDerivativeIntegrand_neg_above_gamma_le h hk hgu huv
  linarith

/-- Strict lower-truncated average inequality from Lemma 3.2, specialized to the derivative
measure of `Z_k`. -/
lemma adjacent_Z_ratio_lt_below_gamma
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) (hvg : v ≤ gamma h k) :
    Z h (k + 1) u / Z h k u < Z h (k + 1) v / Z h k v := by
  have hgammas : gamma h k < gamma h (k + 1) :=
    (strict_moment_logConvexity_and_gamma_lt h k).2
  have hug : u < gamma h k := lt_of_lt_of_le huv hvg
  have hC : 0 < tpC h k := tpC_pos h hk
  let c : ℝ := tpC h k * tpPhi h k u
  let gapL : ℝ → ℝ := fun x ↦ c * zDerivativeIntegrand h k x - zDerivativeIntegrand h (k + 1) x
  let gapR : ℝ → ℝ := fun x ↦ zDerivativeIntegrand h (k + 1) x - c * zDerivativeIntegrand h k x

  have hkLeft : IntegrableOn (zDerivativeIntegrand h k) (Ioc (0 : ℝ) u) :=
    zDerivativeIntegrand_integrableOn_mono_Ioi h hk (by intro x hx; exact hx.1)
  have hk₁Left : IntegrableOn (zDerivativeIntegrand h (k + 1)) (Ioc (0 : ℝ) u) :=
    zDerivativeIntegrand_integrableOn_mono_Ioi h (by omega) (by intro x hx; exact hx.1)
  have hgapLInt : IntegrableOn gapL (Ioc (0 : ℝ) u) := by
    dsimp [gapL]
    exact (hkLeft.const_mul c).sub hk₁Left
  have hgapLNonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) u)] gapL := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    have hxg : x < gamma h k := lt_of_le_of_lt hx.2 hug
    have hxne : x ≠ gamma h k := ne_of_lt hxg
    have hrel := zDerivativeIntegrand_succ_eq_tpC_mul_tpPhi h hk hx.1 hxne
    have hfx : 0 ≤ zDerivativeIntegrand h k x :=
      zDerivativeIntegrand_nonneg_below_gamma h hk hx.1 hxg.le
    have hphi : tpPhi h k x ≤ tpPhi h k u := by
      rcases hx.2.eq_or_lt with hxu | hxu
      · subst x
        exact le_rfl
      · exact (tpPhi_lt_left h k hxu hug).le
    have hmul :
        tpC h k * tpPhi h k x * zDerivativeIntegrand h k x ≤
          tpC h k * tpPhi h k u * zDerivativeIntegrand h k x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hphi hC.le) hfx
    dsimp [gapL, c]
    rw [hrel]
    linarith
  have hsuppL :
      Function.support (h : ℝ → ℝ) ∩ Ioc (u / 4) (u / 2) ⊆
        Function.support gapL ∩ Ioc (0 : ℝ) u := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.2.1, hu]
    have hxu : x < u := by linarith [hx.2.2, hu]
    have hxg : x < gamma h k := lt_trans hxu hug
    have hrel := zDerivativeIntegrand_succ_eq_tpC_mul_tpPhi h hk hx0 (ne_of_lt hxg)
    have hfx : 0 < zDerivativeIntegrand h k x :=
      zDerivativeIntegrand_pos_below_gamma_of_support h hk hx0 hxg hx.1
    have hphi : tpPhi h k x < tpPhi h k u := tpPhi_lt_left h k hxu hug
    have hmul :
        tpC h k * tpPhi h k x * zDerivativeIntegrand h k x <
          tpC h k * tpPhi h k u * zDerivativeIntegrand h k x := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hphi hC) hfx
    refine ⟨?_, ⟨hx0, hxu.le⟩⟩
    dsimp [gapL, c]
    rw [hrel]
    exact ne_of_gt (sub_pos.mpr hmul)
  have hSuppL : 0 < volume (Function.support gapL ∩ Ioc (0 : ℝ) u) := by
    have hinner : 0 < volume (Function.support (h : ℝ → ℝ) ∩ Ioc (u / 4) (u / 2)) :=
      support_h_measure_pos_Ioc h (by linarith [hu]) (by linarith [hu])
    exact lt_of_lt_of_le hinner (measure_mono hsuppL)
  have hgapLPos : 0 < ∫ x, gapL x ∂(volume.restrict (Ioc (0 : ℝ) u)) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hgapLNonneg hgapLInt).2 hSuppL
  have hgapLEq :
      (∫ x, gapL x ∂(volume.restrict (Ioc (0 : ℝ) u))) =
        c * Z h k u - Z h (k + 1) u := by
    dsimp [gapL]
    rw [integral_sub (hkLeft.const_mul c) hk₁Left, integral_const_mul]
    rw [← Z_eq_setIntegral_zDerivativeIntegrand h hk hu,
      ← Z_eq_setIntegral_zDerivativeIntegrand h (k := k + 1) (by omega) hu]
  have hleft : Z h (k + 1) u < c * Z h k u := by
    rw [hgapLEq] at hgapLPos
    linarith

  have hkRight : IntegrableOn (zDerivativeIntegrand h k) (Ioc u v) :=
    zDerivativeIntegrand_integrableOn_mono_Ioi h hk (by
      intro x hx
      exact lt_trans hu hx.1)
  have hk₁Right : IntegrableOn (zDerivativeIntegrand h (k + 1)) (Ioc u v) :=
    zDerivativeIntegrand_integrableOn_mono_Ioi h (by omega) (by
      intro x hx
      exact lt_trans hu hx.1)
  have hgapRInt : IntegrableOn gapR (Ioc u v) := by
    dsimp [gapR]
    exact hk₁Right.sub (hkRight.const_mul c)
  have hgapRNonneg : 0 ≤ᵐ[volume.restrict (Ioc u v)] gapR := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    by_cases hxgEq : x = gamma h k
    · subst x
      have hkzero : zDerivativeIntegrand h k (gamma h k) = 0 := by
        simp [zDerivativeIntegrand]
      have hsucc : 0 ≤ zDerivativeIntegrand h (k + 1) (gamma h k) :=
        zDerivativeIntegrand_nonneg_below_gamma h (by omega) (gamma_pos h k) hgammas.le
      dsimp [gapR]
      rw [hkzero, mul_zero, sub_zero]
      exact hsucc
    · have hxg : x < gamma h k := lt_of_le_of_ne (le_trans hx.2 hvg) hxgEq
      have hrel := zDerivativeIntegrand_succ_eq_tpC_mul_tpPhi h hk
        (lt_trans hu hx.1) hxgEq
      have hfx : 0 ≤ zDerivativeIntegrand h k x :=
        zDerivativeIntegrand_nonneg_below_gamma h hk (lt_trans hu hx.1) hxg.le
      have hphi : tpPhi h k u ≤ tpPhi h k x :=
        (tpPhi_lt_left h k hx.1 hxg).le
      have hmul :
          tpC h k * tpPhi h k u * zDerivativeIntegrand h k x ≤
            tpC h k * tpPhi h k x * zDerivativeIntegrand h k x := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hphi hC.le) hfx
      dsimp [gapR, c]
      rw [hrel]
      linarith
  let w : ℝ := (u + v) / 2
  have huw : u < w := by dsimp [w]; linarith
  have hwv : w < v := by dsimp [w]; linarith
  have hwg : w < gamma h k := lt_of_lt_of_le hwv hvg
  have hsuppR :
      Function.support (h : ℝ → ℝ) ∩ Ioc u w ⊆
        Function.support gapR ∩ Ioc u v := by
    intro x hx
    have hx0 : 0 < x := lt_trans hu hx.2.1
    have hxg : x < gamma h k := lt_of_le_of_lt hx.2.2 hwg
    have hrel := zDerivativeIntegrand_succ_eq_tpC_mul_tpPhi h hk hx0 (ne_of_lt hxg)
    have hfx : 0 < zDerivativeIntegrand h k x :=
      zDerivativeIntegrand_pos_below_gamma_of_support h hk hx0 hxg hx.1
    have hphi : tpPhi h k u < tpPhi h k x := tpPhi_lt_left h k hx.2.1 hxg
    have hmul :
        tpC h k * tpPhi h k u * zDerivativeIntegrand h k x <
          tpC h k * tpPhi h k x * zDerivativeIntegrand h k x := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hphi hC) hfx
    refine ⟨?_, ⟨hx.2.1, hx.2.2.trans hwv.le⟩⟩
    dsimp [gapR, c]
    rw [hrel]
    exact ne_of_gt (sub_pos.mpr hmul)
  have hSuppR : 0 < volume (Function.support gapR ∩ Ioc u v) := by
    have hinner : 0 < volume (Function.support (h : ℝ → ℝ) ∩ Ioc u w) :=
      support_h_measure_pos_Ioc h hu huw
    exact lt_of_lt_of_le hinner (measure_mono hsuppR)
  have hgapRPos : 0 < ∫ x, gapR x ∂(volume.restrict (Ioc u v)) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hgapRNonneg hgapRInt).2 hSuppR
  have hgapREq :
      (∫ x, gapR x ∂(volume.restrict (Ioc u v))) =
        (Z h (k + 1) v - Z h (k + 1) u) - c * (Z h k v - Z h k u) := by
    dsimp [gapR]
    rw [integral_sub hk₁Right (hkRight.const_mul c), integral_const_mul]
    rw [← Z_sub_Z_eq_setIntegral_zDerivativeIntegrand h (k := k + 1) (by omega) hu huv,
      ← Z_sub_Z_eq_setIntegral_zDerivativeIntegrand h hk hu huv]
  have hright :
      c * (Z h k v - Z h k u) < Z h (k + 1) v - Z h (k + 1) u := by
    rw [hgapREq] at hgapRPos
    linarith

  have hZu : 0 < Z h k u := Z_pos h hk hu
  have hZv : 0 < Z h k v := Z_pos h hk (lt_trans hu huv)
  have hB : 0 < Z h k v - Z h k u := by
    linarith [Z_lt_Z_below_gamma_le h hk hu huv hvg]
  have hmulL := mul_lt_mul_of_pos_right hleft hB
  have hmulR := mul_lt_mul_of_pos_left hright hZu
  apply (div_lt_div_iff₀ hZu hZv).2
  nlinarith [hmulL, hmulR]

/-- In the middle interval the denominator decreases while the numerator increases. -/
lemma adjacent_Z_ratio_lt_middle
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u v : ℝ}
    (hgu : gamma h k ≤ u) (huv : u < v) (hvg : v ≤ gamma h (k + 1)) :
    Z h (k + 1) u / Z h k u < Z h (k + 1) v / Z h k v := by
  have hu : 0 < u := lt_of_lt_of_le (gamma_pos h k) hgu
  have hv : 0 < v := lt_trans hu huv
  have hden : Z h k v < Z h k u := Z_lt_Z_above_gamma_le h hk hgu huv
  have hnum : Z h (k + 1) u < Z h (k + 1) v :=
    Z_lt_Z_below_gamma_le h (by omega) hu huv hvg
  have hZu : 0 < Z h k u := Z_pos h hk hu
  have hZv : 0 < Z h k v := Z_pos h hk hv
  have hNu : 0 < Z h (k + 1) u := Z_pos h (by omega) hu
  have h1 := mul_lt_mul_of_pos_left hnum hZu
  have h2 := mul_lt_mul_of_pos_left hden hNu
  apply (div_lt_div_iff₀ hZu hZv).2
  nlinarith [h1, h2]

/-- Strict upper-tail average inequality from Lemma 3.2. -/
lemma adjacent_Z_ratio_lt_above_gamma
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u v : ℝ}
    (hgu : gamma h (k + 1) ≤ u) (huv : u < v) :
    Z h (k + 1) u / Z h k u < Z h (k + 1) v / Z h k v := by
  have hgammas : gamma h k < gamma h (k + 1) :=
    (strict_moment_logConvexity_and_gamma_lt h k).2
  have hu : 0 < u := lt_of_lt_of_le (gamma_pos h (k + 1)) hgu
  have hv : 0 < v := lt_trans hu huv
  have hC : 0 < tpC h k := tpC_pos h hk
  let c : ℝ := tpC h k * tpPhi h k v
  let gapRemoved : ℝ → ℝ := fun x ↦
    c * (- zDerivativeIntegrand h k x) - (- zDerivativeIntegrand h (k + 1) x)
  let gapTail : ℝ → ℝ := fun x ↦
    (- zDerivativeIntegrand h (k + 1) x) - c * (- zDerivativeIntegrand h k x)

  have hkRem : IntegrableOn (fun x ↦ - zDerivativeIntegrand h k x) (Ioc u v) := by
    exact (zDerivativeIntegrand_integrableOn_mono_Ioi h hk (by
      intro x hx
      exact lt_trans hu hx.1)).neg
  have hk₁Rem : IntegrableOn (fun x ↦ - zDerivativeIntegrand h (k + 1) x) (Ioc u v) := by
    exact (zDerivativeIntegrand_integrableOn_mono_Ioi h (by omega) (by
      intro x hx
      exact lt_trans hu hx.1)).neg
  have hGapRemInt : IntegrableOn gapRemoved (Ioc u v) := by
    dsimp [gapRemoved]
    exact (hkRem.const_mul c).sub hk₁Rem
  have hGapRemNonneg : 0 ≤ᵐ[volume.restrict (Ioc u v)] gapRemoved := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    have hx0 : 0 < x := lt_trans hu hx.1
    have hxg : gamma h k < x := lt_trans hgammas (lt_of_le_of_lt hgu hx.1)
    have hrel := zDerivativeIntegrand_succ_eq_tpC_mul_tpPhi h hk hx0 (ne_of_gt hxg)
    have hf : 0 ≤ - zDerivativeIntegrand h k x :=
      neg_nonneg.mpr (zDerivativeIntegrand_nonpos_above_gamma h hk hx0 hxg.le)
    have hphi : tpPhi h k x ≤ tpPhi h k v := by
      rcases hx.2.eq_or_lt with hxv | hxv
      · subst x
        exact le_rfl
      · exact (tpPhi_lt_right h k hxg hxv).le
    have hnegrel :
        - zDerivativeIntegrand h (k + 1) x =
          tpC h k * tpPhi h k x * (- zDerivativeIntegrand h k x) := by
      rw [hrel]
      ring
    have hmul :
        tpC h k * tpPhi h k x * (- zDerivativeIntegrand h k x) ≤
          tpC h k * tpPhi h k v * (- zDerivativeIntegrand h k x) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hphi hC.le) hf
    dsimp [gapRemoved, c]
    rw [hnegrel]
    linarith
  let w : ℝ := (u + v) / 2
  have huw : u < w := by dsimp [w]; linarith
  have hwv : w < v := by dsimp [w]; linarith
  have hsuppRem :
      Function.support (h : ℝ → ℝ) ∩ Ioc u w ⊆
        Function.support gapRemoved ∩ Ioc u v := by
    intro x hx
    have hx0 : 0 < x := lt_trans hu hx.2.1
    have hxg : gamma h k < x := lt_trans hgammas (lt_of_le_of_lt hgu hx.2.1)
    have hrel := zDerivativeIntegrand_succ_eq_tpC_mul_tpPhi h hk hx0 (ne_of_gt hxg)
    have hf : 0 < - zDerivativeIntegrand h k x :=
      neg_pos.mpr (zDerivativeIntegrand_neg_above_gamma_of_support h hk hx0 hxg hx.1)
    have hphi : tpPhi h k x < tpPhi h k v :=
      tpPhi_lt_right h k hxg (lt_of_le_of_lt hx.2.2 hwv)
    have hnegrel :
        - zDerivativeIntegrand h (k + 1) x =
          tpC h k * tpPhi h k x * (- zDerivativeIntegrand h k x) := by
      rw [hrel]
      ring
    have hmul :
        tpC h k * tpPhi h k x * (- zDerivativeIntegrand h k x) <
          tpC h k * tpPhi h k v * (- zDerivativeIntegrand h k x) := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hphi hC) hf
    refine ⟨?_, ⟨hx.2.1, hx.2.2.trans hwv.le⟩⟩
    dsimp [gapRemoved, c]
    rw [hnegrel]
    exact ne_of_gt (sub_pos.mpr hmul)
  have hSuppRem : 0 < volume (Function.support gapRemoved ∩ Ioc u v) := by
    have hinner : 0 < volume (Function.support (h : ℝ → ℝ) ∩ Ioc u w) :=
      support_h_measure_pos_Ioc h hu huw
    exact lt_of_lt_of_le hinner (measure_mono hsuppRem)
  have hGapRemPos : 0 < ∫ x, gapRemoved x ∂(volume.restrict (Ioc u v)) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hGapRemNonneg hGapRemInt).2 hSuppRem
  have hkRemEq :
      (∫ x, (- zDerivativeIntegrand h k x) ∂(volume.restrict (Ioc u v))) =
        Z h k u - Z h k v := by
    rw [integral_neg]
    rw [← Z_sub_Z_eq_setIntegral_zDerivativeIntegrand h hk hu huv]
    ring
  have hk₁RemEq :
      (∫ x, (- zDerivativeIntegrand h (k + 1) x) ∂(volume.restrict (Ioc u v))) =
        Z h (k + 1) u - Z h (k + 1) v := by
    rw [integral_neg]
    rw [← Z_sub_Z_eq_setIntegral_zDerivativeIntegrand h (k := k + 1) (by omega) hu huv]
    ring
  have hGapRemEq :
      (∫ x, gapRemoved x ∂(volume.restrict (Ioc u v))) =
        c * (Z h k u - Z h k v) - (Z h (k + 1) u - Z h (k + 1) v) := by
    dsimp [gapRemoved]
    rw [integral_sub (hkRem.const_mul c) hk₁Rem, integral_const_mul, hkRemEq, hk₁RemEq]
  have hremoved :
      Z h (k + 1) u - Z h (k + 1) v < c * (Z h k u - Z h k v) := by
    rw [hGapRemEq] at hGapRemPos
    linarith

  have hkTail : IntegrableOn (fun x ↦ - zDerivativeIntegrand h k x) (Ioi v) := by
    exact (zDerivativeIntegrand_integrableOn_mono_Ioi h hk (by
      intro x hx
      exact lt_trans hv hx)).neg
  have hk₁Tail : IntegrableOn (fun x ↦ - zDerivativeIntegrand h (k + 1) x) (Ioi v) := by
    exact (zDerivativeIntegrand_integrableOn_mono_Ioi h (by omega) (by
      intro x hx
      exact lt_trans hv hx)).neg
  have hGapTailInt : IntegrableOn gapTail (Ioi v) := by
    dsimp [gapTail]
    exact hk₁Tail.sub (hkTail.const_mul c)
  have hGapTailNonneg : 0 ≤ᵐ[volume.restrict (Ioi v)] gapTail := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    filter_upwards with x hx
    have hx0 : 0 < x := lt_trans hv hx
    have hxg : gamma h k < x := lt_trans hgammas (lt_of_le_of_lt hgu (lt_trans huv hx))
    have hrel := zDerivativeIntegrand_succ_eq_tpC_mul_tpPhi h hk hx0 (ne_of_gt hxg)
    have hf : 0 ≤ - zDerivativeIntegrand h k x :=
      neg_nonneg.mpr (zDerivativeIntegrand_nonpos_above_gamma h hk hx0 hxg.le)
    have hphi : tpPhi h k v ≤ tpPhi h k x :=
      (tpPhi_lt_right h k (lt_trans hgammas (lt_of_le_of_lt hgu huv)) hx).le
    have hnegrel :
        - zDerivativeIntegrand h (k + 1) x =
          tpC h k * tpPhi h k x * (- zDerivativeIntegrand h k x) := by
      rw [hrel]
      ring
    have hmul :
        tpC h k * tpPhi h k v * (- zDerivativeIntegrand h k x) ≤
          tpC h k * tpPhi h k x * (- zDerivativeIntegrand h k x) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hphi hC.le) hf
    dsimp [gapTail, c]
    rw [hnegrel]
    linarith
  have hsuppTail :
      Function.support (h : ℝ → ℝ) ∩ Ioc (2 * v) (3 * v) ⊆
        Function.support gapTail ∩ Ioi v := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.2.1, hv]
    have hvx : v < x := by linarith [hx.2.1, hv]
    have hxg : gamma h k < x := lt_trans hgammas (lt_of_le_of_lt hgu (lt_trans huv hvx))
    have hrel := zDerivativeIntegrand_succ_eq_tpC_mul_tpPhi h hk hx0 (ne_of_gt hxg)
    have hf : 0 < - zDerivativeIntegrand h k x :=
      neg_pos.mpr (zDerivativeIntegrand_neg_above_gamma_of_support h hk hx0 hxg hx.1)
    have hphi : tpPhi h k v < tpPhi h k x :=
      tpPhi_lt_right h k (lt_trans hgammas (lt_of_le_of_lt hgu huv)) hvx
    have hnegrel :
        - zDerivativeIntegrand h (k + 1) x =
          tpC h k * tpPhi h k x * (- zDerivativeIntegrand h k x) := by
      rw [hrel]
      ring
    have hmul :
        tpC h k * tpPhi h k v * (- zDerivativeIntegrand h k x) <
          tpC h k * tpPhi h k x * (- zDerivativeIntegrand h k x) := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hphi hC) hf
    refine ⟨?_, hvx⟩
    dsimp [gapTail, c]
    rw [hnegrel]
    exact ne_of_gt (sub_pos.mpr hmul)
  have hSuppTail : 0 < volume (Function.support gapTail ∩ Ioi v) := by
    have hinner : 0 < volume (Function.support (h : ℝ → ℝ) ∩ Ioc (2 * v) (3 * v)) :=
      support_h_measure_pos_Ioc h (by linarith [hv]) (by linarith [hv])
    exact lt_of_lt_of_le hinner (measure_mono hsuppTail)
  have hGapTailPos : 0 < ∫ x, gapTail x ∂(volume.restrict (Ioi v)) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hGapTailNonneg hGapTailInt).2 hSuppTail
  have hkTailEq :
      (∫ x, (- zDerivativeIntegrand h k x) ∂(volume.restrict (Ioi v))) = Z h k v := by
    rw [integral_neg]
    exact (Z_eq_neg_tailIntegral_zDerivativeIntegrand h hk hv).symm
  have hk₁TailEq :
      (∫ x, (- zDerivativeIntegrand h (k + 1) x) ∂(volume.restrict (Ioi v))) = Z h (k + 1) v := by
    rw [integral_neg]
    exact (Z_eq_neg_tailIntegral_zDerivativeIntegrand h (k := k + 1) (by omega) hv).symm
  have hGapTailEq :
      (∫ x, gapTail x ∂(volume.restrict (Ioi v))) = Z h (k + 1) v - c * Z h k v := by
    dsimp [gapTail]
    rw [integral_sub hk₁Tail (hkTail.const_mul c), integral_const_mul, hkTailEq, hk₁TailEq]
  have htail : c * Z h k v < Z h (k + 1) v := by
    rw [hGapTailEq] at hGapTailPos
    linarith

  have hZu : 0 < Z h k u := Z_pos h hk hu
  have hZv : 0 < Z h k v := Z_pos h hk hv
  have hB : 0 < Z h k u - Z h k v := by
    have hdec := Z_lt_Z_above_gamma_le h hk
      (le_trans hgammas.le hgu) huv
    linarith
  have hmulR := mul_lt_mul_of_pos_left hremoved hZv
  have hmulT := mul_lt_mul_of_pos_right htail hB
  apply (div_lt_div_iff₀ hZu hZv).2
  nlinarith [hmulR, hmulT]

/-- Adjacent normalized ratios are strictly increasing on the whole positive half-line. -/
theorem adjacent_Z_ratio_strict
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    Z h (k + 1) u / Z h k u < Z h (k + 1) v / Z h k v := by
  have hgammas : gamma h k < gamma h (k + 1) :=
    (strict_moment_logConvexity_and_gamma_lt h k).2
  by_cases hvLeft : v ≤ gamma h k
  · exact adjacent_Z_ratio_lt_below_gamma h hk hu huv hvLeft
  by_cases huRight : gamma h (k + 1) ≤ u
  · exact adjacent_Z_ratio_lt_above_gamma h hk huRight huv
  have hgv : gamma h k < v := lt_of_not_ge hvLeft
  have hug1 : u < gamma h (k + 1) := lt_of_not_ge huRight
  by_cases huLeft : u < gamma h k
  · have hLower := adjacent_Z_ratio_lt_below_gamma h hk hu huLeft le_rfl
    by_cases hvMiddle : v ≤ gamma h (k + 1)
    · have hMiddle := adjacent_Z_ratio_lt_middle h hk le_rfl hgv hvMiddle
      exact lt_trans hLower hMiddle
    · have hg1v : gamma h (k + 1) < v := lt_of_not_ge hvMiddle
      have hMiddle := adjacent_Z_ratio_lt_middle h hk le_rfl hgammas hgammas.le
      have hTail := adjacent_Z_ratio_lt_above_gamma h hk le_rfl hg1v
      exact lt_trans hLower (lt_trans hMiddle hTail)
  · have hgu : gamma h k ≤ u := le_of_not_gt huLeft
    by_cases hvMiddle : v ≤ gamma h (k + 1)
    · exact adjacent_Z_ratio_lt_middle h hk hgu huv hvMiddle
    · have hg1v : gamma h (k + 1) < v := lt_of_not_ge hvMiddle
      have hMiddle := adjacent_Z_ratio_lt_middle h hk hgu hug1 hgammas.le
      have hTail := adjacent_Z_ratio_lt_above_gamma h hk le_rfl hg1v
      exact lt_trans hMiddle hTail

end CrossBoundaryMomentKernels
