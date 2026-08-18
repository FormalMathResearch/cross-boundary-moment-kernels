import CrossBoundaryMomentKernels.TotalPositivity

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- The positive constant `C_k = I_{k+1} N_k / (I_k N_{k+1})` from §3.4. -/
def tpC (h : ℝ → ℝ) (k : ℕ) : ℝ :=
  I h (k + 1) * N h k / (I h k * N h (k + 1))

/-- The rational function `φ_k(u) = u (γ_{k+1}-u)/(γ_k-u)` from §3.4. -/
def tpPhi (h : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  u * (gamma h (k + 1) - u) / (gamma h k - u)

lemma tpC_pos (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    0 < tpC h k := by
  rw [tpC]
  exact div_pos
    (mul_pos (h.momentPositive (k + 1)) (N_pos h hk))
    (mul_pos (h.momentPositive k) (N_pos h (by omega)))

/-- Exact difference identity behind strict monotonicity of `φ_k`. -/
lemma tpPhi_sub_tpPhi
    (h : FullSupportMomentWeight) (k : ℕ) {x y : ℝ}
    (hx : x ≠ gamma h k) (hy : y ≠ gamma h k) :
    tpPhi h k y - tpPhi h k x =
      (y - x) *
        (((gamma h k - x) * (gamma h k - y) +
            gamma h k * (gamma h (k + 1) - gamma h k)) /
          ((gamma h k - x) * (gamma h k - y))) := by
  rw [tpPhi, tpPhi]
  field_simp
  ring

/-- `φ_k` is strictly increasing on the left of its pole `γ_k`. -/
lemma tpPhi_lt_left
    (h : FullSupportMomentWeight) (k : ℕ) {x y : ℝ}
    (hxy : x < y) (hy : y < gamma h k) :
    tpPhi h k x < tpPhi h k y := by
  have ha : 0 < gamma h k := gamma_pos h k
  have hab : gamma h k < gamma h (k + 1) :=
    (strict_moment_logConvexity_and_gamma_lt h k).2
  have hxg : x < gamma h k := lt_trans hxy hy
  have hxne : x ≠ gamma h k := ne_of_lt hxg
  have hyne : y ≠ gamma h k := ne_of_lt hy
  have hden : 0 < (gamma h k - x) * (gamma h k - y) :=
    mul_pos (sub_pos.mpr hxg) (sub_pos.mpr hy)
  have hnum :
      0 < (gamma h k - x) * (gamma h k - y) +
        gamma h k * (gamma h (k + 1) - gamma h k) := by
    exact add_pos hden (mul_pos ha (sub_pos.mpr hab))
  rw [← sub_pos, tpPhi_sub_tpPhi h k hxne hyne]
  exact mul_pos (sub_pos.mpr hxy) (div_pos hnum hden)

/-- `φ_k` is strictly increasing on the right of its pole `γ_k`. -/
lemma tpPhi_lt_right
    (h : FullSupportMomentWeight) (k : ℕ) {x y : ℝ}
    (hx : gamma h k < x) (hxy : x < y) :
    tpPhi h k x < tpPhi h k y := by
  have ha : 0 < gamma h k := gamma_pos h k
  have hab : gamma h k < gamma h (k + 1) :=
    (strict_moment_logConvexity_and_gamma_lt h k).2
  have hy : gamma h k < y := lt_trans hx hxy
  have hxne : x ≠ gamma h k := ne_of_gt hx
  have hyne : y ≠ gamma h k := ne_of_gt hy
  have hden : 0 < (gamma h k - x) * (gamma h k - y) :=
    mul_pos_of_neg_of_neg (sub_neg.mpr hx) (sub_neg.mpr hy)
  have hnum :
      0 < (gamma h k - x) * (gamma h k - y) +
        gamma h k * (gamma h (k + 1) - gamma h k) := by
    exact add_pos hden (mul_pos ha (sub_pos.mpr hab))
  rw [← sub_pos, tpPhi_sub_tpPhi h k hxne hyne]
  exact mul_pos (sub_pos.mpr hxy) (div_pos hnum hden)

/-- Pointwise derivative-ratio identity printed in §3.4. -/
lemma zDerivativeIntegrand_succ_eq_tpC_mul_tpPhi
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : 0 < x) (hxg : x ≠ gamma h k) :
    zDerivativeIntegrand h (k + 1) x =
      tpC h k * tpPhi h k x * zDerivativeIntegrand h k x := by
  have hIk : I h k ≠ 0 := ne_of_gt (h.momentPositive k)
  have hIk₁ : I h (k + 1) ≠ 0 := ne_of_gt (h.momentPositive (k + 1))
  have hNk : N h k ≠ 0 := ne_of_gt (N_pos h hk)
  have hNk₁ : N h (k + 1) ≠ 0 := ne_of_gt (N_pos h (by omega))
  have hgam : gamma h k - x ≠ 0 := sub_ne_zero.mpr hxg.symm
  rw [zDerivativeIntegrand, zDerivativeIntegrand, tpC, tpPhi,
    momentIntegrand_succ h k hx]
  field_simp

/-- Full support gives positive Lebesgue measure to the support of `h` in every compact
positive subinterval. -/
lemma support_h_measure_pos_Ioc
    (h : FullSupportMomentWeight) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < volume (Function.support (h : ℝ → ℝ) ∩ Ioc a b) := by
  have hfull : 0 < ∫ x, h x ∂(volume.restrict (Ioc a b)) := h.fullSupport ha hab
  have hhInt : IntegrableOn (h : ℝ → ℝ) (Ioc a b) := by
    by_contra hnot
    have hzero : ∫ x, h x ∂(volume.restrict (Ioc a b)) = 0 := integral_undef hnot
    linarith
  have hhNonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] (h : ℝ → ℝ) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    exact h.nonneg (lt_trans ha hx.1)
  exact (setIntegral_pos_iff_support_of_nonneg_ae hhNonneg hhInt).mp hfull

lemma zDerivativeIntegrand_nonneg_below_gamma
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : 0 < x) (hxg : x ≤ gamma h k) :
    0 ≤ zDerivativeIntegrand h k x := by
  rw [zDerivativeIntegrand]
  exact mul_nonneg
    (mul_nonneg (div_nonneg (h.momentPositive k).le (N_pos h hk).le)
      (momentIntegrand_nonneg h k hx))
    (sub_nonneg.mpr hxg)

lemma zDerivativeIntegrand_pos_below_gamma_of_support
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : 0 < x) (hxg : x < gamma h k)
    (hsupp : x ∈ Function.support (h : ℝ → ℝ)) :
    0 < zDerivativeIntegrand h k x := by
  rw [zDerivativeIntegrand]
  exact mul_pos
    (mul_pos (div_pos (h.momentPositive k) (N_pos h hk))
      (momentIntegrand_pos_of_mem_support h k hx hsupp))
    (sub_pos.mpr hxg)

lemma zDerivativeIntegrand_nonpos_above_gamma
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : 0 < x) (hxg : gamma h k ≤ x) :
    zDerivativeIntegrand h k x ≤ 0 := by
  rw [zDerivativeIntegrand]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (div_nonneg (h.momentPositive k).le (N_pos h hk).le)
      (momentIntegrand_nonneg h k hx))
    (sub_nonpos.mpr hxg)

lemma zDerivativeIntegrand_neg_above_gamma_of_support
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : 0 < x) (hxg : gamma h k < x)
    (hsupp : x ∈ Function.support (h : ℝ → ℝ)) :
    zDerivativeIntegrand h k x < 0 := by
  rw [zDerivativeIntegrand]
  exact mul_neg_of_pos_of_neg
    (mul_pos (div_pos (h.momentPositive k) (N_pos h hk))
      (momentIntegrand_pos_of_mem_support h k hx hsupp))
    (sub_neg.mpr hxg)

/-- Every nonempty interval strictly below `γ_k` has positive `Z_k'` mass. -/
lemma setIntegral_zDerivativeIntegrand_pos_below_gamma
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hbg : b < gamma h k) :
    0 < ∫ x, zDerivativeIntegrand h k x ∂(volume.restrict (Ioc a b)) := by
  have hInt : IntegrableOn (zDerivativeIntegrand h k) (Ioc a b) :=
    zDerivativeIntegrand_integrableOn_mono_Ioi h hk (by
      intro x hx
      exact lt_trans ha hx.1)
  have hNonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] zDerivativeIntegrand h k := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    exact zDerivativeIntegrand_nonneg_below_gamma h hk
      (lt_trans ha hx.1) (le_trans hx.2 hbg.le)
  have hsupp :
      Function.support (h : ℝ → ℝ) ∩ Ioc a b ⊆
        Function.support (zDerivativeIntegrand h k) ∩ Ioc a b := by
    intro x hx
    refine ⟨?_, hx.2⟩
    exact ne_of_gt (zDerivativeIntegrand_pos_below_gamma_of_support h hk
      (lt_trans ha hx.2.1) (lt_of_le_of_lt hx.2.2 hbg) hx.1)
  have hSuppPos :
      0 < volume (Function.support (zDerivativeIntegrand h k) ∩ Ioc a b) :=
    lt_of_lt_of_le (support_h_measure_pos_Ioc h ha hab) (measure_mono hsupp)
  exact (setIntegral_pos_iff_support_of_nonneg_ae hNonneg hInt).2 hSuppPos

/-- Every nonempty interval strictly above `γ_k` has strictly negative `Z_k'` mass. -/
lemma setIntegral_zDerivativeIntegrand_neg_above_gamma
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {a b : ℝ}
    (hga : gamma h k < a) (hab : a < b) :
    ∫ x, zDerivativeIntegrand h k x ∂(volume.restrict (Ioc a b)) < 0 := by
  have ha : 0 < a := lt_trans (gamma_pos h k) hga
  have hInt : IntegrableOn (zDerivativeIntegrand h k) (Ioc a b) :=
    zDerivativeIntegrand_integrableOn_mono_Ioi h hk (by
      intro x hx
      exact lt_trans ha hx.1)
  have hNegInt : IntegrableOn (fun x ↦ - zDerivativeIntegrand h k x) (Ioc a b) := hInt.neg
  have hNonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] (fun x ↦ - zDerivativeIntegrand h k x) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    exact neg_nonneg.mpr (zDerivativeIntegrand_nonpos_above_gamma h hk
      (lt_trans ha hx.1) (le_trans hga.le hx.1.le))
  have hsupp :
      Function.support (h : ℝ → ℝ) ∩ Ioc a b ⊆
        Function.support (fun x ↦ - zDerivativeIntegrand h k x) ∩ Ioc a b := by
    intro x hx
    refine ⟨?_, hx.2⟩
    have hneg := zDerivativeIntegrand_neg_above_gamma_of_support h hk
      (lt_trans ha hx.2.1) (lt_trans hga hx.2.1) hx.1
    exact neg_ne_zero.mpr (ne_of_lt hneg)
  have hSuppPos :
      0 < volume (Function.support (fun x ↦ - zDerivativeIntegrand h k x) ∩ Ioc a b) :=
    lt_of_lt_of_le (support_h_measure_pos_Ioc h ha hab) (measure_mono hsupp)
  have hpos :
      0 < ∫ x, (- zDerivativeIntegrand h k x) ∂(volume.restrict (Ioc a b)) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hNonneg hNegInt).2 hSuppPos
  rw [integral_neg] at hpos
  linarith

/-- `Z_k` is strictly increasing before `γ_k`. -/
lemma Z_lt_Z_below_gamma
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) (hvg : v < gamma h k) :
    Z h k u < Z h k v := by
  have hdiff := Z_sub_Z_eq_setIntegral_zDerivativeIntegrand h hk hu huv
  have hpos := setIntegral_zDerivativeIntegrand_pos_below_gamma h hk hu huv hvg
  linarith

/-- `Z_k` is strictly decreasing after `γ_k`. -/
lemma Z_lt_Z_above_gamma
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u v : ℝ}
    (hgu : gamma h k < u) (huv : u < v) :
    Z h k v < Z h k u := by
  have hu : 0 < u := lt_trans (gamma_pos h k) hgu
  have hdiff := Z_sub_Z_eq_setIntegral_zDerivativeIntegrand h hk hu huv
  have hneg := setIntegral_zDerivativeIntegrand_neg_above_gamma h hk hgu huv
  linarith

end CrossBoundaryMomentKernels
