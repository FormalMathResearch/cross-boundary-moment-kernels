import CrossBoundaryMomentKernels.MomentCurvature
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

namespace CrossBoundaryMomentKernels

/-- In the Gamma family, the normalized moment-ratio scale has the manuscript closed form. -/
theorem gamma_momentRatioScale_eq {a : ℝ} (ha : -(1 / 2 : ℝ) < a) {k : ℕ} (hk : 1 ≤ k) :
    momentRatioScale (gammaFullSupportWeight a ha) k =
      1 + a / momentA k := by
  have hprev : I (gammaFullSupportWeight a ha) (k - 1) ≠ 0 :=
    ne_of_gt ((gammaFullSupportWeight a ha).momentPositive (k - 1))
  have hA : momentA k ≠ 0 := ne_of_gt (momentA_pos hk)
  have hrec := gamma_I_succ ha (k - 1)
  have hidx : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hidx, gammaAlpha_pred hk] at hrec
  rw [momentRatioScale, hrec]
  field_simp [hprev, hA]
  rw [momentA, gammaAlpha]
  ring

/-- Exact relative moment curvature from manuscript Corollary 2.9. -/
theorem gamma_momentCurvature_eq {a : ℝ} (ha : -(1 / 2 : ℝ) < a) {k : ℕ} (hk : 1 ≤ k) :
    momentCurvature (gammaFullSupportWeight a ha) k =
      16 * a /
        (((2 : ℝ) * (k : ℝ) - 1) * ((2 : ℝ) * (k : ℝ) + 1) *
          ((2 : ℝ) * (k : ℝ) + 3)) := by
  have hk1 : 1 ≤ k + 1 := by omega
  have hk2 : 1 ≤ k + 2 := by omega
  rw [momentCurvature, gamma_momentRatioScale_eq ha hk,
    gamma_momentRatioScale_eq ha hk1, gamma_momentRatioScale_eq ha hk2]
  rw [momentA, momentA, momentA]
  push_cast
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1 : (k : ℝ) - 1 / 2 ≠ 0 := by linarith
  have h2 : (k : ℝ) + 1 - 1 / 2 ≠ 0 := by linarith
  have h3 : (k : ℝ) + 2 - 1 / 2 ≠ 0 := by linarith
  field_simp [h1, h2, h3]
  ring

/-- Positive Gamma shape parameter gives strictly positive relative moment curvature. -/
theorem gamma_momentCurvature_pos {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) :
    0 < momentCurvature (gammaFullSupportWeight a (by linarith)) k := by
  rw [gamma_momentCurvature_eq (by linarith) hk]
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden :
      0 < ((2 : ℝ) * (k : ℝ) - 1) * ((2 : ℝ) * (k : ℝ) + 1) *
        ((2 : ℝ) * (k : ℝ) + 3) := by positivity
  exact div_pos (mul_pos (by norm_num) ha) hden

/-- Logarithmic profile of the Gamma weight on the positive half-line. -/
def gammaLogProfile (a y : ℝ) : ℝ := a * Real.log y - y

/-- The logarithmic Gamma profile has second derivative `-a/y²`. -/
theorem gammaLogProfile_second_derivative (a : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x => a / x - 1) (-a / y ^ 2) y := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  convert (hasDerivAt_const_div y a).sub_const 1 using 1 <;> field_simp [hy0] <;> ring

/-- For `a>0`, the logarithmic Gamma profile has strictly negative second derivative. -/
theorem gammaLogProfile_second_derivative_neg {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    -a / y ^ 2 < 0 := by
  exact div_neg_of_neg_of_pos (neg_neg_of_pos ha) (sq_pos_of_pos hy)

/-- The concrete reversed-crossing example from manuscript Corollary 2.8. -/
theorem gamma_a_one_reversed_crossing :
    uStar (gammaFullSupportWeight 1 (by norm_num)) 1 = 15 / 2 ∧
    uStar (gammaFullSupportWeight 1 (by norm_num)) 2 = 35 / 6 ∧
    uStar (gammaFullSupportWeight 1 (by norm_num)) 2 <
      uStar (gammaFullSupportWeight 1 (by norm_num)) 1 := by
  have h1 := gamma_uStar_eq (a := (1 : ℝ)) (by norm_num) (k := 1) (by norm_num)
  have h2 := gamma_uStar_eq (a := (1 : ℝ)) (by norm_num) (k := 2) (by norm_num)
  norm_num [gammaCrossing] at h1 h2 ⊢
  exact ⟨h1, h2, by linarith⟩

end CrossBoundaryMomentKernels
