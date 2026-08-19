import CrossBoundaryMomentKernels.GammaProductDistribution

noncomputable section

open MeasureTheory Set
open scoped ProbabilityTheory

namespace CrossBoundaryMomentKernels

/-- Equality occurs exactly at the sharp threshold in manuscript Theorem 2.7. -/
theorem gamma_uStar_eq_iff_threshold
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) {k : ℕ} (hk : 1 ≤ k) :
    uStar (gammaFullSupportWeight a ha) k =
        uStar (gammaFullSupportWeight a ha) (k + 1) ↔
      a = (4 * (k : ℝ) ^ 2 - 1) / 8 := by
  rw [gamma_uStar_eq ha hk, gamma_uStar_eq ha (by omega)]
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  let D : ℝ := ((2 : ℝ) * (k : ℝ) - 1) * ((2 : ℝ) * (k : ℝ) + 1)
  have hD : D ≠ 0 := by
    dsimp [D]
    have h1 : 0 < (2 : ℝ) * (k : ℝ) - 1 := by linarith
    have h2 : 0 < (2 : ℝ) * (k : ℝ) + 1 := by linarith
    exact ne_of_gt (mul_pos h1 h2)
  constructor
  · intro heq
    have hdiff :
        (4 * (k : ℝ) ^ 2 - 8 * a - 1) / D = 0 := by
      rw [← gammaCrossing_succ_sub (a := a) hk]
      linarith
    have hmul := congrArg (fun x : ℝ => x * D) hdiff
    rw [div_mul_cancel₀ _ hD, zero_mul] at hmul
    rw [eq_div_iff (by norm_num : (8 : ℝ) ≠ 0)]
    linarith
  · intro haeq
    have ha8 : a * 8 = 4 * (k : ℝ) ^ 2 - 1 := by
      exact (eq_div_iff (by norm_num : (8 : ℝ) ≠ 0)).mp haeq
    have hnum : 4 * (k : ℝ) ^ 2 - 8 * a - 1 = 0 := by
      linarith
    have hdiff : gammaCrossing a (k + 1) - gammaCrossing a k = 0 := by
      rw [gammaCrossing_succ_sub hk]
      change (4 * (k : ℝ) ^ 2 - 8 * a - 1) / D = 0
      rw [hnum, zero_div]
    linarith

/-- Reversed adjacent crossing order occurs exactly above the sharp threshold. -/
theorem gamma_uStar_reverse_order_iff
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) {k : ℕ} (hk : 1 ≤ k) :
    uStar (gammaFullSupportWeight a ha) (k + 1) <
        uStar (gammaFullSupportWeight a ha) k ↔
      (4 * (k : ℝ) ^ 2 - 1) / 8 < a := by
  constructor
  · intro hrev
    have hnotlt : ¬a < (4 * (k : ℝ) ^ 2 - 1) / 8 := by
      intro halt
      have hinc := (gamma_uStar_order_iff ha hk).2 halt
      linarith
    have hne : a ≠ (4 * (k : ℝ) ^ 2 - 1) / 8 := by
      intro heq
      have hcrossEq := (gamma_uStar_eq_iff_threshold ha hk).2 heq
      linarith
    have hle : (4 * (k : ℝ) ^ 2 - 1) / 8 ≤ a := le_of_not_gt hnotlt
    exact lt_of_le_of_ne hle (Ne.symm hne)
  · intro hthreshold
    rcases lt_trichotomy
        (uStar (gammaFullSupportWeight a ha) k)
        (uStar (gammaFullSupportWeight a ha) (k + 1)) with hinc | heq | hrev
    · have halt := (gamma_uStar_order_iff ha hk).1 hinc
      linarith
    · have haeq := (gamma_uStar_eq_iff_threshold ha hk).1 heq
      linarith
    · exact hrev

/-- **Manuscript Theorem 2.7 (Gamma model and sharpness), publication-facing form.**
This theorem merely packages the independently proved identities; it does not strengthen the
manuscript hypotheses. -/
theorem gamma_theorem_2_7
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) {k : ℕ} (hk : 1 ≤ k)
    {u : ℝ} (hu : 0 < u) :
    I (gammaFullSupportWeight a ha) k = Real.Gamma (gammaAlpha a k) ∧
    K (gammaFullSupportWeight a ha) k u =
      I (gammaFullSupportWeight a ha) k * u ^ (gammaAlpha a k) * Real.exp (-u) ∧
    uStar (gammaFullSupportWeight a ha) k = gammaCrossing a k ∧
    R (gammaFullSupportWeight a ha) k u =
      2 * I (gammaFullSupportWeight a ha) (k + 1) * u ^ (gammaAlpha a k) *
        Real.exp (-u) * (gammaCrossing a k - u) ∧
    Rhat (gammaFullSupportWeight a ha) k u =
      2 * u ^ (gammaAlpha a k) * Real.exp (-u) /
        (((2 : ℝ) * (k : ℝ) + 1) * ((2 : ℝ) * (k : ℝ) + 3) *
          I (gammaFullSupportWeight a ha) k) * (gammaCrossing a k - u) ∧
    Z (gammaFullSupportWeight a ha) (k + 1) u /
        Z (gammaFullSupportWeight a ha) k u = u / gammaCrossing a k ∧
    uStar (gammaFullSupportWeight a ha) (k + 1) -
        uStar (gammaFullSupportWeight a ha) k =
      (4 * (k : ℝ) ^ 2 - 8 * a - 1) /
        (((2 : ℝ) * (k : ℝ) - 1) * ((2 : ℝ) * (k : ℝ) + 1)) ∧
    (uStar (gammaFullSupportWeight a ha) k <
        uStar (gammaFullSupportWeight a ha) (k + 1) ↔
      a < (4 * (k : ℝ) ^ 2 - 1) / 8) ∧
    (uStar (gammaFullSupportWeight a ha) k =
        uStar (gammaFullSupportWeight a ha) (k + 1) ↔
      a = (4 * (k : ℝ) ^ 2 - 1) / 8) ∧
    (uStar (gammaFullSupportWeight a ha) (k + 1) <
        uStar (gammaFullSupportWeight a ha) k ↔
      (4 * (k : ℝ) ^ 2 - 1) / 8 < a) := by
  have hI : I (gammaFullSupportWeight a ha) k = Real.Gamma (gammaAlpha a k) := by
    change I (gammaModelWeight a) k = Real.Gamma (gammaAlpha a k)
    exact gamma_I_eq_Gamma ha k
  have hdiff :
      uStar (gammaFullSupportWeight a ha) (k + 1) -
          uStar (gammaFullSupportWeight a ha) k =
        (4 * (k : ℝ) ^ 2 - 8 * a - 1) /
          (((2 : ℝ) * (k : ℝ) - 1) * ((2 : ℝ) * (k : ℝ) + 1)) := by
    rw [gamma_uStar_eq ha (by omega), gamma_uStar_eq ha hk]
    exact gammaCrossing_succ_sub hk
  exact ⟨hI, gamma_K_eq ha k hu.le, gamma_uStar_eq ha hk,
    gamma_R_eq ha hk hu, gamma_Rhat_eq ha hk hu, gamma_Z_succ_div_Z ha hk hu,
    hdiff, gamma_uStar_order_iff ha hk, gamma_uStar_eq_iff_threshold ha hk,
    gamma_uStar_reverse_order_iff ha hk⟩

/-- **Manuscript Corollary 2.8, publication-facing form.** Positive Gamma shape exponent gives
strict log-concavity of `log h_a` on `(0,∞)`, while `a=1` supplies the stated reversed crossing. -/
theorem gamma_corollary_2_8 {a : ℝ} (ha : 0 < a) :
    StrictConcaveOn ℝ (Ioi (0 : ℝ)) (gammaLogProfile a) ∧
    uStar (gammaFullSupportWeight 1 (by norm_num)) 1 = 15 / 2 ∧
    uStar (gammaFullSupportWeight 1 (by norm_num)) 2 = 35 / 6 ∧
    uStar (gammaFullSupportWeight 1 (by norm_num)) 2 <
      uStar (gammaFullSupportWeight 1 (by norm_num)) 1 := by
  exact ⟨gammaLogProfile_strictConcaveOn_Ioi ha, gamma_a_one_reversed_crossing⟩

/-- **Manuscript Corollary 2.9, publication-facing form.** -/
theorem gamma_corollary_2_9
    {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) :
    momentRatioScale (gammaFullSupportWeight a (by linarith)) k =
        1 + a / momentA k ∧
    momentCurvature (gammaFullSupportWeight a (by linarith)) k =
        16 * a /
          (((2 : ℝ) * (k : ℝ) - 1) * ((2 : ℝ) * (k : ℝ) + 1) *
            ((2 : ℝ) * (k : ℝ) + 3)) ∧
    0 < momentCurvature (gammaFullSupportWeight a (by linarith)) k := by
  exact ⟨gamma_momentRatioScale_eq (by linarith) hk,
    gamma_momentCurvature_eq (by linarith) hk,
    gamma_momentCurvature_pos ha hk⟩

/-- **Manuscript Proposition 2.10 (Exact Gamma product law), publication-facing form.**
The first conjunct is equality of pushforward probability measures; the remaining two are the
mean and variance consequences printed in the manuscript. -/
theorem gamma_proposition_2_10
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    (crossBoundaryMeasure (gammaFullSupportWeight a ha) k u).map
        (gammaNormalizedProduct u) =
        ProbabilityTheory.gammaMeasure (gammaAlpha a k) 1 ∧
    crossBoundaryMean (gammaFullSupportWeight a ha) k u = gammaAlpha a k * u ∧
    crossBoundaryVariance (gammaFullSupportWeight a ha) k u = gammaAlpha a k * u ^ 2 := by
  exact ⟨gamma_normalizedProduct_map_eq_gammaMeasure ha k hu,
    gamma_crossBoundaryMean_eq ha k hu,
    gamma_crossBoundaryVariance_eq ha k hu⟩

/-- The final variance identity stated after manuscript Proposition 2.10. -/
theorem gamma_proposition_2_10_variance_at_crossing
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) {k : ℕ} (hk : 1 ≤ k) :
    crossBoundaryVariance (gammaFullSupportWeight a ha) k
        (uStar (gammaFullSupportWeight a ha) k) =
      (tau (gammaFullSupportWeight a ha) k) ^ 2 / gammaAlpha a k :=
  gamma_crossBoundaryVariance_at_uStar ha hk

end CrossBoundaryMomentKernels
