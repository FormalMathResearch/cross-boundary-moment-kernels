import CrossBoundaryMomentKernels.GammaRecurrence

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace CrossBoundaryMomentKernels

/-- The explicit manuscript crossing candidate for the Gamma family. -/
def gammaCrossing (a : ℝ) (k : ℕ) : ℝ :=
  (((2 : ℝ) * (k : ℝ) + 3) / ((2 : ℝ) * (k : ℝ) - 1)) *
    ((k : ℝ) + a - (1 / 2 : ℝ))

lemma gammaAlpha_pred {a : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    gammaAlpha a (k - 1) = gammaAlpha a k - 1 := by
  rw [gammaAlpha, gammaAlpha]
  rw [Nat.cast_sub hk]
  norm_num
  ring

/-- Exact determinant formula from manuscript Theorem 2.7. -/
theorem gamma_K_eq {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k : ℕ) {u : ℝ}
    (hu : 0 ≤ u) :
    K (gammaFullSupportWeight a ha) k u =
      I (gammaFullSupportWeight a ha) k * u ^ (gammaAlpha a k) * Real.exp (-u) := by
  rw [K, gamma_I_succ ha k, gamma_J_succ ha k hu]
  ring

/-- The next Gamma determinant is obtained by multiplication by `α_k u`. -/
theorem gamma_K_succ_eq {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k : ℕ) {u : ℝ}
    (hu : 0 < u) :
    K (gammaFullSupportWeight a ha) (k + 1) u =
      gammaAlpha a k * u * K (gammaFullSupportWeight a ha) k u := by
  rw [gamma_K_eq ha (k + 1) hu.le, gamma_K_eq ha k hu.le,
    gamma_I_succ ha k, gammaAlpha_succ]
  rw [Real.rpow_add hu]
  norm_num
  ring

/-- The normalization scale `τ_k` in closed Gamma form. -/
theorem gamma_tau_eq {a : ℝ} (ha : -(1 / 2 : ℝ) < a) {k : ℕ} (hk : 1 ≤ k) :
    tau (gammaFullSupportWeight a ha) k =
      gammaAlpha a k * gammaCrossing a k := by
  let h := gammaFullSupportWeight a ha
  have hIk : 0 < I h k := h.momentPositive k
  have hIkm1 : 0 < I h (k - 1) := h.momentPositive (k - 1)
  have hIk1 : 0 < I h (k + 1) := h.momentPositive (k + 1)
  have hrec1 := gamma_I_succ ha k
  have hrec0 := gamma_I_succ ha (k - 1)
  have hidx : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hidx, gammaAlpha_pred hk] at hrec0
  change tau h k = gammaAlpha a k * gammaCrossing a k
  rw [tau, N, N, gammaCrossing]
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
  field_simp [ne_of_gt hIk, ne_of_gt hIkm1, ne_of_gt hIk1]
  rw [hrec1, hrec0]
  ring

/-- The explicit Gamma crossing is strictly positive at every manuscript index. -/
lemma gammaCrossing_pos {a : ℝ} (ha : -(1 / 2 : ℝ) < a) {k : ℕ} (hk : 1 ≤ k) :
    0 < gammaCrossing a k := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [gammaCrossing]
  have hden : 0 < (2 : ℝ) * (k : ℝ) - 1 := by linarith
  have hnum : 0 < (2 : ℝ) * (k : ℝ) + 3 := by linarith
  have hshape : 0 < (k : ℝ) + a - (1 / 2 : ℝ) := by linarith
  exact mul_pos (div_pos hnum hden) hshape

/-- Exact unnormalized crossing-kernel formula from manuscript Theorem 2.7. -/
theorem gamma_R_eq {a : ℝ} (ha : -(1 / 2 : ℝ) < a) {k : ℕ} (hk : 1 ≤ k) {u : ℝ}
    (hu : 0 < u) :
    R (gammaFullSupportWeight a ha) k u =
      2 * I (gammaFullSupportWeight a ha) (k + 1) *
        u ^ (gammaAlpha a k) * Real.exp (-u) * (gammaCrossing a k - u) := by
  have hK := gamma_K_eq ha k hu.le
  have hKs := gamma_K_succ_eq ha k hu
  have hI := gamma_I_succ ha k
  rw [R, gamma_tau_eq ha hk, hK, hKs, hI]
  ring

/-- The abstract canonical crossing equals the explicit Gamma crossing. -/
theorem gamma_uStar_eq {a : ℝ} (ha : -(1 / 2 : ℝ) < a) {k : ℕ} (hk : 1 ≤ k) :
    uStar (gammaFullSupportWeight a ha) k = gammaCrossing a k := by
  let h := gammaFullSupportWeight a ha
  have hgpos : 0 < gammaCrossing a k := gammaCrossing_pos ha hk
  have hzero : R h k (gammaCrossing a k) = 0 := by
    rw [gamma_R_eq ha hk hgpos]
    ring
  have heq := (R_eq_zero_iff_uStar h hk hgpos).mp hzero
  exact heq.symm

/-- Exact normalized crossing-kernel formula from manuscript Theorem 2.7. -/
theorem gamma_Rhat_eq {a : ℝ} (ha : -(1 / 2 : ℝ) < a) {k : ℕ} (hk : 1 ≤ k) {u : ℝ}
    (hu : 0 < u) :
    Rhat (gammaFullSupportWeight a ha) k u =
      2 * u ^ (gammaAlpha a k) * Real.exp (-u) /
        (((2 : ℝ) * (k : ℝ) + 1) * ((2 : ℝ) * (k : ℝ) + 3) *
          I (gammaFullSupportWeight a ha) k) *
        (gammaCrossing a k - u) := by
  let h := gammaFullSupportWeight a ha
  have hIk : I h k ≠ 0 := ne_of_gt (h.momentPositive k)
  have hIk1 : I h (k + 1) ≠ 0 := ne_of_gt (h.momentPositive (k + 1))
  have hR := gamma_R_eq ha hk hu
  change R h k u / N h (k + 1) = _
  rw [hR, N]
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
  field_simp [hIk, hIk1]
  ring

/-- Exact normalized adjacent ratio from manuscript Theorem 2.7. -/
theorem gamma_Z_succ_div_Z {a : ℝ} (ha : -(1 / 2 : ℝ) < a) {k : ℕ} (hk : 1 ≤ k)
    {u : ℝ} (hu : 0 < u) :
    Z (gammaFullSupportWeight a ha) (k + 1) u /
        Z (gammaFullSupportWeight a ha) k u =
      u / gammaCrossing a k := by
  let h := gammaFullSupportWeight a ha
  have hZ : 0 < Z h k u := Z_pos h hk hu
  have hK : K h k u ≠ 0 := ne_of_gt (K_pos h k hu)
  have hN : N h k ≠ 0 := ne_of_gt (N_pos h hk)
  have hNs : N h (k + 1) ≠ 0 := ne_of_gt (N_pos h (by omega))
  have hcross : gammaCrossing a k ≠ 0 := ne_of_gt (gammaCrossing_pos ha hk)
  rw [Z, Z, gamma_K_succ_eq ha k hu, ← tau, gamma_tau_eq ha hk]
  field_simp [hK, hN, hNs, hcross]
  ring

/-- Difference of consecutive explicit Gamma crossings. -/
theorem gammaCrossing_succ_sub {a : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    gammaCrossing a (k + 1) - gammaCrossing a k =
      (4 * (k : ℝ) ^ 2 - 8 * a - 1) /
        (((2 : ℝ) * (k : ℝ) - 1) * ((2 : ℝ) * (k : ℝ) + 1)) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [gammaCrossing, gammaCrossing]
  push_cast
  have h1 : (2 : ℝ) * (k : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (2 : ℝ) * (k : ℝ) + 1 ≠ 0 := by linarith
  field_simp [h1, h2]
  ring

/-- Sharp adjacent-crossing threshold in the Gamma family. -/
theorem gamma_crossing_order_iff {a : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    gammaCrossing a k < gammaCrossing a (k + 1) ↔
      a < (4 * (k : ℝ) ^ 2 - 1) / 8 := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden :
      0 < ((2 : ℝ) * (k : ℝ) - 1) * ((2 : ℝ) * (k : ℝ) + 1) := by
    exact mul_pos (by linarith) (by linarith)
  have hdiff := gammaCrossing_succ_sub (a := a) hk
  rw [← sub_pos, hdiff]
  rw [div_pos_iff hden]
  constructor
  · intro hnum
    linarith
  · intro ha
    linarith

/-- Manuscript Theorem 2.7 crossing threshold for the abstract canonical crossings. -/
theorem gamma_uStar_order_iff {a : ℝ} (ha : -(1 / 2 : ℝ) < a) {k : ℕ} (hk : 1 ≤ k) :
    uStar (gammaFullSupportWeight a ha) k <
        uStar (gammaFullSupportWeight a ha) (k + 1) ↔
      a < (4 * (k : ℝ) ^ 2 - 1) / 8 := by
  rw [gamma_uStar_eq ha hk, gamma_uStar_eq ha (by omega)]
  exact gamma_crossing_order_iff hk

/-- **Headline explicit Gamma model (core of manuscript Theorem 2.7).** -/
theorem gamma_model_headline {a : ℝ} (ha : -(1 / 2 : ℝ) < a) {k : ℕ} (hk : 1 ≤ k)
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
        Z (gammaFullSupportWeight a ha) k u = u / gammaCrossing a k := by
  have hI : I (gammaFullSupportWeight a ha) k = Real.Gamma (gammaAlpha a k) := by
    change I (gammaModelWeight a) k = Real.Gamma (gammaAlpha a k)
    exact gamma_I_eq_Gamma ha k
  have hK := gamma_K_eq ha k hu.le
  have huStar := gamma_uStar_eq ha hk
  have hR := gamma_R_eq ha hk hu
  have hRhat := gamma_Rhat_eq ha hk hu
  have hZ := gamma_Z_succ_div_Z ha hk hu
  exact ⟨hI, hK, huStar, hR, hRhat, hZ⟩

end CrossBoundaryMomentKernels
