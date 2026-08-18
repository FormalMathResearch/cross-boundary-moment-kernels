import CrossBoundaryMomentKernels.SizeBiasVariance

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace CrossBoundaryMomentKernels

/-- The local relative curvature
`Λ_k(u) = K_k(u) K_{k+2}(u) / K_{k+1}(u)^2` from manuscript Theorem 2.3. -/
def Lambda (h : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  K h k u * K h (k + 2) u / (K h (k + 1) u) ^ 2

/-- The normalization curvature
`Ω_k = N_k N_{k+2} / N_{k+1}^2` from manuscript Theorem 2.3. -/
def Omega (h : ℝ → ℝ) (k : ℕ) : ℝ :=
  N h k * N h (k + 2) / (N h (k + 1)) ^ 2

/-- The canonical crossing point is strictly positive. -/
lemma uStar_pos
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    0 < uStar h k := by
  exact lt_trans (xiMinus_pos h hk) (uStar_spec h hk).1.1

/-- Factorization used at the start of the manuscript proof of Theorem 2.3:
`R_k = 2 K_k (τ_k - M_k)`. -/
theorem R_eq_two_K_mul_tau_sub_mean
    (h : FullSupportMomentWeight) {k : ℕ} (_hk : 1 ≤ k) {u : ℝ} (hu : 0 < u) :
    R h k u = 2 * K h k u * (tau h k - crossBoundaryMean h k u) := by
  have hK : K h k u ≠ 0 := ne_of_gt (K_pos h k hu)
  rw [R, crossBoundaryMean_eq_K_ratio h k hu]
  field_simp [hK]

/-- Positivity of the crossing kernel is equivalent to the mean lying below the global scale. -/
theorem R_pos_iff_mean_lt_tau
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 < u) :
    0 < R h k u ↔ crossBoundaryMean h k u < tau h k := by
  rw [R_eq_two_K_mul_tau_sub_mean h hk hu]
  have hcoef : 0 < 2 * K h k u := mul_pos (by norm_num) (K_pos h k hu)
  constructor
  · intro hprod
    have hdiff : 0 < tau h k - crossBoundaryMean h k u :=
      pos_of_mul_pos_right hprod hcoef.le
    exact sub_pos.mp hdiff
  · intro hlt
    exact mul_pos hcoef (sub_pos.mpr hlt)

/-- Negativity of the crossing kernel is equivalent to the mean lying above the global scale. -/
theorem R_neg_iff_tau_lt_mean
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 < u) :
    R h k u < 0 ↔ tau h k < crossBoundaryMean h k u := by
  rw [R_eq_two_K_mul_tau_sub_mean h hk hu]
  have hcoef : 0 < 2 * K h k u := mul_pos (by norm_num) (K_pos h k hu)
  constructor
  · intro hprod
    have hdiff : tau h k - crossBoundaryMean h k u < 0 :=
      neg_of_mul_neg_right hprod hcoef.le
    exact sub_neg.mp hdiff
  · intro hlt
    exact mul_neg_of_pos_of_neg hcoef (sub_neg.mpr hlt)

/-- Zero of the crossing kernel is equivalent to exact mean/scale matching. -/
theorem R_eq_zero_iff_mean_eq_tau
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 < u) :
    R h k u = 0 ↔ crossBoundaryMean h k u = tau h k := by
  rw [R_eq_two_K_mul_tau_sub_mean h hk hu]
  have hcoef : 2 * K h k u ≠ 0 := ne_of_gt (mul_pos (by norm_num) (K_pos h k hu))
  constructor
  · intro hprod
    have hdiff : tau h k - crossBoundaryMean h k u = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hcoef
    exact (sub_eq_zero.mp hdiff).symm
  · intro heq
    simp [heq]

/-- The crossing kernel in normalized determinant coordinates. -/
theorem R_eq_two_N_succ_mul_Z_sub_Z
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) (u : ℝ) :
    R h k u = 2 * N h (k + 1) * (Z h k u - Z h (k + 1) u) := by
  have hNk : N h k ≠ 0 := ne_of_gt (N_pos h hk)
  have hNk1 : N h (k + 1) ≠ 0 := ne_of_gt (N_pos h (by omega))
  rw [R, tau, Z, Z]
  field_simp [hNk, hNk1]

/-- At the canonical crossing, the multiplicative mean matches `τ_k`. -/
theorem crossBoundaryMean_uStar_eq_tau
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    crossBoundaryMean h k (uStar h k) = tau h k := by
  have hu : 0 < uStar h k := uStar_pos h hk
  exact (R_eq_zero_iff_mean_eq_tau h hk hu).mp (uStar_spec h hk).2

/-- At the canonical crossing, two adjacent normalized determinants coincide. -/
theorem Z_uStar_eq_Z_succ
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    Z h k (uStar h k) = Z h (k + 1) (uStar h k) := by
  have hN : 0 < N h (k + 1) := N_pos h (by omega)
  have hR := R_eq_two_N_succ_mul_Z_sub_Z h hk (uStar h k)
  rw [(uStar_spec h hk).2] at hR
  nlinarith

/-- The common normalized determinant value at the crossing is positive. -/
theorem Z_uStar_pos
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    0 < Z h k (uStar h k) :=
  Z_pos h hk (uStar_pos h hk)

/-- `Λ_k` is one plus the squared coefficient of variation of the cross-boundary product law. -/
theorem Lambda_eq_one_add_variance_div_mean_sq
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    Lambda h k u =
      1 + crossBoundaryVariance h k u / (crossBoundaryMean h k u) ^ 2 := by
  have hK : K h k u ≠ 0 := ne_of_gt (K_pos h k hu)
  have hK1 : K h (k + 1) u ≠ 0 := ne_of_gt (K_pos h (k + 1) hu)
  rw [Lambda, crossBoundaryVariance_eq_K h k hu,
    crossBoundaryMean_eq_K_ratio h k hu]
  field_simp [hK, hK1]
  ring

/-- Universal strict relative log-convexity of the unnormalized `K` hierarchy. -/
theorem one_lt_Lambda
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    1 < Lambda h k u := by
  have hden : 0 < (K h (k + 1) u) ^ 2 := sq_pos_of_pos (K_pos h (k + 1) hu)
  have hlog := strict_crossBoundary_K_logConvexity h k hu
  rw [Lambda]
  exact (lt_div_iff₀ hden).2 (by simpa using hlog)

/-- The normalization curvature is the ratio of consecutive `τ` scales. -/
theorem Omega_eq_tau_succ_div_tau
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    Omega h k = tau h (k + 1) / tau h k := by
  have hNk : N h k ≠ 0 := ne_of_gt (N_pos h hk)
  have hNk1 : N h (k + 1) ≠ 0 := ne_of_gt (N_pos h (by omega))
  have hNk2 : N h (k + 2) ≠ 0 := ne_of_gt (N_pos h (by omega))
  rw [Omega, tau, tau]
  field_simp [hNk, hNk1, hNk2]

/-- `Ω_k` is positive at every manuscript index. -/
theorem Omega_pos
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    0 < Omega h k := by
  rw [Omega_eq_tau_succ_div_tau h hk]
  exact div_pos (tau_pos h (by omega)) (tau_pos h hk)

/-- Exact local/global curvature identity from the discussion after Theorem 2.3. -/
theorem Z_curvature_ratio_eq_Lambda_div_Omega
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 < u) :
    Z h k u * Z h (k + 2) u / (Z h (k + 1) u) ^ 2 =
      Lambda h k u / Omega h k := by
  have hNk : N h k ≠ 0 := ne_of_gt (N_pos h hk)
  have hNk1 : N h (k + 1) ≠ 0 := ne_of_gt (N_pos h (by omega))
  have hNk2 : N h (k + 2) ≠ 0 := ne_of_gt (N_pos h (by omega))
  have hK : K h k u ≠ 0 := ne_of_gt (K_pos h k hu)
  have hK1 : K h (k + 1) u ≠ 0 := ne_of_gt (K_pos h (k + 1) hu)
  have hK2 : K h (k + 2) u ≠ 0 := ne_of_gt (K_pos h (k + 2) hu)
  rw [Z, Z, Z, Lambda, Omega]
  field_simp [hNk, hNk1, hNk2, hK, hK1, hK2]

end CrossBoundaryMomentKernels
