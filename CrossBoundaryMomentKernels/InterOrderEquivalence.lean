import CrossBoundaryMomentKernels.InterOrder

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace CrossBoundaryMomentKernels

/-- Manuscript Theorem 2.3, step `(a) ↔ (b)`: crossing order is exactly the sign of the
next crossing kernel at the current canonical crossing. -/
theorem uStar_lt_succ_iff_R_succ_pos
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    uStar h k < uStar h (k + 1) ↔ 0 < R h (k + 1) (uStar h k) := by
  have hu : 0 < uStar h k := uStar_pos h hk
  constructor
  · intro hlt
    exact R_pos_before_uStar h (k := k + 1) (by omega) hu hlt
  · intro hR
    by_contra hnot
    have hle : uStar h (k + 1) ≤ uStar h k := le_of_not_gt hnot
    rcases hle.eq_or_lt with heq | hlt
    · have hzero : R h (k + 1) (uStar h (k + 1)) = 0 :=
        (uStar_spec h (k := k + 1) (by omega)).2
      rw [← heq] at hR
      linarith
    · have hneg : R h (k + 1) (uStar h k) < 0 :=
        R_neg_after_uStar h (k := k + 1) (by omega) hlt
      linarith

/-- Manuscript Theorem 2.3, step `(b) ↔ (c)`: at the matching point
`Z_k = Z_{k+1} > 0`, the sign of `R_{k+1}` is precisely strict local index
log-concavity of the normalized hierarchy. -/
theorem R_succ_uStar_pos_iff_Z_logConcave
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    0 < R h (k + 1) (uStar h k) ↔
      Z h k (uStar h k) * Z h (k + 2) (uStar h k) <
        (Z h (k + 1) (uStar h k)) ^ 2 := by
  have hZeq := Z_uStar_eq_Z_succ h hk
  have hZpos0 := Z_uStar_pos h hk
  have hZpos1 : 0 < Z h (k + 1) (uStar h k) := by
    rw [← hZeq]
    exact hZpos0
  have hRform :
      R h (k + 1) (uStar h k) =
        2 * N h (k + 2) *
          (Z h (k + 1) (uStar h k) - Z h (k + 2) (uStar h k)) := by
    simpa [Nat.add_assoc] using
      R_eq_two_N_succ_mul_Z_sub_Z h (k := k + 1) (by omega) (uStar h k)
  have hcoef : 0 < 2 * N h (k + 2) :=
    mul_pos (by norm_num) (N_pos h (by omega))
  rw [hRform]
  constructor
  · intro hprod
    have hdiff :
        0 < Z h (k + 1) (uStar h k) - Z h (k + 2) (uStar h k) :=
      pos_of_mul_pos_right hprod hcoef.le
    have hmul :
        0 < Z h (k + 1) (uStar h k) *
          (Z h (k + 1) (uStar h k) - Z h (k + 2) (uStar h k)) :=
      mul_pos hZpos1 hdiff
    rw [hZeq]
    nlinarith
  · intro hZ
    rw [hZeq] at hZ
    have hmul :
        0 < Z h (k + 1) (uStar h k) *
          (Z h (k + 1) (uStar h k) - Z h (k + 2) (uStar h k)) := by
      nlinarith
    have hdiff :
        0 < Z h (k + 1) (uStar h k) - Z h (k + 2) (uStar h k) :=
      pos_of_mul_pos_right hmul hZpos1.le
    exact mul_pos hcoef hdiff

/-- Manuscript Theorem 2.3, step `(b) ↔ (d)`, obtained directly from the already verified
Gram decomposition and positivity of its denominator. -/
theorem R_succ_uStar_pos_iff_gram_reserve_pos
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    0 < R h (k + 1) (uStar h k) ↔
      0 < truncatedVar h k (uStar h k) +
        crossingQ h (k + 1) (truncatedMu h k (uStar h k)) := by
  have hu : 0 < uStar h k := uStar_pos h hk
  have hI : 0 < I h (k + 2) := h.momentPositive (k + 2)
  have hJ : 0 < J h (k + 1) (uStar h k) := J_pos h (k + 1) hu
  have hden : 0 < 2 * I h (k + 2) * J h (k + 1) (uStar h k) := by positivity
  have hId := crossing_kernel_succ_gram_decomposition h hk hu
  constructor
  · intro hR
    have hquot :
        0 < R h (k + 1) (uStar h k) /
          (2 * I h (k + 2) * J h (k + 1) (uStar h k)) :=
      div_pos hR hden
    linarith
  · intro hG
    have hquot :
        0 < R h (k + 1) (uStar h k) /
          (2 * I h (k + 2) * J h (k + 1) (uStar h k)) := by
      linarith
    have hmul := mul_pos hquot hden
    rw [div_mul_cancel₀ _ (ne_of_gt hden)] at hmul
    exact hmul

/-- At the canonical crossing the variance is exactly `τ_k` times the increase of the
multiplicative mean. This is the algebraic bridge used in step `(b) ↔ (e)`. -/
lemma variance_uStar_eq_tau_mul_mean_drift
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    crossBoundaryVariance h k (uStar h k) =
      tau h k * (crossBoundaryMean h (k + 1) (uStar h k) - tau h k) := by
  have hu : 0 < uStar h k := uStar_pos h hk
  have htau : tau h k ≠ 0 := ne_of_gt (tau_pos h hk)
  have hdrift := crossBoundaryMean_succ_sub_eq_variance_div_mean h k hu
  rw [crossBoundaryMean_uStar_eq_tau h hk] at hdrift
  calc
    crossBoundaryVariance h k (uStar h k) =
        (crossBoundaryVariance h k (uStar h k) / tau h k) * tau h k := by
      exact (div_mul_cancel₀ _ htau).symm
    _ = (crossBoundaryMean h (k + 1) (uStar h k) - tau h k) * tau h k := by
      rw [← hdrift]
    _ = tau h k * (crossBoundaryMean h (k + 1) (uStar h k) - tau h k) := by ring

/-- Manuscript Theorem 2.3, step `(b) ↔ (e)`: the next crossing kernel is positive exactly
when local multiplicative variance fits inside the available global drift reserve. -/
theorem R_succ_uStar_pos_iff_variance_lt_reserve
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    0 < R h (k + 1) (uStar h k) ↔
      crossBoundaryVariance h k (uStar h k) <
        tau h k * (tau h (k + 1) - tau h k) := by
  have hu : 0 < uStar h k := uStar_pos h hk
  have htau : 0 < tau h k := tau_pos h hk
  have hvar := variance_uStar_eq_tau_mul_mean_drift h hk
  rw [R_pos_iff_mean_lt_tau h (k := k + 1) (by omega) hu]
  constructor
  · intro hmean
    rw [hvar]
    have hgap :
        0 < tau h k *
          (tau h (k + 1) - crossBoundaryMean h (k + 1) (uStar h k)) :=
      mul_pos htau (sub_pos.mpr hmean)
    nlinarith
  · intro hvarlt
    rw [hvar] at hvarlt
    have hgap :
        0 < tau h k *
          ((tau h (k + 1) - tau h k) -
            (crossBoundaryMean h (k + 1) (uStar h k) - tau h k)) := by
      nlinarith
    have hinner :
        0 < (tau h (k + 1) - tau h k) -
          (crossBoundaryMean h (k + 1) (uStar h k) - tau h k) :=
      pos_of_mul_pos_right hgap htau.le
    linarith

/-- Scaling identity for `Λ_k` at the canonical crossing. -/
lemma Lambda_uStar_mul_tau_sq
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    Lambda h k (uStar h k) * (tau h k) ^ 2 =
      (tau h k) ^ 2 + crossBoundaryVariance h k (uStar h k) := by
  have hu : 0 < uStar h k := uStar_pos h hk
  have htau : tau h k ≠ 0 := ne_of_gt (tau_pos h hk)
  rw [Lambda_eq_one_add_variance_div_mean_sq h k hu,
    crossBoundaryMean_uStar_eq_tau h hk]
  field_simp [htau]

/-- Scaling identity for the normalization curvature. -/
lemma Omega_mul_tau_sq
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    Omega h k * (tau h k) ^ 2 = tau h k * tau h (k + 1) := by
  have htau : tau h k ≠ 0 := ne_of_gt (tau_pos h hk)
  rw [Omega_eq_tau_succ_div_tau h hk]
  field_simp [htau]

/-- Manuscript Theorem 2.3, step `(e) ↔ (f)` in its compact curvature form. -/
theorem variance_lt_reserve_iff_Lambda_lt_Omega
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    crossBoundaryVariance h k (uStar h k) <
        tau h k * (tau h (k + 1) - tau h k) ↔
      Lambda h k (uStar h k) < Omega h k := by
  have htau2 : 0 < (tau h k) ^ 2 := sq_pos_of_pos (tau_pos h hk)
  have hL := Lambda_uStar_mul_tau_sq h hk
  have hO := Omega_mul_tau_sq h hk
  constructor
  · intro hvar
    have hscaled :
        (tau h k) ^ 2 + crossBoundaryVariance h k (uStar h k) <
          tau h k * tau h (k + 1) := by
      nlinarith
    have hmul :
        Lambda h k (uStar h k) * (tau h k) ^ 2 <
          Omega h k * (tau h k) ^ 2 := by
      rw [hL, hO]
      exact hscaled
    have hgap :
        0 < (Omega h k - Lambda h k (uStar h k)) * (tau h k) ^ 2 := by
      nlinarith
    have hinner : 0 < Omega h k - Lambda h k (uStar h k) :=
      pos_of_mul_pos_left hgap htau2.le
    linarith
  · intro hcurv
    have hgap :
        0 < (Omega h k - Lambda h k (uStar h k)) * (tau h k) ^ 2 :=
      mul_pos (sub_pos.mpr hcurv) htau2
    have hmul :
        Lambda h k (uStar h k) * (tau h k) ^ 2 <
          Omega h k * (tau h k) ^ 2 := by
      nlinarith
    rw [hL, hO] at hmul
    nlinarith

/-- Compact local/global curvature form of manuscript Theorem 2.3. -/
theorem crossing_order_iff_Lambda_lt_Omega
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    uStar h k < uStar h (k + 1) ↔ Lambda h k (uStar h k) < Omega h k :=
  (uStar_lt_succ_iff_R_succ_pos h hk).trans
    ((R_succ_uStar_pos_iff_variance_lt_reserve h hk).trans
      (variance_lt_reserve_iff_Lambda_lt_Omega h hk))

/-- **Six-way inter-order equivalence (manuscript Theorem 2.3).**

The five displayed equivalences below say that each of manuscript conditions `(b)`--`(f)`
is equivalent to condition `(a)`. Thus all six conditions are mutually equivalent. -/
theorem six_way_inter_order_equivalence
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    (uStar h k < uStar h (k + 1) ↔ 0 < R h (k + 1) (uStar h k)) ∧
    (uStar h k < uStar h (k + 1) ↔
      Z h k (uStar h k) * Z h (k + 2) (uStar h k) <
        (Z h (k + 1) (uStar h k)) ^ 2) ∧
    (uStar h k < uStar h (k + 1) ↔
      0 < truncatedVar h k (uStar h k) +
        crossingQ h (k + 1) (truncatedMu h k (uStar h k))) ∧
    (uStar h k < uStar h (k + 1) ↔
      crossBoundaryVariance h k (uStar h k) <
        tau h k * (tau h (k + 1) - tau h k)) ∧
    (uStar h k < uStar h (k + 1) ↔
      K h k (uStar h k) * K h (k + 2) (uStar h k) /
          (K h (k + 1) (uStar h k)) ^ 2 <
        N h k * N h (k + 2) / (N h (k + 1)) ^ 2) := by
  have hab := uStar_lt_succ_iff_R_succ_pos h hk
  have hac := hab.trans (R_succ_uStar_pos_iff_Z_logConcave h hk)
  have had := hab.trans (R_succ_uStar_pos_iff_gram_reserve_pos h hk)
  have hae := hab.trans (R_succ_uStar_pos_iff_variance_lt_reserve h hk)
  have haf := crossing_order_iff_Lambda_lt_Omega h hk
  exact ⟨hab, hac, had, hae, by simpa [Lambda, Omega] using haf⟩

end CrossBoundaryMomentKernels
