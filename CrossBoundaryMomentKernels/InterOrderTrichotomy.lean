import CrossBoundaryMomentKernels.InterOrderEquivalence

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace CrossBoundaryMomentKernels

/-- Equality version of the variance/curvature comparison in Theorem 2.3. -/
theorem variance_eq_reserve_iff_Lambda_eq_Omega
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    crossBoundaryVariance h k (uStar h k) =
        tau h k * (tau h (k + 1) - tau h k) ↔
      Lambda h k (uStar h k) = Omega h k := by
  have htau2 : 0 < (tau h k) ^ 2 := sq_pos_of_pos (tau_pos h hk)
  have htau2ne : (tau h k) ^ 2 ≠ 0 := ne_of_gt htau2
  have hL := Lambda_uStar_mul_tau_sq h hk
  have hO := Omega_mul_tau_sq h hk
  constructor
  · intro hvar
    have hscaled :
        (tau h k) ^ 2 + crossBoundaryVariance h k (uStar h k) =
          tau h k * tau h (k + 1) := by
      nlinarith
    have hmul :
        Lambda h k (uStar h k) * (tau h k) ^ 2 =
          Omega h k * (tau h k) ^ 2 := by
      rw [hL, hO]
      exact hscaled
    have hzero :
        (Lambda h k (uStar h k) - Omega h k) * (tau h k) ^ 2 = 0 := by
      nlinarith
    have hdiff : Lambda h k (uStar h k) - Omega h k = 0 :=
      (mul_eq_zero.mp hzero).resolve_right htau2ne
    exact sub_eq_zero.mp hdiff
  · intro hcurv
    have hmul :
        Lambda h k (uStar h k) * (tau h k) ^ 2 =
          Omega h k * (tau h k) ^ 2 := by
      rw [hcurv]
    rw [hL, hO] at hmul
    nlinarith

/-- Reversed inequality version of the variance/curvature comparison. -/
theorem variance_gt_reserve_iff_Lambda_gt_Omega
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    tau h k * (tau h (k + 1) - tau h k) <
        crossBoundaryVariance h k (uStar h k) ↔
      Omega h k < Lambda h k (uStar h k) := by
  have htau2 : 0 < (tau h k) ^ 2 := sq_pos_of_pos (tau_pos h hk)
  have hL := Lambda_uStar_mul_tau_sq h hk
  have hO := Omega_mul_tau_sq h hk
  constructor
  · intro hvar
    have hscaled :
        tau h k * tau h (k + 1) <
          (tau h k) ^ 2 + crossBoundaryVariance h k (uStar h k) := by
      nlinarith
    have hmul :
        Omega h k * (tau h k) ^ 2 <
          Lambda h k (uStar h k) * (tau h k) ^ 2 := by
      rw [hL, hO]
      exact hscaled
    have hgap :
        0 < (Lambda h k (uStar h k) - Omega h k) * (tau h k) ^ 2 := by
      nlinarith
    have hinner : 0 < Lambda h k (uStar h k) - Omega h k :=
      pos_of_mul_pos_left hgap htau2.le
    linarith
  · intro hcurv
    have hgap :
        0 < (Lambda h k (uStar h k) - Omega h k) * (tau h k) ^ 2 :=
      mul_pos (sub_pos.mpr hcurv) htau2
    have hmul :
        Omega h k * (tau h k) ^ 2 <
          Lambda h k (uStar h k) * (tau h k) ^ 2 := by
      nlinarith
    rw [hL, hO] at hmul
    nlinarith

/-- The next crossing kernel vanishes at the current crossing exactly in the equality case of
the size-bias reserve. -/
theorem R_succ_uStar_eq_zero_iff_variance_eq_reserve
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    R h (k + 1) (uStar h k) = 0 ↔
      crossBoundaryVariance h k (uStar h k) =
        tau h k * (tau h (k + 1) - tau h k) := by
  have hu : 0 < uStar h k := uStar_pos h hk
  have htau : 0 < tau h k := tau_pos h hk
  have htau_ne : tau h k ≠ 0 := ne_of_gt htau
  have hvar := variance_uStar_eq_tau_mul_mean_drift h hk
  rw [R_eq_zero_iff_mean_eq_tau h (k := k + 1) (by omega) hu]
  constructor
  · intro hmean
    rw [hvar, hmean]
  · intro hreserve
    rw [hvar] at hreserve
    have hzero :
        tau h k *
          (crossBoundaryMean h (k + 1) (uStar h k) - tau h (k + 1)) = 0 := by
      nlinarith
    have hdiff :
        crossBoundaryMean h (k + 1) (uStar h k) - tau h (k + 1) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left htau_ne
    exact sub_eq_zero.mp hdiff

/-- The equality of consecutive canonical crossings is exactly the equality case of the local/global
curvature comparison. -/
theorem crossing_eq_iff_Lambda_eq_Omega
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    uStar h k = uStar h (k + 1) ↔ Lambda h k (uStar h k) = Omega h k := by
  have hu : 0 < uStar h k := uStar_pos h hk
  have hzero :
      R h (k + 1) (uStar h k) = 0 ↔ uStar h k = uStar h (k + 1) :=
    R_eq_zero_iff_uStar h (k := k + 1) (by omega) hu
  exact hzero.symm.trans
    ((R_succ_uStar_eq_zero_iff_variance_eq_reserve h hk).trans
      (variance_eq_reserve_iff_Lambda_eq_Omega h hk))

/-- The reversed crossing order is exactly the reversed local/global curvature comparison. -/
theorem crossing_gt_iff_Lambda_gt_Omega
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    uStar h (k + 1) < uStar h k ↔ Omega h k < Lambda h k (uStar h k) := by
  constructor
  · intro hcross
    rcases lt_trichotomy (Lambda h k (uStar h k)) (Omega h k) with hlt | heq | hgt
    · have hforward := (crossing_order_iff_Lambda_lt_Omega h hk).mpr hlt
      linarith
    · have heqCross := (crossing_eq_iff_Lambda_eq_Omega h hk).mpr heq
      linarith
    · exact hgt
  · intro hcurv
    rcases lt_trichotomy (uStar h k) (uStar h (k + 1)) with hlt | heq | hgt
    · have hforward := (crossing_order_iff_Lambda_lt_Omega h hk).mp hlt
      linarith
    · have heqCurv := (crossing_eq_iff_Lambda_eq_Omega h hk).mp heq
      linarith
    · exact hgt

/-- **Exact inter-order trichotomy (manuscript Remark 4.1).** -/
theorem inter_order_curvature_trichotomy
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    (uStar h k < uStar h (k + 1) ↔ Lambda h k (uStar h k) < Omega h k) ∧
    (uStar h k = uStar h (k + 1) ↔ Lambda h k (uStar h k) = Omega h k) ∧
    (uStar h (k + 1) < uStar h k ↔ Omega h k < Lambda h k (uStar h k)) :=
  ⟨crossing_order_iff_Lambda_lt_Omega h hk,
    crossing_eq_iff_Lambda_eq_Omega h hk,
    crossing_gt_iff_Lambda_gt_Omega h hk⟩

/-- Equivalent variance-reserve trichotomy from manuscript Remark 4.1. -/
theorem inter_order_variance_trichotomy
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    (uStar h k < uStar h (k + 1) ↔
      crossBoundaryVariance h k (uStar h k) <
        tau h k * (tau h (k + 1) - tau h k)) ∧
    (uStar h k = uStar h (k + 1) ↔
      crossBoundaryVariance h k (uStar h k) =
        tau h k * (tau h (k + 1) - tau h k)) ∧
    (uStar h (k + 1) < uStar h k ↔
      tau h k * (tau h (k + 1) - tau h k) <
        crossBoundaryVariance h k (uStar h k)) := by
  have hlt := (uStar_lt_succ_iff_R_succ_pos h hk).trans
    (R_succ_uStar_pos_iff_variance_lt_reserve h hk)
  have heq := (crossing_eq_iff_Lambda_eq_Omega h hk).trans
    (variance_eq_reserve_iff_Lambda_eq_Omega h hk).symm
  have hgt := (crossing_gt_iff_Lambda_gt_Omega h hk).trans
    (variance_gt_reserve_iff_Lambda_gt_Omega h hk).symm
  exact ⟨hlt, heq, hgt⟩

/-- **Necessary normalization curvature for increasing crossing order (manuscript Theorem 2.4).**
Since `Λ_k(u) > 1` universally, `u_k^* < u_{k+1}^*` forces `Ω_k > 1`. -/
theorem crossing_order_implies_one_lt_Omega
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k)
    (horder : uStar h k < uStar h (k + 1)) :
    1 < Omega h k := by
  have hLambda : 1 < Lambda h k (uStar h k) := one_lt_Lambda h k (uStar_pos h hk)
  have hcurv : Lambda h k (uStar h k) < Omega h k :=
    (crossing_order_iff_Lambda_lt_Omega h hk).mp horder
  exact lt_trans hLambda hcurv

end CrossBoundaryMomentKernels
