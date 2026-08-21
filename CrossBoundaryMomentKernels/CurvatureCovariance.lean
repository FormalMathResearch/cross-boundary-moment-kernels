import CrossBoundaryMomentKernels.CurvatureTiltedMeasure

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- The next-index form of the manuscript identity
`E_k[V'(Y)] = 1/s_k`, using the `b_k` specialization of Lemma 5.1. -/
theorem CurvaturePairingHypotheses.curvatureTilted_succ_expectation_deriv
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    ∫ y, deriv V y ∂curvatureTiltedMeasure h (k + 1) =
      1 / momentRatioScale h (k + 1) := by
  rw [integral_curvatureTiltedMeasure]
  have hEq :
      (fun y : ℝ ↦ curvatureTiltedDensity h (k + 1) y * deriv V y) =ᵐ[
        volume.restrict (Ioi (0 : ℝ))]
      (fun y : ℝ ↦ (I h (k + 1))⁻¹ *
        (y ^ momentB k * deriv V y * h y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simp only [curvatureTiltedDensity, momentIntegrand, halfExponent, momentB,
      Real.rpow_eq_pow]
    push_cast
    ring_nf
  rw [integral_congr_ae hEq, integral_const_mul, H.ibp_at_B]
  rw [momentRatioScale, ← momentB_eq_A_succ]
  have hk : k + 1 - 1 = k := by omega
  rw [hk]
  field_simp [ne_of_gt (h.momentPositive k), ne_of_gt (h.momentPositive (k + 1))]

/-- The next-index mean identity
`E_{k+1}[Y] = I_{k+2}/I_{k+1} = c_k s_{k+2}`. -/
theorem CurvaturePairingHypotheses.curvatureTilted_succ_expectation_id
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (_H : CurvaturePairingHypotheses h V k) :
    ∫ y, y ∂curvatureTiltedMeasure h (k + 1) =
      momentC k * momentRatioScale h (k + 2) := by
  rw [curvatureTilted_expectation_id_eq_I_ratio]
  rw [momentRatioScale, ← momentC_eq_A_add_two]
  have hk : k + 2 - 1 = k + 1 := by omega
  rw [hk]
  have hC : momentC k ≠ 0 := by
    rw [momentC]
    positivity
  field_simp [hC, ne_of_gt (h.momentPositive (k + 1))]

/-- The next-index mixed-moment identity
`E_{k+1}[Y V'(Y)] = c_k`. -/
theorem CurvaturePairingHypotheses.curvatureTilted_succ_expectation_id_mul_deriv
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    ∫ y, y * deriv V y ∂curvatureTiltedMeasure h (k + 1) = momentC k := by
  rw [integral_curvatureTiltedMeasure]
  have hEq :
      (fun y : ℝ ↦ curvatureTiltedDensity h (k + 1) y * (y * deriv V y)) =ᵐ[
        volume.restrict (Ioi (0 : ℝ))]
      (fun y : ℝ ↦ (I h (k + 1))⁻¹ *
        (y ^ momentC k * deriv V y * h y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hs := momentIntegrand_succ h (k + 1) hy
    calc
      curvatureTiltedDensity h (k + 1) y * (y * deriv V y) =
          (I h (k + 1))⁻¹ *
            ((y * momentIntegrand h (k + 1) y) * deriv V y) := by
              rw [curvatureTiltedDensity]
              ring
      _ = (I h (k + 1))⁻¹ *
          (momentIntegrand h (k + 1 + 1) y * deriv V y) := by rw [← hs]
      _ = (I h (k + 1))⁻¹ * (y ^ momentC k * deriv V y * h y) := by
        simp only [momentIntegrand, halfExponent, momentC, Real.rpow_eq_pow]
        push_cast
        ring_nf
  rw [integral_congr_ae hEq, integral_const_mul, H.ibp_at_C]
  field_simp [ne_of_gt (h.momentPositive (k + 1))]

/-- The next-index covariance formula
`C_{k+1} = c_k (1 - s_{k+2}/s_{k+1})`. -/
theorem CurvaturePairingHypotheses.curvatureCovariance_succ_eq
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    curvatureCovariance h V (k + 1) =
      momentC k *
        (1 - momentRatioScale h (k + 2) / momentRatioScale h (k + 1)) := by
  rw [curvatureCovariance, H.curvatureTilted_succ_expectation_id_mul_deriv,
    H.curvatureTilted_succ_expectation_id, H.curvatureTilted_succ_expectation_deriv]
  have hs : momentRatioScale h (k + 1) ≠ 0 := by
    rw [momentRatioScale]
    have hk : k + 1 - 1 = k := by omega
    rw [hk]
    exact div_ne_zero (ne_of_gt (h.momentPositive (k + 1)))
      (mul_ne_zero (ne_of_gt (momentA_pos (by omega)))
        (ne_of_gt (h.momentPositive k)))
  field_simp [hs]

/-- The next-index first-difference identity
`s_{k+1} - s_{k+2} = (s_{k+1}/c_k) C_{k+1}`. -/
theorem CurvaturePairingHypotheses.momentRatioScale_succ_sub_add_two_eq_covariance
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    momentRatioScale h (k + 1) - momentRatioScale h (k + 2) =
      (momentRatioScale h (k + 1) / momentC k) * curvatureCovariance h V (k + 1) := by
  rw [H.curvatureCovariance_succ_eq]
  have hs : momentRatioScale h (k + 1) ≠ 0 := by
    rw [momentRatioScale]
    have hk : k + 1 - 1 = k := by omega
    rw [hk]
    exact div_ne_zero (ne_of_gt (h.momentPositive (k + 1)))
      (mul_ne_zero (ne_of_gt (momentA_pos (by omega)))
        (ne_of_gt (h.momentPositive k)))
  have hC : momentC k ≠ 0 := by
    rw [momentC]
    positivity
  field_simp [hs, hC]

/-- The covariance decomposition printed in manuscript Section 5:
`κ_k = (s_k/b_k) C_k - (s_{k+1}/c_k) C_{k+1}`. -/
theorem CurvaturePairingHypotheses.momentCurvature_eq_covariance_difference
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    momentCurvature h k =
      (momentRatioScale h k / momentB k) * curvatureCovariance h V k -
      (momentRatioScale h (k + 1) / momentC k) * curvatureCovariance h V (k + 1) := by
  rw [momentCurvature]
  calc
    momentRatioScale h k - 2 * momentRatioScale h (k + 1) + momentRatioScale h (k + 2) =
        (momentRatioScale h k - momentRatioScale h (k + 1)) -
          (momentRatioScale h (k + 1) - momentRatioScale h (k + 2)) := by ring
    _ = (momentRatioScale h k / momentB k) * curvatureCovariance h V k -
        (momentRatioScale h (k + 1) / momentC k) * curvatureCovariance h V (k + 1) := by
      rw [H.momentRatioScale_sub_succ_eq_covariance,
        H.momentRatioScale_succ_sub_add_two_eq_covariance]

end CrossBoundaryMomentKernels
