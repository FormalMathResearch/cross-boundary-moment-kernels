import CrossBoundaryMomentKernels.CurvaturePairingMoments

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace CrossBoundaryMomentKernels

/-- The real-valued density of the manuscript tilted law
`dP_k(y) = y^{a_k} h(y) / I_k dy` on `(0,∞)`. -/
def curvatureTiltedDensity
    (h : FullSupportMomentWeight) (k : ℕ) (y : ℝ) : ℝ :=
  (I h k)⁻¹ * momentIntegrand h k y

/-- The tilted law `P_k` used in manuscript Section 5. -/
def curvatureTiltedMeasure
    (h : FullSupportMomentWeight) (k : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun y ↦ ENNReal.ofReal (curvatureTiltedDensity h k y))

lemma curvatureTiltedDensity_integrable
    (h : FullSupportMomentWeight) (k : ℕ) :
    Integrable (curvatureTiltedDensity h k) (volume.restrict (Ioi (0 : ℝ))) := by
  change Integrable (fun y : ℝ => (I h k)⁻¹ * momentIntegrand h k y)
    (volume.restrict (Ioi (0 : ℝ)))
  exact (h.momentIntegrable k).const_mul (I h k)⁻¹

lemma curvatureTiltedDensity_nonneg_ae
    (h : FullSupportMomentWeight) (k : ℕ) :
    0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] curvatureTiltedDensity h k := by
  have hI : 0 ≤ (I h k)⁻¹ := inv_nonneg.mpr (h.momentPositive k).le
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact mul_nonneg hI (momentIntegrand_nonneg h k hy)

lemma integral_curvatureTiltedDensity
    (h : FullSupportMomentWeight) (k : ℕ) :
    ∫ y, curvatureTiltedDensity h k y ∂(volume.restrict (Ioi (0 : ℝ))) = 1 := by
  change ∫ y, (I h k)⁻¹ * momentIntegrand h k y
      ∂(volume.restrict (Ioi (0 : ℝ))) = 1
  rw [integral_const_mul]
  change (I h k)⁻¹ * I h k = 1
  exact inv_mul_cancel₀ (ne_of_gt (h.momentPositive k))

/-- The manuscript tilted density is normalized, so it really defines a probability measure. -/
theorem curvatureTiltedMeasure_isProbability
    (h : FullSupportMomentWeight) (k : ℕ) :
    IsProbabilityMeasure (curvatureTiltedMeasure h k) := by
  constructor
  rw [curvatureTiltedMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (curvatureTiltedDensity_integrable h k) (curvatureTiltedDensity_nonneg_ae h k)]
  rw [integral_curvatureTiltedDensity h k]
  simp

/-- Integration against `P_k` is normalized integration against `y^{a_k}h(y)`. -/
theorem integral_curvatureTiltedMeasure
    (h : FullSupportMomentWeight) (k : ℕ) (g : ℝ → ℝ) :
    ∫ y, g y ∂curvatureTiltedMeasure h k =
      ∫ y, curvatureTiltedDensity h k y * g y
        ∂(volume.restrict (Ioi (0 : ℝ))) := by
  have hdenInt := curvatureTiltedDensity_integrable h k
  have hmeas : AEMeasurable
      (fun y ↦ ENNReal.ofReal (curvatureTiltedDensity h k y))
      (volume.restrict (Ioi (0 : ℝ))) :=
    hdenInt.1.aemeasurable.ennreal_ofReal
  have htop : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))),
      ENNReal.ofReal (curvatureTiltedDensity h k y) < ∞ := by
    filter_upwards with y
    exact ENNReal.ofReal_lt_top
  rw [curvatureTiltedMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas htop]
  apply integral_congr_ae
  filter_upwards [curvatureTiltedDensity_nonneg_ae h k] with y hy
  simp [ENNReal.toReal_ofReal hy, smul_eq_mul]

/-- The first moment under `P_k` is the adjacent global moment ratio. -/
theorem curvatureTilted_expectation_id_eq_I_ratio
    (h : FullSupportMomentWeight) (k : ℕ) :
    ∫ y, y ∂curvatureTiltedMeasure h k = I h (k + 1) / I h k := by
  rw [integral_curvatureTiltedMeasure]
  have hEq :
      (fun y : ℝ ↦ curvatureTiltedDensity h k y * y) =ᵐ[
        volume.restrict (Ioi (0 : ℝ))]
      (fun y : ℝ ↦ (I h k)⁻¹ * momentIntegrand h (k + 1) y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [curvatureTiltedDensity, momentIntegrand_succ h k hy]
    ring
  rw [integral_congr_ae hEq, integral_const_mul]
  change (I h k)⁻¹ * I h (k + 1) = I h (k + 1) / I h k
  rw [div_eq_mul_inv]
  ring

/-- The manuscript identity `E_k[V'(Y)] = 1/s_k`. -/
theorem CurvaturePairingHypotheses.curvatureTilted_expectation_deriv
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    ∫ y, deriv V y ∂curvatureTiltedMeasure h k =
      1 / momentRatioScale h k := by
  rw [integral_curvatureTiltedMeasure]
  have hEq :
      (fun y : ℝ ↦ curvatureTiltedDensity h k y * deriv V y) =ᵐ[
        volume.restrict (Ioi (0 : ℝ))]
      (fun y : ℝ ↦ (I h k)⁻¹ *
        (y ^ momentA k * deriv V y * h y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simp only [curvatureTiltedDensity, momentIntegrand, momentA, halfExponent,
      Real.rpow_eq_pow]
    ring_nf
  rw [integral_congr_ae hEq, integral_const_mul, H.ibp_at_A]
  rw [momentRatioScale]
  field_simp [ne_of_gt (h.momentPositive k), ne_of_gt (h.momentPositive (k - 1)),
    ne_of_gt (momentA_pos H.index)]

/-- The manuscript identity `E_k[Y] = I_{k+1}/I_k = b_k s_{k+1}`. -/
theorem CurvaturePairingHypotheses.curvatureTilted_expectation_id
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (_H : CurvaturePairingHypotheses h V k) :
    ∫ y, y ∂curvatureTiltedMeasure h k =
      momentB k * momentRatioScale h (k + 1) := by
  rw [curvatureTilted_expectation_id_eq_I_ratio]
  rw [momentRatioScale, ← momentB_eq_A_succ]
  have hk : k + 1 - 1 = k := by omega
  rw [hk]
  have hB : momentB k ≠ 0 := by
    rw [momentB]
    positivity
  field_simp [hB, ne_of_gt (h.momentPositive k)]

/-- The manuscript identity `E_k[Y V'(Y)] = b_k`. -/
theorem CurvaturePairingHypotheses.curvatureTilted_expectation_id_mul_deriv
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    ∫ y, y * deriv V y ∂curvatureTiltedMeasure h k = momentB k := by
  rw [integral_curvatureTiltedMeasure]
  have hEq :
      (fun y : ℝ ↦ curvatureTiltedDensity h k y * (y * deriv V y)) =ᵐ[
        volume.restrict (Ioi (0 : ℝ))]
      (fun y : ℝ ↦ (I h k)⁻¹ *
        (y ^ momentB k * deriv V y * h y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hs := momentIntegrand_succ h k hy
    calc
      curvatureTiltedDensity h k y * (y * deriv V y) =
          (I h k)⁻¹ * ((y * momentIntegrand h k y) * deriv V y) := by
            rw [curvatureTiltedDensity]
            ring
      _ = (I h k)⁻¹ * (momentIntegrand h (k + 1) y * deriv V y) := by rw [← hs]
      _ = (I h k)⁻¹ * (y ^ momentB k * deriv V y * h y) := by
        simp only [momentIntegrand, halfExponent, momentB, Real.rpow_eq_pow]
        push_cast
        ring_nf
  rw [integral_congr_ae hEq, integral_const_mul, H.ibp_at_B]
  field_simp [ne_of_gt (h.momentPositive k)]

/-- The covariance `C_k = Cov_{P_k}(Y,V'(Y))` in the form used by the manuscript. -/
def curvatureCovariance
    (h : FullSupportMomentWeight) (V : ℝ → ℝ) (k : ℕ) : ℝ :=
  (∫ y, y * deriv V y ∂curvatureTiltedMeasure h k) -
    (∫ y, y ∂curvatureTiltedMeasure h k) *
      (∫ y, deriv V y ∂curvatureTiltedMeasure h k)

/-- Manuscript covariance formula
`C_k = b_k (1 - s_{k+1}/s_k)`. -/
theorem CurvaturePairingHypotheses.curvatureCovariance_eq
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    curvatureCovariance h V k =
      momentB k * (1 - momentRatioScale h (k + 1) / momentRatioScale h k) := by
  rw [curvatureCovariance, H.curvatureTilted_expectation_id_mul_deriv,
    H.curvatureTilted_expectation_id, H.curvatureTilted_expectation_deriv]
  have hs : momentRatioScale h k ≠ 0 := by
    rw [momentRatioScale]
    exact div_ne_zero (ne_of_gt (h.momentPositive k))
      (mul_ne_zero (ne_of_gt (momentA_pos H.index))
        (ne_of_gt (h.momentPositive (k - 1))))
  field_simp [hs]

/-- The first difference identity
`s_k - s_{k+1} = (s_k/b_k) C_k`. -/
theorem CurvaturePairingHypotheses.momentRatioScale_sub_succ_eq_covariance
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    momentRatioScale h k - momentRatioScale h (k + 1) =
      (momentRatioScale h k / momentB k) * curvatureCovariance h V k := by
  rw [H.curvatureCovariance_eq]
  have hs : momentRatioScale h k ≠ 0 := by
    rw [momentRatioScale]
    exact div_ne_zero (ne_of_gt (h.momentPositive k))
      (mul_ne_zero (ne_of_gt (momentA_pos H.index))
        (ne_of_gt (h.momentPositive (k - 1))))
  have hB : momentB k ≠ 0 := by
    rw [momentB]
    positivity
  field_simp [hs, hB]

end CrossBoundaryMomentKernels
