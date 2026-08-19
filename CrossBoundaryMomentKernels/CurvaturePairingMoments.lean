import CrossBoundaryMomentKernels.CurvaturePairing

noncomputable section

open MeasureTheory Set

namespace CrossBoundaryMomentKernels

/-- For `k ≥ 1`, the exponent below `a_k` is exactly the manuscript moment exponent at `k-1`. -/
lemma momentA_sub_one_eq_halfExponent_pred {k : ℕ} (hk : 1 ≤ k) :
    momentA k - 1 = halfExponent (k - 1) := by
  rw [momentA, halfExponent]
  rw [Nat.cast_sub hk]
  ring

/-- The exponent below `b_k` is exactly the manuscript moment exponent at `k`. -/
lemma momentB_sub_one_eq_halfExponent (k : ℕ) :
    momentB k - 1 = halfExponent k := by
  rw [momentB, halfExponent]
  ring

/-- The exponent below `c_k` is exactly the manuscript moment exponent at `k+1`. -/
lemma momentC_sub_one_eq_halfExponent_succ (k : ℕ) :
    momentC k - 1 = halfExponent (k + 1) := by
  rw [momentC, halfExponent]
  push_cast
  ring

/-- The first specialization printed immediately after manuscript Lemma 5.1. -/
theorem CurvaturePairingHypotheses.ibp_at_A
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    ∫ y in Ioi (0 : ℝ), y ^ (momentA k) * deriv V y * h y =
      momentA k * I h (k - 1) := by
  have hmoment :
      IntegrableOn (fun y : ℝ => y ^ (momentA k - 1) * h y) (Ioi 0) := by
    change Integrable (fun y : ℝ => y ^ (momentA k - 1) * h y)
      (volume.restrict (Ioi 0))
    apply (h.momentIntegrable (k - 1)).congr
    filter_upwards with y
    simp only [momentIntegrand, momentA_sub_one_eq_halfExponent_pred H.index,
      Real.rpow_eq_pow]
  have hibp := curvature_improper_integration_by_parts H (momentA_pos H.index) H.atA hmoment
  rw [momentA_sub_one_eq_halfExponent_pred H.index] at hibp
  simpa [I, momentIntegrand, Real.rpow_eq_pow] using hibp

/-- The second specialization printed immediately after manuscript Lemma 5.1. -/
theorem CurvaturePairingHypotheses.ibp_at_B
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    ∫ y in Ioi (0 : ℝ), y ^ (momentB k) * deriv V y * h y =
      momentB k * I h k := by
  have hBpos : 0 < momentB k := by
    rw [momentB_eq_A_succ]
    exact momentA_pos (by omega)
  have hmoment :
      IntegrableOn (fun y : ℝ => y ^ (momentB k - 1) * h y) (Ioi 0) := by
    change Integrable (fun y : ℝ => y ^ (momentB k - 1) * h y)
      (volume.restrict (Ioi 0))
    apply (h.momentIntegrable k).congr
    filter_upwards with y
    simp only [momentIntegrand, momentB_sub_one_eq_halfExponent, Real.rpow_eq_pow]
  have hibp := curvature_improper_integration_by_parts H hBpos H.atB hmoment
  rw [momentB_sub_one_eq_halfExponent] at hibp
  simpa [I, momentIntegrand, Real.rpow_eq_pow] using hibp

/-- The third specialization printed immediately after manuscript Lemma 5.1. -/
theorem CurvaturePairingHypotheses.ibp_at_C
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    ∫ y in Ioi (0 : ℝ), y ^ (momentC k) * deriv V y * h y =
      momentC k * I h (k + 1) := by
  have hCpos : 0 < momentC k := by
    rw [momentC_eq_A_add_two]
    exact momentA_pos (by omega)
  have hmoment :
      IntegrableOn (fun y : ℝ => y ^ (momentC k - 1) * h y) (Ioi 0) := by
    change Integrable (fun y : ℝ => y ^ (momentC k - 1) * h y)
      (volume.restrict (Ioi 0))
    apply (h.momentIntegrable (k + 1)).congr
    filter_upwards with y
    simp only [momentIntegrand, momentC_sub_one_eq_halfExponent_succ,
      Real.rpow_eq_pow]
  have hibp := curvature_improper_integration_by_parts H hCpos H.atC hmoment
  rw [momentC_sub_one_eq_halfExponent_succ] at hibp
  simpa [I, momentIntegrand, Real.rpow_eq_pow] using hibp

/-- The three identities used in manuscript Section 5, packaged in the printed order
`a_k`, `b_k`, `c_k`. -/
theorem CurvaturePairingHypotheses.ibp_at_manuscript_exponents
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    (∫ y in Ioi (0 : ℝ), y ^ (momentA k) * deriv V y * h y =
      momentA k * I h (k - 1)) ∧
    (∫ y in Ioi (0 : ℝ), y ^ (momentB k) * deriv V y * h y =
      momentB k * I h k) ∧
    (∫ y in Ioi (0 : ℝ), y ^ (momentC k) * deriv V y * h y =
      momentC k * I h (k + 1)) := by
  exact ⟨H.ibp_at_A, H.ibp_at_B, H.ibp_at_C⟩

end CrossBoundaryMomentKernels
