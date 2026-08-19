import CrossBoundaryMomentKernels.CurvatureTwoCopyManuscript
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open MeasureTheory Set Filter
open scoped Interval

namespace CrossBoundaryMomentKernels

/-- On every compact interval contained in `(0,∞)`, the derivative `V'` satisfies the
fundamental theorem of calculus under exactly the manuscript assumption `V ∈ C²(0,∞)`.
This is the analytic identity used in Section 5 before Tonelli/Fubini. -/
theorem CurvaturePairingHypotheses.integral_secondDeriv_eq_deriv_sub
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) {y z : ℝ}
    (hy : 0 < y) (hyz : y ≤ z) :
    (∫ u in y..z, deriv (deriv V) u) = deriv V z - deriv V y := by
  have hD : ContDiffOn ℝ 1 (deriv V) (Ioi (0 : ℝ)) :=
    H.smooth.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hsubset : uIcc y z ⊆ Ioi (0 : ℝ) := by
    rw [uIcc_of_le hyz]
    intro x hx
    exact lt_of_lt_of_le hy hx.1
  have hdiff : ∀ x ∈ uIcc y z, DifferentiableAt ℝ (deriv V) x := by
    intro x hx
    have hxpos : x ∈ Ioi (0 : ℝ) := hsubset hx
    exact (hD.differentiableOn (by norm_num) x hxpos).differentiableAt
      (isOpen_Ioi.mem_nhds hxpos)
  have hcont : ContinuousOn (deriv (deriv V)) (uIcc y z) :=
    (hD.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsubset
  exact intervalIntegral.integral_deriv_eq_sub hdiff hcont.intervalIntegrable

/-- Manuscript Section 5 identity
`(y-z)(V'(y)-V'(z)) = (z-y) ∫_y^z V''(u) du` for `0 < y < z`. -/
theorem CurvaturePairingHypotheses.deriv_difference_eq_intervalIntegral_secondDeriv
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) {y z : ℝ}
    (hy : 0 < y) (hyz : y < z) :
    (y - z) * (deriv V y - deriv V z) =
      (z - y) * ∫ u in y..z, deriv (deriv V) u := by
  rw [H.integral_secondDeriv_eq_deriv_sub hy hyz.le]
  ring

/-- The signed two-copy integrand is symmetric under interchange of its two variables. -/
theorem curvatureTwoCopyIntegrand_swap
    (h : FullSupportMomentWeight) (V : ℝ → ℝ) (k : ℕ) (y z : ℝ) :
    curvatureTwoCopyIntegrand h V k z y =
      curvatureTwoCopyIntegrand h V k y z := by
  have hmul : z * y = y * z := by ring
  rw [curvatureTwoCopyIntegrand, curvatureTwoCopyIntegrand, hmul]
  ring

/-- On the ordered region `0 < y < z`, the exact manuscript two-copy integrand has the
fundamental-theorem form used for the absolute Tonelli estimate. -/
theorem CurvaturePairingHypotheses.curvatureTwoCopyIntegrand_eq_intervalIntegral
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) {y z : ℝ}
    (hy : 0 < y) (hyz : y < z) :
    curvatureTwoCopyIntegrand h V k y z =
      (y * z) ^ (momentA k) * h y * h z * (z - y) *
        (∫ u in y..z, deriv (deriv V) u) * (tau h k - y * z) := by
  rw [curvatureTwoCopyIntegrand,
    H.integral_secondDeriv_eq_deriv_sub hy hyz.le]
  ring

end CrossBoundaryMomentKernels
