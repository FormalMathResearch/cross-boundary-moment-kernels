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

/-- The nonnegative ordered-pair majorant that appears after applying the triangle inequality
to the FTC form of the manuscript two-copy integrand.  The remaining Tonelli step will expand
the interval integral and identify its reordered integral with the printed envelope `A_k`. -/
def curvatureFTCMajorant
    (h : FullSupportMomentWeight) (V : ℝ → ℝ) (k : ℕ) (y z : ℝ) : ℝ :=
  (y * z) ^ (momentA k) * h y * h z * (z - y) *
    (∫ u in y..z, |deriv (deriv V) u|) * |tau h k - y * z|

/-- On `0 < y < z`, the absolute value of the signed manuscript two-copy integrand is bounded by
exactly the ordered majorant obtained by replacing `|∫ V''|` with `∫ |V''|`. -/
theorem CurvaturePairingHypotheses.abs_curvatureTwoCopyIntegrand_le_FTCMajorant
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) {y z : ℝ}
    (hy : 0 < y) (hyz : y < z) :
    |curvatureTwoCopyIntegrand h V k y z| ≤ curvatureFTCMajorant h V k y z := by
  have hz : 0 < z := lt_trans hy hyz
  have hp : 0 ≤ (y * z) ^ (momentA k) :=
    Real.rpow_nonneg (mul_nonneg hy.le hz.le) _
  have hhy : 0 ≤ h y := h.nonneg hy
  have hhz : 0 ≤ h z := h.nonneg hz
  have hzy : 0 ≤ z - y := sub_nonneg.mpr hyz.le
  have hInt :
      |∫ u in y..z, deriv (deriv V) u| ≤
        ∫ u in y..z, |deriv (deriv V) u| :=
    intervalIntegral.abs_integral_le_integral_abs hyz.le
  rw [H.curvatureTwoCopyIntegrand_eq_intervalIntegral hy hyz, curvatureFTCMajorant]
  simp only [abs_mul, abs_of_nonneg hp, abs_of_nonneg hhy, abs_of_nonneg hhz,
    abs_of_nonneg hzy]
  gcongr

end CrossBoundaryMomentKernels
