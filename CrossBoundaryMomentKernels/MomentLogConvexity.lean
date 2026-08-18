import CrossBoundaryMomentKernels.Basic

noncomputable section

open MeasureTheory Set

namespace CrossBoundaryMomentKernels

/-- The consecutive-moment ratio `γ_k = I_{k+1} / I_k` from the manuscript. -/
def gamma (h : ℝ → ℝ) (k : ℕ) : ℝ :=
  I h (k + 1) / I h k

/-- Advancing the moment index raises the half-integer exponent by one. -/
lemma halfExponent_succ (j : ℕ) :
    halfExponent (j + 1) = halfExponent j + 1 := by
  simp [halfExponent]
  ring

/-- On the positive half-line, the `(j+1)`-st moment integrand is obtained by
multiplying the `j`-th moment integrand by the integration variable. -/
lemma momentIntegrand_succ (h : ℝ → ℝ) (j : ℕ) {y : ℝ} (hy : 0 < y) :
    momentIntegrand h (j + 1) y = y * momentIntegrand h j y := by
  rw [momentIntegrand, momentIntegrand, halfExponent_succ, Real.rpow_add hy]
  simp [mul_assoc, mul_left_comm, mul_comm]

/-- Every consecutive-moment ratio is strictly positive for a full-support moment weight. -/
lemma gamma_pos (h : FullSupportMomentWeight) (k : ℕ) :
    0 < gamma h k := by
  exact div_pos (h.momentPositive (k + 1)) (h.momentPositive k)

end CrossBoundaryMomentKernels
