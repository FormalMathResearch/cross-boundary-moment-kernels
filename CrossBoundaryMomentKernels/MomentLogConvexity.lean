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
  rw [momentIntegrand, momentIntegrand, halfExponent_succ]
  change (y ^ (halfExponent j + 1)) * h y = y * (y ^ halfExponent j * h y)
  rw [Real.rpow_add hy (halfExponent j) 1, Real.rpow_one]
  ring

/-- The moment integrand is nonnegative on the positive half-line. -/
lemma momentIntegrand_nonneg (h : FullSupportMomentWeight) (j : ℕ) {y : ℝ} (hy : 0 < y) :
    0 ≤ momentIntegrand h j y := by
  exact mul_nonneg (Real.rpow_nonneg hy.le _) (h.nonneg hy)

/-- On the support of the weight, the moment integrand is strictly positive. -/
lemma momentIntegrand_pos_of_mem_support (h : FullSupportMomentWeight) (j : ℕ) {y : ℝ}
    (hy : 0 < y) (hy_support : y ∈ Function.support (h : ℝ → ℝ)) :
    0 < momentIntegrand h j y := by
  have hh_pos : 0 < h y := lt_of_le_of_ne (h.nonneg hy) (Ne.symm hy_support)
  exact mul_pos (Real.rpow_pos_of_pos hy _) hh_pos

/-- Every consecutive-moment ratio is strictly positive for a full-support moment weight. -/
lemma gamma_pos (h : FullSupportMomentWeight) (k : ℕ) :
    0 < gamma h k := by
  exact div_pos (h.momentPositive (k + 1)) (h.momentPositive k)

end CrossBoundaryMomentKernels
