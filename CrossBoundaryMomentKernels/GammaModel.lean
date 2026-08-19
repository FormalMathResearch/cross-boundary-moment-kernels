import CrossBoundaryMomentKernels.InterOrderTrichotomy
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Distributions.Gamma

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace CrossBoundaryMomentKernels

/-- The exactly solvable manuscript family `h_a(y) = y^a exp(-y)`. -/
def gammaModelWeight (a y : ℝ) : ℝ :=
  y ^ a * Real.exp (-y)

/-- The Gamma shape parameter `α_k = k + a + 1/2`. -/
def gammaAlpha (a : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) + a + (1 / 2 : ℝ)

lemma gammaAlpha_pos {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k : ℕ) :
    0 < gammaAlpha a k := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [gammaAlpha]
  linarith

lemma gammaModelWeight_measurable (a : ℝ) : Measurable (gammaModelWeight a) := by
  unfold gammaModelWeight
  fun_prop

lemma gammaModelWeight_nonneg (a : ℝ) {y : ℝ} (hy : 0 < y) :
    0 ≤ gammaModelWeight a y := by
  rw [gammaModelWeight]
  exact mul_nonneg (Real.rpow_nonneg hy.le a) (Real.exp_pos (-y)).le

lemma gammaModelWeight_pos (a : ℝ) {y : ℝ} (hy : 0 < y) :
    0 < gammaModelWeight a y := by
  rw [gammaModelWeight]
  exact mul_pos (Real.rpow_pos_of_pos hy a) (Real.exp_pos (-y))

/-- On `(0,∞)`, the manuscript moment integrand is exactly the Euler-Gamma integrand. -/
lemma gammaMomentIntegrand_eq (a : ℝ) (k : ℕ) {y : ℝ} (hy : 0 < y) :
    momentIntegrand (gammaModelWeight a) k y =
      Real.exp (-y) * y ^ (gammaAlpha a k - 1) := by
  rw [momentIntegrand, gammaModelWeight]
  change y ^ halfExponent k * (y ^ a * Real.exp (-y)) =
    Real.exp (-y) * y ^ (gammaAlpha a k - 1)
  calc
    y ^ halfExponent k * (y ^ a * Real.exp (-y)) =
        (y ^ halfExponent k * y ^ a) * Real.exp (-y) := by ring
    _ = y ^ (halfExponent k + a) * Real.exp (-y) := by
      rw [← Real.rpow_add hy]
    _ = Real.exp (-y) * y ^ (gammaAlpha a k - 1) := by
      have hexp : halfExponent k + a = gammaAlpha a k - 1 := by
        rw [halfExponent, gammaAlpha]
        ring
      rw [hexp]
      ring

/-- The global half-integer moments of the Gamma family are exactly `Γ(α_k)`. -/
theorem gamma_I_eq_Gamma {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k : ℕ) :
    I (gammaModelWeight a) k = Real.Gamma (gammaAlpha a k) := by
  have hα : 0 < gammaAlpha a k := gammaAlpha_pos ha k
  rw [I]
  calc
    (∫ y, momentIntegrand (gammaModelWeight a) k y ∂(volume.restrict (Ioi (0 : ℝ)))) =
        ∫ y in Ioi (0 : ℝ), Real.exp (-y) * y ^ (gammaAlpha a k - 1) := by
      exact setIntegral_congr_fun measurableSet_Ioi fun y hy => gammaMomentIntegrand_eq a k hy
    _ = Real.Gamma (gammaAlpha a k) := (Real.Gamma_eq_integral hα).symm

/-- Every manuscript half-integer moment of the Gamma family is integrable. -/
theorem gammaMomentIntegrable {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k : ℕ) :
    IntegrableOn (momentIntegrand (gammaModelWeight a) k) (Ioi (0 : ℝ)) := by
  have hα : 0 < gammaAlpha a k := gammaAlpha_pos ha k
  have hbase := Real.GammaIntegral_convergent hα
  change Integrable (momentIntegrand (gammaModelWeight a) k) (volume.restrict (Ioi (0 : ℝ)))
  have hbase' :
      Integrable (fun y : ℝ => Real.exp (-y) * y ^ (gammaAlpha a k - 1))
        (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using hbase
  apply hbase'.congr
  refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
  filter_upwards with y hy
  exact (gammaMomentIntegrand_eq a k hy).symm

end CrossBoundaryMomentKernels
