import CrossBoundaryMomentKernels.GammaModel

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ProbabilityTheory Interval

namespace CrossBoundaryMomentKernels

lemma gammaAlpha_succ (a : ℝ) (k : ℕ) :
    gammaAlpha a (k + 1) = gammaAlpha a k + 1 := by
  rw [gammaAlpha, gammaAlpha]
  push_cast
  ring

/-- Real lower incomplete-Gamma integral used to identify the truncated manuscript moments. -/
def gammaPartial (s u : ℝ) : ℝ :=
  ∫ y in 0..u, Real.exp (-y) * y ^ (s - 1)

/-- The truncated manuscript moment is the lower incomplete-Gamma integral. -/
theorem gamma_J_eq_partial {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k : ℕ) {u : ℝ}
    (hu : 0 ≤ u) :
    J (gammaFullSupportWeight a ha) k u = gammaPartial (gammaAlpha a k) u := by
  rw [J, gammaPartial, intervalIntegral.integral_of_le hu]
  exact setIntegral_congr_fun measurableSet_Ioc fun y hy =>
    gammaMomentIntegrand_eq a k (lt_of_lt_of_le hy.1 hu)

/-- Compatibility of mathlib's complex lower incomplete Gamma integral with the real one. -/
lemma complex_partialGamma_ofReal {s u : ℝ} (hs : 0 < s) (hu : 0 ≤ u) :
    Complex.partialGamma (s : ℂ) u = (gammaPartial s u : ℂ) := by
  rw [Complex.partialGamma, gammaPartial, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro y hy
  have hy0 : 0 ≤ y := by
    rw [uIcc_of_le hu] at hy
    exact hy.1
  change ((Real.exp (-y) : ℝ) : ℂ) * (y : ℂ) ^ ((s : ℂ) - 1) =
    ((Real.exp (-y) * y ^ (s - 1) : ℝ) : ℂ)
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hy0]
  norm_cast

/-- Integration-by-parts recurrence for the lower incomplete Gamma integral. -/
theorem gammaPartial_add_one {s u : ℝ} (hs : 0 < s) (hu : 0 ≤ u) :
    gammaPartial (s + 1) u =
      s * gammaPartial s u - Real.exp (-u) * u ^ s := by
  have hc := Complex.partialGamma_add_one (s := (s : ℂ)) (X := u) (by simpa using hs) hu
  have hcast : (s : ℂ) + 1 = ((s + 1 : ℝ) : ℂ) := by norm_num
  rw [hcast, complex_partialGamma_ofReal (by linarith) hu,
    complex_partialGamma_ofReal hs hu] at hc
  have hboundary :
      (((Real.exp (-u) * u ^ s : ℝ) : ℂ)) =
        ((-u : ℝ).exp : ℂ) * (u : ℂ) ^ (s : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hu]
    norm_cast
  rw [← hboundary] at hc
  exact_mod_cast hc

/-- Truncated Gamma recurrence in the exact manuscript indexing. -/
theorem gamma_J_succ {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k : ℕ) {u : ℝ}
    (hu : 0 ≤ u) :
    J (gammaFullSupportWeight a ha) (k + 1) u =
      gammaAlpha a k * J (gammaFullSupportWeight a ha) k u -
        u ^ (gammaAlpha a k) * Real.exp (-u) := by
  rw [gamma_J_eq_partial ha (k + 1) hu, gammaAlpha_succ,
    gammaPartial_add_one (gammaAlpha_pos ha k) hu,
    gamma_J_eq_partial ha k hu]
  ring

/-- Global Gamma recurrence in manuscript indexing. -/
theorem gamma_I_succ {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k : ℕ) :
    I (gammaFullSupportWeight a ha) (k + 1) =
      gammaAlpha a k * I (gammaFullSupportWeight a ha) k := by
  rw [gamma_I_eq_Gamma ha (k + 1), gamma_I_eq_Gamma ha k, gammaAlpha_succ]
  exact Real.Gamma_add_one (ne_of_gt (gammaAlpha_pos ha k))

end CrossBoundaryMomentKernels
