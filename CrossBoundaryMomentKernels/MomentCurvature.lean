import CrossBoundaryMomentKernels.GammaExplicit

noncomputable section

namespace CrossBoundaryMomentKernels

/-- Manuscript exponent `a_k = k - 1/2` used in the curvature pairing. -/
def momentA (k : ℕ) : ℝ := (k : ℝ) - (1 / 2 : ℝ)

/-- Manuscript exponent `b_k = k + 1/2`. -/
def momentB (k : ℕ) : ℝ := (k : ℝ) + (1 / 2 : ℝ)

/-- Manuscript exponent `c_k = k + 3/2`. -/
def momentC (k : ℕ) : ℝ := (k : ℝ) + (3 / 2 : ℝ)

/-- Manuscript normalized moment-ratio scale `s_k`. -/
def momentRatioScale (h : ℝ → ℝ) (k : ℕ) : ℝ :=
  I h k / (momentA k * I h (k - 1))

/-- Manuscript relative moment curvature `κ_k = s_k - 2 s_{k+1} + s_{k+2}`. -/
def momentCurvature (h : ℝ → ℝ) (k : ℕ) : ℝ :=
  momentRatioScale h k - 2 * momentRatioScale h (k + 1) + momentRatioScale h (k + 2)

lemma momentA_pos {k : ℕ} (hk : 1 ≤ k) : 0 < momentA k := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [momentA]
  linarith

lemma momentB_eq_A_succ (k : ℕ) : momentB k = momentA (k + 1) := by
  rw [momentA, momentB]
  push_cast
  ring

lemma momentC_eq_A_add_two (k : ℕ) : momentC k = momentA (k + 2) := by
  rw [momentA, momentC]
  push_cast
  ring

end CrossBoundaryMomentKernels
