import CrossBoundaryMomentKernels.CrossBoundaryRepresentation

noncomputable section

open MeasureTheory Set

namespace CrossBoundaryMomentKernels

/-- The coefficient `A_k = (τ_k I_k + I_{k+2}) / I_{k+1}` from Theorem 2.2(ii). -/
def crossingA (h : ℝ → ℝ) (k : ℕ) : ℝ :=
  (tau h k * I h k + I h (k + 2)) / I h (k + 1)

/-- The monic quadratic controlling the derivative of the crossing kernel. -/
def crossingQ (h : ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  x ^ 2 - crossingA h k * x + tau h k

/-- The discriminant of the crossing quadratic. -/
def crossingDisc (h : ℝ → ℝ) (k : ℕ) : ℝ :=
  (crossingA h k) ^ 2 - 4 * tau h k

/-- The smaller root of the crossing quadratic. -/
def xiMinus (h : ℝ → ℝ) (k : ℕ) : ℝ :=
  (crossingA h k - Real.sqrt (crossingDisc h k)) / 2

/-- The larger root of the crossing quadratic. -/
def xiPlus (h : ℝ → ℝ) (k : ℕ) : ℝ :=
  (crossingA h k + Real.sqrt (crossingDisc h k)) / 2

/-- The manuscript derivative density `2 I_{k+1} x^(k-1/2) h(x) Q_k(x)`. -/
def rDerivativeIntegrand (h : ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  2 * I h (k + 1) * momentIntegrand h k x * crossingQ h k x

/-- The canonical normalization is positive at every manuscript index `k ≥ 1`. -/
lemma N_pos (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    0 < N h k := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hfac₁ : 0 < (2 : ℝ) * (k : ℝ) - 1 := by linarith
  have hfac₂ : 0 < (2 : ℝ) * (k : ℝ) + 1 := by linarith
  dsimp [N]
  positivity

/-- The scale ratio `τ_k` is strictly positive for `k ≥ 1`. -/
lemma tau_pos (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    0 < tau h k := by
  rw [tau]
  exact div_pos (N_pos h (by omega)) (N_pos h hk)

/-- The linear coefficient `A_k` is strictly positive. -/
lemma crossingA_pos (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    0 < crossingA h k := by
  rw [crossingA]
  exact div_pos
    (add_pos (mul_pos (tau_pos h hk) (h.momentPositive k)) (h.momentPositive (k + 2)))
    (h.momentPositive (k + 1))

/-- Strict moment log-convexity forces the crossing quadratic to have positive discriminant. -/
lemma crossingDisc_pos (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    0 < crossingDisc h k := by
  have htau : 0 < tau h k := tau_pos h hk
  have hlog := (strict_moment_logConvexity_and_gamma_lt h k).1
  have hI : 0 < I h (k + 1) := h.momentPositive (k + 1)
  have hstrict :
      4 * tau h k * (I h (k + 1)) ^ 2 <
        4 * tau h k * (I h k * I h (k + 2)) := by
    nlinarith
  have hnum :
      0 < (tau h k * I h k + I h (k + 2)) ^ 2 -
        4 * tau h k * (I h (k + 1)) ^ 2 := by
    have hsquare : 0 ≤ (tau h k * I h k - I h (k + 2)) ^ 2 := sq_nonneg _
    nlinarith
  rw [crossingDisc, crossingA]
  field_simp
  nlinarith [sq_pos_of_pos hI]

/-- The explicit smaller root is positive. -/
lemma xiMinus_pos (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    0 < xiMinus h k := by
  have hA : 0 < crossingA h k := crossingA_pos h hk
  have hτ : 0 < tau h k := tau_pos h hk
  have hD : 0 < crossingDisc h k := crossingDisc_pos h hk
  have hsqrt_nonneg : 0 ≤ Real.sqrt (crossingDisc h k) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (crossingDisc h k)) ^ 2 = crossingDisc h k := by
    rw [sq_sqrt hD.le]
  have hsqrt_lt : Real.sqrt (crossingDisc h k) < crossingA h k := by
    rw [crossingDisc] at hsqrt_sq
    nlinarith
  rw [xiMinus]
  linarith

/-- The two explicit roots are strictly ordered. -/
lemma xiMinus_lt_xiPlus (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    xiMinus h k < xiPlus h k := by
  have hsqrt : 0 < Real.sqrt (crossingDisc h k) := Real.sqrt_pos.2 (crossingDisc_pos h hk)
  rw [xiMinus, xiPlus]
  linarith

/-- The larger explicit root is positive. -/
lemma xiPlus_pos (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) :
    0 < xiPlus h k :=
  lt_trans (xiMinus_pos h hk) (xiMinus_lt_xiPlus h hk)

/-- The crossing quadratic factors through its two explicit roots. -/
lemma crossingQ_factor (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    crossingQ h k x = (x - xiMinus h k) * (x - xiPlus h k) := by
  have hD : 0 ≤ crossingDisc h k := (crossingDisc_pos h hk).le
  have hsqrt_sq : (Real.sqrt (crossingDisc h k)) ^ 2 = crossingDisc h k := by
    rw [sq_sqrt hD]
  rw [crossingQ, xiMinus, xiPlus, crossingDisc] at *
  nlinarith

/-- `Q_k` is positive to the left of its smaller root. -/
lemma crossingQ_pos_of_lt_xiMinus
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : x < xiMinus h k) :
    0 < crossingQ h k x := by
  rw [crossingQ_factor h hk]
  exact mul_pos_of_neg_of_neg (sub_neg.mpr hx)
    (sub_neg.mpr (lt_trans hx (xiMinus_lt_xiPlus h hk)))

/-- `Q_k` is negative strictly between its two roots. -/
lemma crossingQ_neg_between
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx₁ : xiMinus h k < x) (hx₂ : x < xiPlus h k) :
    crossingQ h k x < 0 := by
  rw [crossingQ_factor h hk]
  exact mul_neg_of_pos_of_neg (sub_pos.mpr hx₁) (sub_neg.mpr hx₂)

/-- `Q_k` is positive to the right of its larger root. -/
lemma crossingQ_pos_of_xiPlus_lt
    (h : FullSupportMomentWeight) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : xiPlus h k < x) :
    0 < crossingQ h k x := by
  rw [crossingQ_factor h hk]
  exact mul_pos (sub_pos.mpr (lt_trans (xiMinus_lt_xiPlus h hk) hx)) (sub_pos.mpr hx)

end CrossBoundaryMomentKernels
