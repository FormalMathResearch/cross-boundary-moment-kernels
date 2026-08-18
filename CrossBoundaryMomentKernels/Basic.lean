import Mathlib

noncomputable section

open MeasureTheory Set

namespace CrossBoundaryMomentKernels

/-- The half-integer exponent `j - 1/2` occurring in the manuscript. -/
def halfExponent (j : ℕ) : ℝ :=
  (j : ℝ) - (1 / 2 : ℝ)

/-- The integrand `y^(j-1/2) h(y)` used for global and truncated moments. -/
def momentIntegrand (h : ℝ → ℝ) (j : ℕ) (y : ℝ) : ℝ :=
  Real.rpow y (halfExponent j) * h y

/-- The global moment `I_j`. The integral is over `(0, ∞)`. -/
def I (h : ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ y, momentIntegrand h j y ∂(volume.restrict (Set.Ioi (0 : ℝ)))

/-- The truncated moment `J_j(u)`. -/
def J (h : ℝ → ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  ∫ y, momentIntegrand h j y ∂(volume.restrict (Set.Ioc (0 : ℝ) u))

/-- A full-support moment weight, mirroring Definition 2.1 of the manuscript.

The manuscript assumes a measurable nonnegative weight on `(0, ∞)`, positive mass on
all nonempty compact subintervals of `(0, ∞)`, and finite positive half-integer moments.
Finiteness is represented here by `IntegrableOn`; positivity of the moments is recorded
separately so that the Lean structure matches the stated hypotheses rather than silently
strengthening or weakening them.
-/
structure FullSupportMomentWeight where
  toFun : ℝ → ℝ
  measurable_toFun : Measurable toFun
  nonneg : ∀ ⦃y : ℝ⦄, 0 < y → 0 ≤ toFun y
  fullSupport : ∀ ⦃a b : ℝ⦄, 0 < a → a < b →
    0 < ∫ y, toFun y ∂(volume.restrict (Set.Ioc a b))
  momentIntegrable : ∀ j : ℕ,
    IntegrableOn (momentIntegrand toFun j) (Set.Ioi (0 : ℝ))
  momentPositive : ∀ j : ℕ, 0 < I toFun j

instance : CoeFun FullSupportMomentWeight (fun _ => ℝ → ℝ) where
  coe h := h.toFun

/-- The cross-boundary determinant `K_k(u)`. -/
def K (h : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  J h k u * I h (k + 1) - J h (k + 1) u * I h k

/-- The normalization `N_k` from the manuscript. It is used only for `k ≥ 1`. -/
def N (h : ℝ → ℝ) (k : ℕ) : ℝ :=
  ((2 : ℝ) * (k : ℝ) - 1) * ((2 : ℝ) * (k : ℝ) + 1) *
    I h (k - 1) * I h k

/-- The normalized determinant `Z_k(u) = K_k(u) / N_k`. -/
def Z (h : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  K h k u / N h k

/-- The scale ratio `τ_k = N_{k+1} / N_k`. -/
def tau (h : ℝ → ℝ) (k : ℕ) : ℝ :=
  N h (k + 1) / N h k

/-- The unnormalized crossing kernel `R_k(u) = 2(τ_k K_k(u) - K_{k+1}(u))`. -/
def R (h : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  2 * (tau h k * K h k u - K h (k + 1) u)

/-- The normalized crossing kernel `R̂_k(u) = R_k(u) / N_{k+1}`. -/
def Rhat (h : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  R h k u / N h (k + 1)

end CrossBoundaryMomentKernels
