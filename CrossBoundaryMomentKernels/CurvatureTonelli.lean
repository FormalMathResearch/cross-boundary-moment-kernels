import CrossBoundaryMomentKernels.CurvatureFTC
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace CrossBoundaryMomentKernels

/-- Generic nonnegative density on the ordered triple region
`0 < y < u < z`.  Keeping this Tonelli layer independent of the curvature-specific
algebra makes the measure-theoretic rearrangement explicit and reusable. -/
def orderedTonelliDensity
    (g : ℝ × ℝ → ℝ≥0∞) (q : ℝ → ℝ≥0∞) (p : (ℝ × ℝ) × ℝ) : ℝ≥0∞ :=
  if 0 < p.1.1 ∧ p.1.1 < p.2 ∧ p.2 < p.1.2 then g p.1 * q p.2 else 0

/-- Measurability of the ordered triple density. -/
theorem orderedTonelliDensity_measurable
    {g : ℝ × ℝ → ℝ≥0∞} {q : ℝ → ℝ≥0∞}
    (hg : Measurable g) (hq : Measurable q) :
    Measurable (orderedTonelliDensity g q) := by
  unfold orderedTonelliDensity
  measurability

/-- Tonelli may swap the pair variable `(y,z)` with the middle variable `u` on the
nonnegative region `0 < y < u < z`, without any integrability hypothesis.
This is the measure-theoretic core of the manuscript's absolute-convergence rearrangement. -/
theorem lintegral_orderedTonelli_swap
    {g : ℝ × ℝ → ℝ≥0∞} {q : ℝ → ℝ≥0∞}
    (hg : Measurable g) (hq : Measurable q) :
    (∫⁻ p : ℝ × ℝ, ∫⁻ u : ℝ,
        orderedTonelliDensity g q (p, u) ∂volume ∂(volume.prod volume)) =
      ∫⁻ u : ℝ, ∫⁻ p : ℝ × ℝ,
        orderedTonelliDensity g q (p, u) ∂(volume.prod volume) ∂volume := by
  exact MeasureTheory.lintegral_lintegral_swap
    (orderedTonelliDensity_measurable hg hq).aemeasurable

end CrossBoundaryMomentKernels
