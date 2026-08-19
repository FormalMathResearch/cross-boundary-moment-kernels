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
  have hs : MeasurableSet
      {p : (ℝ × ℝ) × ℝ | 0 < p.1.1 ∧ p.1.1 < p.2 ∧ p.2 < p.1.2} := by
    measurability
  exact Measurable.ite hs
    ((hg.comp measurable_fst).mul (hq.comp measurable_snd)) measurable_const

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

/-- For a positive left endpoint `y`, the middle-variable slice of the ordered density is
exactly the integral over `y < u < z`. -/
theorem lintegral_orderedTonelliDensity_middle_of_pos
    {g : ℝ × ℝ → ℝ≥0∞} {q : ℝ → ℝ≥0∞}
    (hq : Measurable q) {y z : ℝ} (hy : 0 < y) :
    (∫⁻ u : ℝ, orderedTonelliDensity g q ((y, z), u) ∂volume) =
      g (y, z) * ∫⁻ u : ℝ in Ioo y z, q u ∂volume := by
  have heq :
      (fun u : ℝ => orderedTonelliDensity g q ((y, z), u)) =
        (Ioo y z).indicator (fun u => g (y, z) * q u) := by
    funext u
    simp [orderedTonelliDensity, hy, Set.indicator, mem_Ioo]
  rw [heq, lintegral_indicator measurableSet_Ioo]
  exact lintegral_const_mul _ hq

/-- The middle-variable slice, including the positive-support condition carried by the
manuscript's region `0 < y < u < z`. -/
theorem lintegral_orderedTonelliDensity_middle
    {g : ℝ × ℝ → ℝ≥0∞} {q : ℝ → ℝ≥0∞}
    (hq : Measurable q) (y z : ℝ) :
    (∫⁻ u : ℝ, orderedTonelliDensity g q ((y, z), u) ∂volume) =
      if 0 < y then g (y, z) * ∫⁻ u : ℝ in Ioo y z, q u ∂volume else 0 := by
  by_cases hy : 0 < y
  · rw [if_pos hy, lintegral_orderedTonelliDensity_middle_of_pos hq hy]
  · rw [if_neg hy]
    simp [orderedTonelliDensity, hy]

/-- For fixed `u`, the pair slice is exactly the rectangle `0 < y < u < z`.
The constant factor `q u` is kept on the right to make the two Tonelli slices line up directly. -/
theorem lintegral_orderedTonelliDensity_pair
    {g : ℝ × ℝ → ℝ≥0∞} {q : ℝ → ℝ≥0∞}
    (hg : Measurable g) (u : ℝ) :
    (∫⁻ p : ℝ × ℝ, orderedTonelliDensity g q (p, u) ∂(volume.prod volume)) =
      (∫⁻ y : ℝ in Ioo 0 u, ∫⁻ z : ℝ in Ioi u, g (y, z) ∂volume ∂volume) * q u := by
  have hs : MeasurableSet (Ioo (0 : ℝ) u ×ˢ Ioi u) :=
    measurableSet_Ioo.prod measurableSet_Ioi
  have heq :
      (fun p : ℝ × ℝ => orderedTonelliDensity g q (p, u)) =
        (Ioo (0 : ℝ) u ×ˢ Ioi u).indicator (fun p => g p * q u) := by
    funext p
    by_cases h0 : 0 < p.1
    · by_cases h1 : p.1 < u
      · by_cases h2 : u < p.2 <;>
          simp [orderedTonelliDensity, Set.indicator, mem_Ioo, mem_Ioi, mem_prod,
            h0, h1, h2]
      · simp [orderedTonelliDensity, Set.indicator, mem_Ioo, mem_Ioi, mem_prod, h0, h1]
    · simp [orderedTonelliDensity, Set.indicator, mem_Ioo, mem_Ioi, mem_prod, h0]
  rw [heq, lintegral_indicator hs]
  rw [lintegral_mul_const (q u) hg]
  rw [MeasureTheory.setLIntegral_prod]
  exact hg.aemeasurable

/-- Generic moving-domain Tonelli identity for the ordered region `0 < y < u < z`.
It is an equality of nonnegative extended integrals, hence it requires no finiteness or
integrability assumption and occurs before any signed cancellation. -/
theorem lintegral_ordered_moving_domain
    {g : ℝ × ℝ → ℝ≥0∞} {q : ℝ → ℝ≥0∞}
    (hg : Measurable g) (hq : Measurable q) :
    (∫⁻ p : ℝ × ℝ,
        (if 0 < p.1 then
          g p * ∫⁻ u : ℝ in Ioo p.1 p.2, q u ∂volume
        else 0) ∂(volume.prod volume)) =
      ∫⁻ u : ℝ,
        (∫⁻ y : ℝ in Ioo 0 u, ∫⁻ z : ℝ in Ioi u, g (y, z) ∂volume ∂volume) * q u
        ∂volume := by
  calc
    (∫⁻ p : ℝ × ℝ,
        (if 0 < p.1 then
          g p * ∫⁻ u : ℝ in Ioo p.1 p.2, q u ∂volume
        else 0) ∂(volume.prod volume)) =
        ∫⁻ p : ℝ × ℝ, ∫⁻ u : ℝ,
          orderedTonelliDensity g q (p, u) ∂volume ∂(volume.prod volume) := by
      apply lintegral_congr
      intro p
      symm
      exact lintegral_orderedTonelliDensity_middle hq p.1 p.2
    _ = ∫⁻ u : ℝ, ∫⁻ p : ℝ × ℝ,
          orderedTonelliDensity g q (p, u) ∂(volume.prod volume) ∂volume :=
      lintegral_orderedTonelli_swap hg hq
    _ = ∫⁻ u : ℝ,
        (∫⁻ y : ℝ in Ioo 0 u, ∫⁻ z : ℝ in Ioi u, g (y, z) ∂volume ∂volume) * q u
        ∂volume := by
      apply lintegral_congr
      intro u
      exact lintegral_orderedTonelliDensity_pair hg u

end CrossBoundaryMomentKernels
