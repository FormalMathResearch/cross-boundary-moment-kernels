import CrossBoundaryMomentKernels.CurvatureBracket
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace CrossBoundaryMomentKernels

/-- Signed analogue of `orderedTonelliDensity`, supported on the manuscript region
`0 < y < u < z`.  Unlike the Tonelli density, this object is used only after absolute
integrability has been established. -/
def orderedSignedDensity
    (g : ℝ × ℝ → ℝ) (q : ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  if 0 < p.1.1 ∧ p.1.1 < p.2 ∧ p.2 < p.1.2 then g p.1 * q p.2 else 0

/-- Measurability of the signed ordered triple density. -/
theorem orderedSignedDensity_measurable
    {g : ℝ × ℝ → ℝ} {q : ℝ → ℝ}
    (hg : Measurable g) (hq : Measurable q) :
    Measurable (orderedSignedDensity g q) := by
  unfold orderedSignedDensity
  have hs : MeasurableSet
      {p : (ℝ × ℝ) × ℝ | 0 < p.1.1 ∧ p.1.1 < p.2 ∧ p.2 < p.1.2} := by
    measurability
  exact Measurable.ite hs
    ((hg.comp measurable_fst).mul (hq.comp measurable_snd)) measurable_const

/-- The absolute norm of the signed ordered density is exactly the corresponding nonnegative
Tonelli density.  This pointwise identity is the bridge by which the absolute Tonelli estimate
will imply integrability before signed Fubini is invoked. -/
theorem ofReal_norm_orderedSignedDensity_eq_orderedTonelliDensity
    (g : ℝ × ℝ → ℝ) (q : ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) :
    ENNReal.ofReal ‖orderedSignedDensity g q p‖ =
      orderedTonelliDensity
        (fun x => ENNReal.ofReal |g x|)
        (fun u => ENNReal.ofReal |q u|) p := by
  unfold orderedSignedDensity orderedTonelliDensity
  by_cases hp : 0 < p.1.1 ∧ p.1.1 < p.2 ∧ p.2 < p.1.2
  · rw [if_pos hp, if_pos hp]
    rw [Real.norm_eq_abs, abs_mul,
      ENNReal.ofReal_mul (abs_nonneg (g p.1))]
  · rw [if_neg hp, if_neg hp]
    simp

/-- For fixed `(y,z)` with `y>0`, integrating the signed triple density in the middle
variable gives the signed integral over `y<u<z`. -/
theorem integral_orderedSignedDensity_middle_of_pos
    {g : ℝ × ℝ → ℝ} {q : ℝ → ℝ} {y z : ℝ} (hy : 0 < y) :
    (∫ u : ℝ, orderedSignedDensity g q ((y, z), u) ∂volume) =
      g (y, z) * ∫ u : ℝ in Ioo y z, q u ∂volume := by
  have heq :
      (fun u : ℝ => orderedSignedDensity g q ((y, z), u)) =
        (Ioo y z).indicator (fun u => g (y, z) * q u) := by
    funext u
    simp [orderedSignedDensity, hy, Set.indicator, mem_Ioo]
  rw [heq, integral_indicator measurableSet_Ioo, integral_const_mul]

/-- The middle-variable slice with the positivity support condition included. -/
theorem integral_orderedSignedDensity_middle
    {g : ℝ × ℝ → ℝ} {q : ℝ → ℝ} (y z : ℝ) :
    (∫ u : ℝ, orderedSignedDensity g q ((y, z), u) ∂volume) =
      if 0 < y then g (y, z) * ∫ u : ℝ in Ioo y z, q u ∂volume else 0 := by
  by_cases hy : 0 < y
  · rw [if_pos hy, integral_orderedSignedDensity_middle_of_pos hy]
  · rw [if_neg hy]
    simp [orderedSignedDensity, hy]

/-- Lebesgue-null endpoints may be restored, matching the `Ioc` convention used by the
manuscript envelope and by the absolute Tonelli layer. -/
theorem integral_orderedSignedDensity_middle_Ioc
    {g : ℝ × ℝ → ℝ} {q : ℝ → ℝ} (y z : ℝ) :
    (∫ u : ℝ, orderedSignedDensity g q ((y, z), u) ∂volume) =
      if 0 < y then g (y, z) * ∫ u : ℝ in Ioc y z, q u ∂volume else 0 := by
  simpa only [MeasureTheory.restrict_Ioo_eq_restrict_Ioc] using
    (integral_orderedSignedDensity_middle (g := g) (q := q) y z)

/-- **Signed moving-domain Fubini theorem.**
Once the signed triple density is integrable, Fubini legitimately exchanges the `(y,z)` pair
with the middle variable `u`.  This theorem is deliberately separated from the earlier Tonelli
argument: its sole analytic input is the already-established absolute integrability. -/
theorem integral_orderedSigned_moving_domain_Ioc
    {g : ℝ × ℝ → ℝ} {q : ℝ → ℝ}
    (hf : Integrable (orderedSignedDensity g q) ((volume.prod volume).prod volume)) :
    (∫ p : ℝ × ℝ,
        (if 0 < p.1 then
          g p * ∫ u : ℝ in Ioc p.1 p.2, q u ∂volume
        else 0) ∂(volume.prod volume)) =
      ∫ u : ℝ, ∫ p : ℝ × ℝ,
        orderedSignedDensity g q (p, u) ∂(volume.prod volume) ∂volume := by
  calc
    (∫ p : ℝ × ℝ,
        (if 0 < p.1 then
          g p * ∫ u : ℝ in Ioc p.1 p.2, q u ∂volume
        else 0) ∂(volume.prod volume)) =
        ∫ p : ℝ × ℝ, ∫ u : ℝ,
          orderedSignedDensity g q (p, u) ∂volume ∂(volume.prod volume) := by
      apply integral_congr_ae
      filter_upwards with p
      exact (integral_orderedSignedDensity_middle_Ioc (g := g) (q := q) p.1 p.2).symm
    _ = ∫ u : ℝ, ∫ p : ℝ × ℝ,
        orderedSignedDensity g q (p, u) ∂(volume.prod volume) ∂volume :=
      MeasureTheory.integral_integral_swap hf

end CrossBoundaryMomentKernels
