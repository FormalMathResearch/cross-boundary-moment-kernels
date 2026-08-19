import CrossBoundaryMomentKernels.CurvatureSignedFubiniR
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open MeasureTheory Set Filter
open scoped Interval

namespace CrossBoundaryMomentKernels

private def curvatureUpperHalf : Set (ℝ × ℝ) :=
  {p | p.1 < p.2}

private def curvatureLowerHalf : Set (ℝ × ℝ) :=
  {p | p.2 < p.1}

private lemma curvatureUpperHalf_measurable : MeasurableSet curvatureUpperHalf := by
  unfold curvatureUpperHalf
  measurability

private lemma curvatureLowerHalf_measurable : MeasurableSet curvatureLowerHalf := by
  unfold curvatureLowerHalf
  measurability

/-- The symmetric two-copy integrand vanishes on the diagonal, so the positive quadrant splits
exactly into the two strict ordered halves without any separate diagonal-null argument. -/
theorem curvatureTwoCopyIntegral_eq_two_upperHalf
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    (∫ p, curvatureTwoCopyIntegrand h V k p.1 p.2
        ∂((volume.restrict (Ioi (0 : ℝ))).prod
          (volume.restrict (Ioi (0 : ℝ))))) =
      2 * ∫ p,
        curvatureUpperHalf.indicator
          (fun p : ℝ × ℝ => curvatureTwoCopyIntegrand h V k p.1 p.2) p
        ∂((volume.restrict (Ioi (0 : ℝ))).prod
          (volume.restrict (Ioi (0 : ℝ)))) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let f : ℝ × ℝ → ℝ := fun p => curvatureTwoCopyIntegrand h V k p.1 p.2
  have hf : Integrable f (μ.prod μ) := by
    simpa [μ, f] using H.curvatureTwoCopyIntegrand_integrable
  have hupperInt : Integrable (curvatureUpperHalf.indicator f) (μ.prod μ) :=
    hf.indicator curvatureUpperHalf_measurable
  have hlowerInt : Integrable (curvatureLowerHalf.indicator f) (μ.prod μ) :=
    hf.indicator curvatureLowerHalf_measurable
  have hdecomp :
      f = fun p => curvatureUpperHalf.indicator f p + curvatureLowerHalf.indicator f p := by
    funext p
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · simp [curvatureUpperHalf, curvatureLowerHalf, hlt, not_lt_of_ge hlt.le]
    · simp [curvatureUpperHalf, curvatureLowerHalf, f, curvatureTwoCopyIntegrand, heq]
    · simp [curvatureUpperHalf, curvatureLowerHalf, hgt, not_lt_of_ge hgt.le]
  have hswap :
      (fun p : ℝ × ℝ => curvatureUpperHalf.indicator f p.swap) =
        curvatureLowerHalf.indicator f := by
    funext p
    by_cases hp : p.2 < p.1
    · have hup : p.swap ∈ curvatureUpperHalf := by
        simpa [curvatureUpperHalf] using hp
      have hlo : p ∈ curvatureLowerHalf := by
        simpa [curvatureLowerHalf] using hp
      rw [Set.indicator_of_mem hup, Set.indicator_of_mem hlo]
      dsimp [f]
      exact curvatureTwoCopyIntegrand_swap h V k p.1 p.2
    · have hup : p.swap ∉ curvatureUpperHalf := by
        simpa [curvatureUpperHalf] using hp
      have hlo : p ∉ curvatureLowerHalf := by
        simpa [curvatureLowerHalf] using hp
      rw [Set.indicator_of_notMem hup, Set.indicator_of_notMem hlo]
  have hlower_eq_upper :
      (∫ p, curvatureLowerHalf.indicator f p ∂(μ.prod μ)) =
        ∫ p, curvatureUpperHalf.indicator f p ∂(μ.prod μ) := by
    calc
      (∫ p, curvatureLowerHalf.indicator f p ∂(μ.prod μ)) =
          ∫ p, curvatureUpperHalf.indicator f p.swap ∂(μ.prod μ) := by
        rw [hswap]
      _ = ∫ p, curvatureUpperHalf.indicator f p ∂(μ.prod μ) :=
        integral_prod_swap (curvatureUpperHalf.indicator f)
  change (∫ p, f p ∂(μ.prod μ)) = _
  rw [hdecomp, integral_add hupperInt hlowerInt, hlower_eq_upper]
  ring

/-- On the ordered positive half-plane, the FTC form of the two-copy integrand is exactly the
signed density times the set integral of `V''` over `(y,z]`. -/
theorem CurvaturePairingHypotheses.two_mul_twoCopy_eq_signedFTC
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) {y z : ℝ}
    (hy : 0 < y) (hyz : y < z) :
    2 * curvatureTwoCopyIntegrand h V k y z =
      2 * curvatureSignedEnvelopeDensity h k (y, z) *
        ∫ u : ℝ in Ioc y z, deriv (deriv V) u ∂volume := by
  rw [H.curvatureTwoCopyIntegrand_eq_intervalIntegral hy hyz,
    intervalIntegral.integral_of_le hyz.le]
  unfold curvatureSignedEnvelopeDensity
  ring

/-- **Symmetry + FTC bridge from manuscript Section 5.**
The full positive-quadrant two-copy integral equals the ordered signed integral that appears
immediately before the justified Fubini rearrangement.  The factor `2` comes only from symmetry;
the diagonal contributes exactly zero because the two-copy kernel contains `y-z`. -/
theorem CurvaturePairingHypotheses.twoCopyIntegral_eq_ordered_signedFTC
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    (∫ p, curvatureTwoCopyIntegrand h V k p.1 p.2
        ∂((volume.restrict (Ioi (0 : ℝ))).prod
          (volume.restrict (Ioi (0 : ℝ))))) =
      ∫ p : ℝ × ℝ,
        (if 0 < p.1 then
          2 * curvatureSignedEnvelopeDensity h k p *
            ∫ u : ℝ in Ioc p.1 p.2, deriv (deriv V) u ∂volume
        else 0) ∂(volume.prod volume) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let f : ℝ × ℝ → ℝ := fun p => curvatureTwoCopyIntegrand h V k p.1 p.2
  have hsym := curvatureTwoCopyIntegral_eq_two_upperHalf H
  have hpositive : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hpoint :
      (fun p : ℝ × ℝ =>
        (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator
          (curvatureUpperHalf.indicator (fun p : ℝ × ℝ => 2 * f p)) p) =
      (fun p : ℝ × ℝ =>
        if 0 < p.1 then
          2 * curvatureSignedEnvelopeDensity h k p *
            ∫ u : ℝ in Ioc p.1 p.2, deriv (deriv V) u ∂volume
        else 0) := by
    funext p
    by_cases hy : 0 < p.1
    · rw [if_pos hy]
      by_cases hyz : p.1 < p.2
      · have hz : 0 < p.2 := lt_trans hy hyz
        have hpos : p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := ⟨hy, hz⟩
        have hup : p ∈ curvatureUpperHalf := by simpa [curvatureUpperHalf] using hyz
        rw [Set.indicator_of_mem hpos, Set.indicator_of_mem hup]
        dsimp [f]
        exact H.two_mul_twoCopy_eq_signedFTC hy hyz
      · simp [Set.indicator, curvatureUpperHalf, hyz, Ioc_eq_empty hyz]
    · rw [if_neg hy]
      have hnotpos : p ∉ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
        intro hp
        exact hy hp.1
      rw [Set.indicator_of_notMem hnotpos]
  calc
    (∫ p, curvatureTwoCopyIntegrand h V k p.1 p.2
        ∂((volume.restrict (Ioi (0 : ℝ))).prod
          (volume.restrict (Ioi (0 : ℝ))))) =
        2 * ∫ p, curvatureUpperHalf.indicator f p ∂(μ.prod μ) := by
      simpa [μ, f] using hsym
    _ = ∫ p, curvatureUpperHalf.indicator (fun p : ℝ × ℝ => 2 * f p) p
          ∂(μ.prod μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with p
      by_cases hp : p ∈ curvatureUpperHalf
      · simp [Set.indicator_of_mem hp]
      · simp [Set.indicator_of_notMem hp]
    _ = ∫ p : ℝ × ℝ,
        (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator
          (curvatureUpperHalf.indicator (fun p : ℝ × ℝ => 2 * f p)) p
          ∂(volume.prod volume) := by
      dsimp [μ]
      rw [Measure.prod_restrict]
      rw [← integral_indicator hpositive]
    _ = ∫ p : ℝ × ℝ,
        (if 0 < p.1 then
          2 * curvatureSignedEnvelopeDensity h k p *
            ∫ u : ℝ in Ioc p.1 p.2, deriv (deriv V) u ∂volume
        else 0) ∂(volume.prod volume) := by
      rw [hpoint]

end CrossBoundaryMomentKernels
