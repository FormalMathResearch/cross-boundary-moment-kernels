import CrossBoundaryMomentKernels.CurvatureAbsoluteTonelli

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace CrossBoundaryMomentKernels

/-- The printed envelope `A_k(u)` is nonnegative for `u>0`.  This is a consequence of its
ordered-region definition and the nonnegativity of the weight; it is not an extra hypothesis. -/
theorem curvatureEnvelope_nonneg
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    0 ≤ curvatureEnvelope h k u := by
  rw [curvatureEnvelope_eq_two_mul_productIntegral h k hu]
  have hnn :
      0 ≤ᵐ[(volume.prod volume).restrict (Ioc (0 : ℝ) u ×ˢ Ioi u)]
        curvatureEnvelopeDensity h k := by
    change ∀ᵐ p ∂(volume.prod volume).restrict (Ioc (0 : ℝ) u ×ˢ Ioi u),
      0 ≤ curvatureEnvelopeDensity h k p
    rw [ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioi)]
    filter_upwards with p hp
    exact curvatureEnvelopeDensity_nonneg_on_rectangle h k hu hp.1 hp.2
  have hint :
      0 ≤ ∫ p in Ioc (0 : ℝ) u ×ˢ Ioi u,
        curvatureEnvelopeDensity h k p ∂(volume.prod volume) :=
    integral_nonneg_of_ae hnn
  positivity

/-- The right-hand side of the absolute Tonelli identity is exactly the `ofReal` of the
ordinary integral appearing in the manuscript hypothesis
`∫₀∞ |V''(u)| A_k(u) du < ∞`.

The only sign input is `A_k(u) ≥ 0`, proved above from the definition. -/
theorem CurvaturePairingHypotheses.absoluteEnvelope_lintegral_eq_ofReal_integral
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    (∫⁻ u : ℝ,
        (if 0 < u then
          ENNReal.ofReal (curvatureEnvelope h k u) *
            ENNReal.ofReal |deriv (deriv V) u|
        else 0) ∂volume) =
      ENNReal.ofReal
        (∫ u in Ioi (0 : ℝ),
          |deriv (deriv V) u| * curvatureEnvelope h k u) := by
  have hf : Integrable
      (fun u : ℝ => |deriv (deriv V) u| * curvatureEnvelope h k u)
      (volume.restrict (Ioi (0 : ℝ))) := H.envelopeIntegrable
  have hnn :
      0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun u : ℝ => |deriv (deriv V) u| * curvatureEnvelope h k u) := by
    change ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ |deriv (deriv V) u| * curvatureEnvelope h k u
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    exact mul_nonneg (abs_nonneg _) (curvatureEnvelope_nonneg h k hu)
  have hbridge := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf hnn
  rw [hbridge]
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro u
  by_cases hu : 0 < u
  · have humem : u ∈ Ioi (0 : ℝ) := hu
    rw [if_pos hu, Set.indicator_of_mem humem,
      ENNReal.ofReal_mul (curvatureEnvelope_nonneg h k hu)]
  · have hunmem : u ∉ Ioi (0 : ℝ) := hu
    rw [if_neg hu, Set.indicator_of_notMem hunmem]

/-- **Finite absolute Tonelli identity.**
The manuscript envelope assumption makes the nonnegative three-variable Tonelli integral finite.
This is the precise analytic gate needed before any signed Fubini rearrangement. -/
theorem CurvaturePairingHypotheses.absoluteTonelli_lintegral_eq_ofReal_envelopeIntegral
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    (∫⁻ p : ℝ × ℝ,
        (if 0 < p.1 then
          curvatureEnvelopeTonelliDensity h k p *
            ∫⁻ u : ℝ in Ioc p.1 p.2,
              ENNReal.ofReal |deriv (deriv V) u| ∂volume
        else 0) ∂(volume.prod volume)) =
      ENNReal.ofReal
        (∫ u in Ioi (0 : ℝ),
          |deriv (deriv V) u| * curvatureEnvelope h k u) := by
  rw [H.absoluteTonelli_lintegral]
  exact H.absoluteEnvelope_lintegral_eq_ofReal_integral

/-- In particular, the absolute Tonelli integral is strictly below `∞`. -/
theorem CurvaturePairingHypotheses.absoluteTonelli_lintegral_lt_top
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    (∫⁻ p : ℝ × ℝ,
        (if 0 < p.1 then
          curvatureEnvelopeTonelliDensity h k p *
            ∫⁻ u : ℝ in Ioc p.1 p.2,
              ENNReal.ofReal |deriv (deriv V) u| ∂volume
        else 0) ∂(volume.prod volume)) < ⊤ := by
  rw [H.absoluteTonelli_lintegral_eq_ofReal_envelopeIntegral]
  exact ENNReal.ofReal_lt_top

end CrossBoundaryMomentKernels
