import CrossBoundaryMomentKernels.CurvatureEnvelopeIntegrability

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace CrossBoundaryMomentKernels

/-- A globally measurable ENNReal representative of twice the nonnegative envelope density.
On the positive quadrant it is exactly the density occurring in the manuscript absolute
Tonelli computation, including the factor `2`. -/
def curvatureEnvelopeTonelliDensity
    (h : FullSupportMomentWeight) (k : ℕ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * curvatureEnvelopeDensityMeasurableRep h k p)

lemma curvatureEnvelopeTonelliDensity_measurable
    (h : FullSupportMomentWeight) (k : ℕ) :
    Measurable (curvatureEnvelopeTonelliDensity h k) := by
  unfold curvatureEnvelopeTonelliDensity
  exact ENNReal.measurable_ofReal.comp
    ((measurable_const.mul (curvatureEnvelopeDensityMeasurableRep_measurable h k)))

/-- On the positive quadrant the measurable Tonelli representative is the exact manuscript
ordered density (with the factor `2`). -/
theorem curvatureEnvelopeTonelliDensity_eq_manuscript
    (h : FullSupportMomentWeight) (k : ℕ) {y z : ℝ}
    (hy : 0 < y) (hz : 0 < z) :
    curvatureEnvelopeTonelliDensity h k (y, z) =
      ENNReal.ofReal (2 * curvatureEnvelopeDensity h k (y, z)) := by
  unfold curvatureEnvelopeTonelliDensity curvatureEnvelopeDensityMeasurableRep
    curvatureEnvelopeDensity
  rw [Real.rpow_def_of_pos (mul_pos hy hz)]

/-- The absolute second derivative is almost-everywhere measurable on `(0,∞)` under exactly
`V ∈ C²(0,∞)`.  No behaviour of `V` outside the manuscript domain is required. -/
theorem CurvaturePairingHypotheses.secondDerivAbsENNReal_aemeasurableOn_positive
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    AEMeasurable (fun u : ℝ => ENNReal.ofReal |deriv (deriv V) u|)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hD : ContDiffOn ℝ 1 (deriv V) (Ioi (0 : ℝ)) :=
    H.smooth.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hD2 : ContinuousOn (deriv (deriv V)) (Ioi (0 : ℝ)) :=
    hD.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have habs : AEStronglyMeasurable (fun u : ℝ => |deriv (deriv V) u|)
      (volume.restrict (Ioi (0 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      hD2.aestronglyMeasurable measurableSet_Ioi |>.norm
  exact ENNReal.measurable_ofReal.comp_aemeasurable habs.aemeasurable

/-- For `u>0`, the measurable Tonelli density integrates over `0<y≤u<z` to exactly
`ofReal (A_k(u))`.  This is the bridge between the generic moving-domain Tonelli lemma and the
printed envelope. -/
theorem curvatureEnvelopeTonelliDensity_slice_eq_ofReal_envelope
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    (∫⁻ y : ℝ in Ioc (0 : ℝ) u, ∫⁻ z : ℝ in Ioi u,
        curvatureEnvelopeTonelliDensity h k (y, z) ∂volume ∂volume) =
      ENNReal.ofReal (curvatureEnvelope h k u) := by
  let base : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (curvatureEnvelopeDensityMeasurableRep h k p)
  have hbase : Measurable base :=
    ENNReal.measurable_ofReal.comp (curvatureEnvelopeDensityMeasurableRep_measurable h k)
  have hg : Measurable (curvatureEnvelopeTonelliDensity h k) :=
    curvatureEnvelopeTonelliDensity_measurable h k
  have hprod :
      (∫⁻ p : ℝ × ℝ in Ioc (0 : ℝ) u ×ˢ Ioi u,
          curvatureEnvelopeTonelliDensity h k p ∂(volume.prod volume)) =
        ∫⁻ y : ℝ in Ioc (0 : ℝ) u, ∫⁻ z : ℝ in Ioi u,
          curvatureEnvelopeTonelliDensity h k (y, z) ∂volume ∂volume := by
    rw [MeasureTheory.setLIntegral_prod]
    exact hg.aemeasurable
  have hscale :
      (∫⁻ p : ℝ × ℝ in Ioc (0 : ℝ) u ×ˢ Ioi u,
          curvatureEnvelopeTonelliDensity h k p ∂(volume.prod volume)) =
        2 * ∫⁻ p : ℝ × ℝ in Ioc (0 : ℝ) u ×ˢ Ioi u,
          base p ∂(volume.prod volume) := by
    change (∫⁻ p : ℝ × ℝ in Ioc (0 : ℝ) u ×ˢ Ioi u,
      ENNReal.ofReal (2 * curvatureEnvelopeDensityMeasurableRep h k p)
        ∂(volume.prod volume)) = _
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    rw [lintegral_const_mul]
    exact hbase
  have hrep :
      (∫⁻ p : ℝ × ℝ in Ioc (0 : ℝ) u ×ˢ Ioi u,
          base p ∂(volume.prod volume)) =
        ∫⁻ p : ℝ × ℝ in Ioc (0 : ℝ) u ×ˢ Ioi u,
          ENNReal.ofReal (curvatureEnvelopeDensity h k p) ∂(volume.prod volume) := by
    apply lintegral_congr_ae
    change ∀ᵐ p ∂(volume.prod volume).restrict (Ioc (0 : ℝ) u ×ˢ Ioi u),
      base p = ENNReal.ofReal (curvatureEnvelopeDensity h k p)
    rw [ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioi)]
    filter_upwards with p hp
    have hy : 0 < p.1 := hp.1.1
    have hz : 0 < p.2 := lt_trans hu hp.2
    simp only [base]
    unfold curvatureEnvelopeDensityMeasurableRep curvatureEnvelopeDensity
    rw [Real.rpow_def_of_pos (mul_pos hy hz)]
  have hbridge := ofReal_curvatureEnvelope_eq_two_mul_lintegral h k hu
  rw [← hprod, hscale, hrep]
  exact hbridge.symm

/-- **Absolute Tonelli identity, ENNReal form.**
This is the nonnegative measure-theoretic equality in manuscript Section 5, specialized to
`q(u)=|V''(u)|` and the exact envelope density.  A measurable representative of `|V''|` is used
only internally; the statement itself contains the manuscript function. -/
theorem CurvaturePairingHypotheses.absoluteTonelli_lintegral
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    (∫⁻ p : ℝ × ℝ,
        (if 0 < p.1 then
          curvatureEnvelopeTonelliDensity h k p *
            ∫⁻ u : ℝ in Ioc p.1 p.2,
              ENNReal.ofReal |deriv (deriv V) u| ∂volume
        else 0) ∂(volume.prod volume)) =
      ∫⁻ u : ℝ,
        (if 0 < u then
          ENNReal.ofReal (curvatureEnvelope h k u) *
            ENNReal.ofReal |deriv (deriv V) u|
        else 0) ∂volume := by
  let q0 : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal |deriv (deriv V) u|
  have hq0 : AEMeasurable q0 (volume.restrict (Ioi (0 : ℝ))) :=
    H.secondDerivAbsENNReal_aemeasurableOn_positive
  let q : ℝ → ℝ≥0∞ := hq0.mk q0
  have hq : Measurable q := hq0.measurable_mk
  have hqeq : q0 =ᵐ[volume.restrict (Ioi (0 : ℝ))] q := hq0.ae_eq_mk
  have hqImp : ∀ᵐ u ∂volume, u ∈ Ioi (0 : ℝ) → q0 u = q u :=
    ae_imp_of_ae_restrict hqeq
  have hg : Measurable (curvatureEnvelopeTonelliDensity h k) :=
    curvatureEnvelopeTonelliDensity_measurable h k
  have hTon := lintegral_ordered_moving_domain_Ioc hg hq
  calc
    (∫⁻ p : ℝ × ℝ,
        (if 0 < p.1 then
          curvatureEnvelopeTonelliDensity h k p *
            ∫⁻ u : ℝ in Ioc p.1 p.2,
              ENNReal.ofReal |deriv (deriv V) u| ∂volume
        else 0) ∂(volume.prod volume)) =
        ∫⁻ p : ℝ × ℝ,
          (if 0 < p.1 then
            curvatureEnvelopeTonelliDensity h k p *
              ∫⁻ u : ℝ in Ioc p.1 p.2, q u ∂volume
          else 0) ∂(volume.prod volume) := by
      apply lintegral_congr
      intro p
      by_cases hy : 0 < p.1
      · rw [if_pos hy, if_pos hy]
        have hsub : Ioc p.1 p.2 ⊆ Ioi (0 : ℝ) := by
          intro u hu
          exact lt_trans hy hu.1
        have heq : q0 =ᵐ[volume.restrict (Ioc p.1 p.2)] q := by
          change ∀ᵐ u ∂volume.restrict (Ioc p.1 p.2), q0 u = q u
          rw [ae_restrict_iff' measurableSet_Ioc]
          filter_upwards [hqImp] with u huq hu
          exact huq (hsub hu)
        congr 1
        exact lintegral_congr_ae heq
      · simp [hy]
    _ = ∫⁻ u : ℝ,
        (∫⁻ y : ℝ in Ioc 0 u, ∫⁻ z : ℝ in Ioi u,
          curvatureEnvelopeTonelliDensity h k (y, z) ∂volume ∂volume) * q u ∂volume := hTon
    _ = ∫⁻ u : ℝ,
        (if 0 < u then
          ENNReal.ofReal (curvatureEnvelope h k u) * q0 u
        else 0) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [hqImp] with u huq
      by_cases hu : 0 < u
      · rw [if_pos hu, curvatureEnvelopeTonelliDensity_slice_eq_ofReal_envelope h k hu,
          huq hu]
      · rw [if_neg hu]
        simp [Ioc_eq_empty hu]
    _ = ∫⁻ u : ℝ,
        (if 0 < u then
          ENNReal.ofReal (curvatureEnvelope h k u) *
            ENNReal.ofReal |deriv (deriv V) u|
        else 0) ∂volume := by
      rfl

end CrossBoundaryMomentKernels
