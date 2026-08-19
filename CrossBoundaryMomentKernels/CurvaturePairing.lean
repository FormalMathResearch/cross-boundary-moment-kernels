import CrossBoundaryMomentKernels.MomentCurvature
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- The absolute cross-boundary envelope `A_k(u)` from manuscript Theorem 2.5. -/
def curvatureEnvelope (h : FullSupportMomentWeight) (k : ℕ) (u : ℝ) : ℝ :=
  2 * ∫ y, ∫ z,
      (y * z) ^ (momentA k) * (z - y) * |tau h k - y * z| * h y * h z
      ∂(volume.restrict (Ioi u))
    ∂(volume.restrict (Ioc (0 : ℝ) u))

/-- The signed two-copy integrand appearing immediately before the Tonelli/Fubini step in
manuscript Section 5. -/
def curvatureTwoCopyIntegrand
    (h : FullSupportMomentWeight) (V : ℝ → ℝ) (k : ℕ) (y z : ℝ) : ℝ :=
  (y * z) ^ (momentA k) * h y * h z * (y - z) *
    (deriv V y - deriv V z) * (tau h k - y * z)

/-- The boundary and weighted-`V'` assumptions of Theorem 2.5 at one exponent `r`.
This is stated directly in the manuscript form: vanishing of `y^r h(y)` at both ends and
absolute integrability of `y^r V'(y) h(y)` on `(0,∞)`. -/
def CurvatureExponentHypotheses
    (h : FullSupportMomentWeight) (V : ℝ → ℝ) (r : ℝ) : Prop :=
  Tendsto (fun y : ℝ => y ^ r * h y) (nhdsWithin 0 (Ioi 0)) (nhds 0) ∧
  Tendsto (fun y : ℝ => y ^ r * h y) atTop (nhds 0) ∧
  IntegrableOn (fun y : ℝ => y ^ r * |deriv V y| * h y) (Ioi 0)

/-- The analytic assumptions of manuscript Theorem 2.5, packaged without strengthening them.
The three exponent conditions correspond exactly to `r ∈ {a_k,b_k,c_k}`.  The last field is
the printed absolute envelope condition used for Tonelli/Fubini. -/
structure CurvaturePairingHypotheses
    (h : FullSupportMomentWeight) (V : ℝ → ℝ) (k : ℕ) : Prop where
  index : 1 ≤ k
  weight_eq : Set.EqOn h (fun y : ℝ => Real.exp (-V y)) (Ioi 0)
  smooth : ContDiffOn ℝ 2 V (Ioi 0)
  atA : CurvatureExponentHypotheses h V (momentA k)
  atB : CurvatureExponentHypotheses h V (momentB k)
  atC : CurvatureExponentHypotheses h V (momentC k)
  envelopeIntegrable :
    IntegrableOn
      (fun u : ℝ => |deriv (deriv V) u| * curvatureEnvelope h k u)
      (Ioi 0)

/-- The differential identity `h' = -V' h` used in Lemma 5.1, derived from the manuscript
assumptions `h = exp(-V)` and `V ∈ C²(0,∞)`.  No differentiability of `h` is added as an
independent hypothesis. -/
theorem CurvaturePairingHypotheses.hasDerivAt_weight
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => h y) (-(deriv V x) * h x) x := by
  have hVwithin : DifferentiableWithinAt ℝ V (Ioi 0) x :=
    H.smooth.differentiableOn (by norm_num) x hx
  have hVat : DifferentiableAt ℝ V x :=
    hVwithin.differentiableAt (isOpen_Ioi.mem_nhds hx)
  have hexp :
      HasDerivAt (fun y : ℝ => Real.exp (-V y))
        (-(Real.exp (-V x) * deriv V x)) x := by
    simpa [Pi.neg_apply] using hVat.hasDerivAt.neg.exp
  have heq :
      (fun y : ℝ => h y) =ᶠ[nhds x] (fun y : ℝ => Real.exp (-V y)) := by
    filter_upwards [isOpen_Ioi.eventually_mem hx] with y hy
    exact H.weight_eq hy
  have hh := hexp.congr_of_eventuallyEq heq
  have hxEq : h x = Real.exp (-V x) := by
    exact H.weight_eq hx
  apply hh.congr_deriv
  calc
    -(Real.exp (-V x) * deriv V x) = -(deriv V x) * Real.exp (-V x) := by ring
    _ = -(deriv V x) * h x := by rw [hxEq]

/-- The manuscript's absolute `V'` assumption implies integrability of the signed derivative
term needed in integration by parts.  The only measurability input is the stated `C²` regularity
and `h = exp(-V)` on `(0,∞)`. -/
theorem CurvaturePairingHypotheses.weightedWeightDerivative_integrableOn
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) {r : ℝ}
    (Hr : CurvatureExponentHypotheses h V r) :
    IntegrableOn (fun y : ℝ => y ^ r * (-(deriv V y) * h y)) (Ioi 0) := by
  let f : ℝ → ℝ := fun y => y ^ r * (-(deriv V y) * h y)
  let g : ℝ → ℝ := fun y => y ^ r * (-(deriv V y) * Real.exp (-V y))
  have hderivCont : ContinuousOn (deriv V) (Ioi (0 : ℝ)) :=
    H.smooth.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hgCont : ContinuousOn g (Ioi (0 : ℝ)) := by
    intro y hy
    have hpow : ContinuousWithinAt (fun x : ℝ => x ^ r) (Ioi 0) y :=
      (Real.continuousAt_rpow_const y r (.inl (ne_of_gt hy))).continuousWithinAt
    have hV : ContinuousWithinAt V (Ioi 0) y := H.smooth.continuousOn y hy
    have hexpV : ContinuousWithinAt (fun x : ℝ => Real.exp (-V x)) (Ioi 0) y :=
      Real.continuous_exp.continuousAt.comp_continuousWithinAt hV.neg
    exact hpow.mul ((hderivCont y hy).neg.mul hexpV)
  have hfg : Set.EqOn f g (Ioi (0 : ℝ)) := by
    intro y hy
    have hyEq : h y = Real.exp (-V y) := H.weight_eq hy
    simp only [f, g]
    rw [hyEq]
  have hgMeas : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ))) :=
    hgCont.aestronglyMeasurable measurableSet_Ioi
  have hfgAE : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hfg)
  have hfMeas : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))) :=
    hgMeas.congr hfgAE.symm
  have hnorm : IntegrableOn (fun y : ℝ => ‖f y‖) (Ioi 0) := by
    refine Hr.2.2.congr_fun ?_ measurableSet_Ioi
    intro y hy
    have hpowNonneg : 0 ≤ y ^ r := Real.rpow_nonneg hy.le r
    have hhNonneg : 0 ≤ h y := h.nonneg hy
    change y ^ r * |deriv V y| * h y = |y ^ r * (-(deriv V y) * h y)|
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hpowNonneg, abs_of_nonneg hhNonneg]
    ring
  exact (integrable_norm_iff hfMeas).mp hnorm

/-- **Manuscript Lemma 5.1 (improper integration by parts).**
For `r > 0`, the boundary limits, absolute weighted-`V'` integrability, and the finite
`(r-1)` moment give exactly
`∫₀∞ y^r V'(y) h(y) dy = r ∫₀∞ y^(r-1) h(y) dy`.
The proof uses the improper integration-by-parts theorem on `(0,∞)`; its boundary terms are
exactly the two limits assumed in the manuscript. -/
theorem curvature_improper_integration_by_parts
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) {r : ℝ} (_hr : 0 < r)
    (Hr : CurvatureExponentHypotheses h V r)
    (hmoment : IntegrableOn (fun y : ℝ => y ^ (r - 1) * h y) (Ioi 0)) :
    ∫ y in Ioi (0 : ℝ), y ^ r * deriv V y * h y =
      r * ∫ y in Ioi (0 : ℝ), y ^ (r - 1) * h y := by
  have hu : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => y ^ r) (r * x ^ (r - 1)) x := by
    intro x hx
    exact Real.hasDerivAt_rpow_const (.inl (ne_of_gt hx))
  have hv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => h y) (-(deriv V x) * h x) x := by
    intro x hx
    exact H.hasDerivAt_weight hx
  have huv' : IntegrableOn
      ((fun y : ℝ => y ^ r) * (fun y : ℝ => -(deriv V y) * h y)) (Ioi 0) := by
    change IntegrableOn (fun y : ℝ => y ^ r * (-(deriv V y) * h y)) (Ioi 0)
    exact H.weightedWeightDerivative_integrableOn Hr
  have hu'v : IntegrableOn
      ((fun y : ℝ => r * y ^ (r - 1)) * (fun y : ℝ => h y)) (Ioi 0) := by
    change Integrable (fun y : ℝ => (r * y ^ (r - 1)) * h y)
      (volume.restrict (Ioi 0))
    simpa only [mul_assoc] using hmoment.const_mul r
  have hzero : Tendsto
      ((fun y : ℝ => y ^ r) * (fun y : ℝ => h y))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    change Tendsto (fun y : ℝ => y ^ r * h y) (nhdsWithin 0 (Ioi 0)) (nhds 0)
    exact Hr.1
  have hinfty : Tendsto
      ((fun y : ℝ => y ^ r) * (fun y : ℝ => h y)) atTop (nhds 0) := by
    change Tendsto (fun y : ℝ => y ^ r * h y) atTop (nhds 0)
    exact Hr.2.1
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    hu hv huv' hu'v hzero hinfty
  have hleft :
      (∫ y in Ioi (0 : ℝ), y ^ r * (-(deriv V y) * h y)) =
        -(∫ y in Ioi (0 : ℝ), y ^ r * deriv V y * h y) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with y
    ring
  have hright :
      (∫ y in Ioi (0 : ℝ), (r * y ^ (r - 1)) * h y) =
        r * ∫ y in Ioi (0 : ℝ), y ^ (r - 1) * h y := by
    calc
      (∫ y in Ioi (0 : ℝ), (r * y ^ (r - 1)) * h y) =
          ∫ y in Ioi (0 : ℝ), r * (y ^ (r - 1) * h y) := by
            apply integral_congr_ae
            filter_upwards with y
            ring
      _ = r * ∫ y in Ioi (0 : ℝ), y ^ (r - 1) * h y := by
        rw [integral_const_mul]
  rw [hleft, hright] at hibp
  linarith

end CrossBoundaryMomentKernels
