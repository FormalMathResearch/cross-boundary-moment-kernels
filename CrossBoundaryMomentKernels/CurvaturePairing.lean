import CrossBoundaryMomentKernels.MomentCurvature
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

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
  apply hh.congr_deriv
  rw [(H.weight_eq hx).symm]
  ring

end CrossBoundaryMomentKernels
