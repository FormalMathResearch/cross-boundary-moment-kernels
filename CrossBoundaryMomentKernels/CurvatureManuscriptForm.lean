import CrossBoundaryMomentKernels.CurvatureBalance

noncomputable section

open MeasureTheory Set Filter
open scoped Interval ENNReal

namespace CrossBoundaryMomentKernels

/-- **Manuscript Theorem 2.5 (Curvature pairing), publication-facing form.**

The assumptions are exposed in the same blocks as in the manuscript: `k ≥ 1`,
`h = exp(-V)` on `(0,∞)`, `V ∈ C²(0,∞)`, the boundary and weighted-`V'`
conditions at `a_k,b_k,c_k`, and the printed absolute envelope condition.

The proof deliberately keeps the manuscript's main transitions visible in local `have`
blocks.  The underlying helper lemmas are modular, but the headline statement is checked
from these stated assumptions through the two-copy, FTC, absolute Tonelli, and signed
Fubini steps to the final curvature pairing. -/
theorem curvature_theorem_2_5
    (h : FullSupportMomentWeight) (V : ℝ → ℝ) {k : ℕ}
    (hk : 1 ≤ k)
    (hweight : Set.EqOn h (fun y : ℝ => Real.exp (-V y)) (Ioi (0 : ℝ)))
    (hsmooth : ContDiffOn ℝ 2 V (Ioi (0 : ℝ)))
    (hA : CurvatureExponentHypotheses h V (momentA k))
    (hB : CurvatureExponentHypotheses h V (momentB k))
    (hC : CurvatureExponentHypotheses h V (momentC k))
    (henvelope :
      IntegrableOn
        (fun u : ℝ => |deriv (deriv V) u| * curvatureEnvelope h k u)
        (Ioi (0 : ℝ))) :
    momentCurvature h k =
      (2 * momentB k * momentC k * I h k * I h (k + 1))⁻¹ *
        ∫ u in Ioi (0 : ℝ), deriv (deriv V) u * R h k u := by
  let H : CurvaturePairingHypotheses h V k :=
    { index := hk
      weight_eq := hweight
      smooth := hsmooth
      atA := hA
      atB := hB
      atC := hC
      envelopeIntegrable := henvelope }

  -- Lemma 5.1 at exactly the three manuscript exponents.
  have hIBPA := H.ibp_at_A
  have hIBPB := H.ibp_at_B
  have hIBPC := H.ibp_at_C

  -- Tilted-measure identities and covariance reduction of κ_k.
  have hCovariance := H.momentCurvature_eq_covariance_difference

  -- Exact signed two-copy formula printed in Section 5.
  have hTwoCopy := H.momentCurvature_eq_twoCopy_manuscript

  -- FTC on every ordered positive pair.
  have hFTC :
      ∀ {y z : ℝ}, 0 < y → y < z →
        (y - z) * (deriv V y - deriv V z) =
          (z - y) * ∫ u in y..z, deriv (deriv V) u := by
    intro y z hy hyz
    exact H.deriv_difference_eq_intervalIntegral_secondDeriv hy hyz

  -- Absolute Tonelli is established and finite before the signed rearrangement.
  have hAbsoluteTonelli := H.absoluteTonelli_lintegral_eq_ofReal_envelopeIntegral
  have hAbsoluteFinite := H.absoluteTonelli_lintegral_lt_top

  -- Symmetry plus FTC gives the ordered signed integral.
  have hSymmetryFTC := H.twoCopyIntegral_eq_ordered_signedFTC

  -- Only now is signed Fubini used, with the inner bracket identified as R_k.
  have hSignedFubini := H.signedFubini_eq_R

  calc
    momentCurvature h k =
        (2 * momentB k * momentC k * I h k * I h (k + 1))⁻¹ *
          ∫ p, curvatureTwoCopyIntegrand h V k p.1 p.2
            ∂((volume.restrict (Ioi (0 : ℝ))).prod
              (volume.restrict (Ioi (0 : ℝ)))) := hTwoCopy
    _ = (2 * momentB k * momentC k * I h k * I h (k + 1))⁻¹ *
        ∫ p : ℝ × ℝ,
          (if 0 < p.1 then
            2 * curvatureSignedEnvelopeDensity h k p *
              ∫ u : ℝ in Ioc p.1 p.2, deriv (deriv V) u ∂volume
          else 0) ∂(volume.prod volume) := by
      rw [hSymmetryFTC]
    _ = (2 * momentB k * momentC k * I h k * I h (k + 1))⁻¹ *
        ∫ u in Ioi (0 : ℝ), deriv (deriv V) u * R h k u := by
      rw [hSignedFubini]

/-- **Manuscript Corollary 2.6 (Curvature balance for log-concave weights),
publication-facing form.**

This exposes exactly the assumptions of Theorem 2.5 and adds only `V'' ≥ 0` on `(0,∞)`.
The conclusion is the manuscript balance between the positive lobe before the canonical
crossing and the absolute negative lobe after it. -/
theorem curvature_corollary_2_6
    (h : FullSupportMomentWeight) (V : ℝ → ℝ) {k : ℕ}
    (hk : 1 ≤ k)
    (hweight : Set.EqOn h (fun y : ℝ => Real.exp (-V y)) (Ioi (0 : ℝ)))
    (hsmooth : ContDiffOn ℝ 2 V (Ioi (0 : ℝ)))
    (hA : CurvatureExponentHypotheses h V (momentA k))
    (hB : CurvatureExponentHypotheses h V (momentB k))
    (hC : CurvatureExponentHypotheses h V (momentC k))
    (henvelope :
      IntegrableOn
        (fun u : ℝ => |deriv (deriv V) u| * curvatureEnvelope h k u)
        (Ioi (0 : ℝ)))
    (hconvex : ∀ u : ℝ, 0 < u → 0 ≤ deriv (deriv V) u) :
    0 ≤ momentCurvature h k ↔
      (∫ u in (0 : ℝ)..uStar h k, deriv (deriv V) u * R h k u) ≥
        ∫ u in Ioi (uStar h k), deriv (deriv V) u * |R h k u| := by
  let H : CurvaturePairingHypotheses h V k :=
    { index := hk
      weight_eq := hweight
      smooth := hsmooth
      atA := hA
      atB := hB
      atC := hC
      envelopeIntegrable := henvelope }

  -- Theorem 2.5 and the unique-crossing sign pattern are the two inputs.
  have hPairing := H.momentCurvature_eq_curvaturePairing
  have huStar := uStar_spec h hk
  have hLeftSign :
      ∀ {x : ℝ}, 0 < x → x < uStar h k → 0 < R h k x := by
    intro x hx hxu
    exact R_pos_before_uStar h hk hx hxu
  have hRightSign :
      ∀ {x : ℝ}, uStar h k < x → R h k x < 0 := by
    intro x hux
    exact R_neg_after_uStar h hk hux

  -- Absolute convergence from Theorem 2.5 permits the split at u_k^*.
  have hSplit := H.curvaturePairingIntegral_eq_left_sub_rightAbs hconvex

  -- The prefactor in Theorem 2.5 is strictly positive.
  have hBpos : 0 < momentB k := by
    rw [momentB_eq_A_succ]
    exact momentA_pos (by omega)
  have hCpos : 0 < momentC k := by
    rw [momentC_eq_A_add_two]
    exact momentA_pos (by omega)
  have hIk : 0 < I h k := h.momentPositive k
  have hIk1 : 0 < I h (k + 1) := h.momentPositive (k + 1)
  have hden : 0 < 2 * momentB k * momentC k * I h k * I h (k + 1) :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hBpos) hCpos) hIk) hIk1
  have hcoef :
      0 < (2 * momentB k * momentC k * I h k * I h (k + 1))⁻¹ :=
    inv_pos.mpr hden

  rw [hPairing, hSplit]
  constructor
  · intro hnonneg
    have hdiff :
        0 ≤ (∫ u in (0 : ℝ)..uStar h k, deriv (deriv V) u * R h k u) -
          ∫ u in Ioi (uStar h k), deriv (deriv V) u * |R h k u| :=
      (mul_nonneg_iff_of_pos_left hcoef).mp hnonneg
    linarith
  · intro hbalance
    have hdiff :
        0 ≤ (∫ u in (0 : ℝ)..uStar h k, deriv (deriv V) u * R h k u) -
          ∫ u in Ioi (uStar h k), deriv (deriv V) u * |R h k u| := by
      linarith
    exact mul_nonneg hcoef.le hdiff

end CrossBoundaryMomentKernels
