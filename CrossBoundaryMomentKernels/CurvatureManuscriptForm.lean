import CrossBoundaryMomentKernels.CurvatureBalance

noncomputable section

open MeasureTheory Set Filter
open scoped Interval ENNReal

namespace CrossBoundaryMomentKernels

/-- **Manuscript Theorem 2.5 (Curvature pairing), publication-facing form.**

The assumptions are exposed in the same blocks as in the manuscript: `k ≥ 1`,
`h = exp(-V)` on `(0,∞)`, `V ∈ C²(0,∞)`, the boundary and weighted-`V'`
conditions at `a_k,b_k,c_k`, and the printed absolute envelope condition.

The headline proof exposes exactly the equality chain it invokes: the Section 5 two-copy
formula, symmetry plus FTC on the ordered region, and the signed Fubini identification with
`R_k`.  The preceding Lemma 5.1, tilted-measure/covariance, and absolute-convergence gates
remain kernel-checked dependencies of these named helper theorems rather than decorative
unused local facts. -/
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

  -- Endpoint of the Lemma 5.1 -> tilted law -> covariance -> two-copy chain.
  have hTwoCopy := H.momentCurvature_eq_twoCopy_manuscript

  -- Symmetry and the C² FTC step give the ordered signed integral.
  have hSymmetryFTC := H.twoCopyIntegral_eq_ordered_signedFTC

  -- The envelope hypothesis supplies the absolute-integrability gate before signed Fubini;
  -- the inner bracket is then identified exactly with R_k.
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

  -- Use the public manuscript-facing Theorem 2.5, not the internal packaged endpoint.
  have hPairing :
      momentCurvature h k =
        (2 * momentB k * momentC k * I h k * I h (k + 1))⁻¹ *
          ∫ u in Ioi (0 : ℝ), deriv (deriv V) u * R h k u :=
    curvature_theorem_2_5 h V hk hweight hsmooth hA hB hC henvelope

  -- The split theorem packages the already verified unique-crossing sign pattern together with
  -- the absolute convergence supplied by the Theorem 2.5 hypotheses.
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
