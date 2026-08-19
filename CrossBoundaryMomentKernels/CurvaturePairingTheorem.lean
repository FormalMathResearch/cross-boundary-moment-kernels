import CrossBoundaryMomentKernels.CurvatureSymmetryFTC

noncomputable section

open MeasureTheory Set Filter
open scoped Interval ENNReal

namespace CrossBoundaryMomentKernels

/-- **Manuscript Theorem 2.5 (curvature pairing), end-to-end form.**

Under exactly the hypotheses packaged in `CurvaturePairingHypotheses`, the second difference
`κ_k` is the curvature pairing

`κ_k = (2 b_k c_k I_k I_{k+1})⁻¹ ∫₀∞ V''(u) R_k(u) du`.

The proof is deliberately written in the order of manuscript Section 5.  The local `have`
blocks expose the three improper-integration-by-parts identities, the covariance reduction,
the exact two-copy formula, the FTC step, the absolute Tonelli gate, the symmetry reduction,
and only then the signed Fubini rearrangement and the identification with `R_k`.
No hypothesis stronger than the manuscript assumptions is introduced. -/
theorem CurvaturePairingHypotheses.momentCurvature_eq_curvaturePairing
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    momentCurvature h k =
      (2 * momentB k * momentC k * I h k * I h (k + 1))⁻¹ *
        ∫ u in Ioi (0 : ℝ), deriv (deriv V) u * R h k u := by
  -- Lemma 5.1 at the three manuscript exponents a_k, b_k, c_k.
  have hIBPA := H.ibp_at_A
  have hIBPB := H.ibp_at_B
  have hIBPC := H.ibp_at_C

  -- The tilted-measure moment identities give the covariance decomposition of κ_k.
  have hCovariance := H.momentCurvature_eq_covariance_difference

  -- Covariance symmetrization and the moment algebra give the exact printed two-copy formula.
  have hTwoCopy := H.momentCurvature_eq_twoCopy_manuscript

  -- Fundamental theorem of calculus on every ordered pair 0 < y < z.
  have hFTC :
      ∀ {y z : ℝ}, 0 < y → y < z →
        (y - z) * (deriv V y - deriv V z) =
          (z - y) * ∫ u in y..z, deriv (deriv V) u := by
    intro y z hy hyz
    exact H.deriv_difference_eq_intervalIntegral_secondDeriv hy hyz

  -- Before signed Fubini, the exact nonnegative Tonelli integral is identified with the
  -- manuscript envelope integral and is finite by the stated envelope hypothesis.
  have hAbsoluteTonelli := H.absoluteTonelli_lintegral_eq_ofReal_envelopeIntegral
  have hAbsoluteFinite := H.absoluteTonelli_lintegral_lt_top

  -- Symmetry of the two-copy kernel, together with FTC, produces the ordered signed integral.
  have hSymmetryFTC := H.twoCopyIntegral_eq_ordered_signedFTC

  -- Only after the absolute-convergence gate do we perform signed Fubini; its inner bracket is R_k.
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

end CrossBoundaryMomentKernels
