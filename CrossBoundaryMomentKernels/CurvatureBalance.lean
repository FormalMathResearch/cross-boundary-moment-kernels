import CrossBoundaryMomentKernels.CurvatureSymmetryFTC
import CrossBoundaryMomentKernels.OneCrossingGeometry

noncomputable section

open MeasureTheory Set Filter
open scoped Interval

namespace CrossBoundaryMomentKernels

/-- The signed curvature-pairing integrand is integrable on `(0,∞)`.  This is a direct
consequence of the absolute-convergence gate already established before signed Fubini. -/
theorem CurvaturePairingHypotheses.curvaturePairingIntegrand_integrableOn_positive
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    IntegrableOn (fun u : ℝ => deriv (deriv V) u * R h k u) (Ioi (0 : ℝ)) := by
  let q0 : ℝ → ℝ := fun u => deriv (deriv V) u
  have hq0 : AEMeasurable q0 (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [q0] using H.secondDeriv_aemeasurableOn_positive
  let q : ℝ → ℝ := hq0.mk q0
  have hq : Measurable q := hq0.measurable_mk
  have hqeq : q0 =ᵐ[volume.restrict (Ioi (0 : ℝ))] q := hq0.ae_eq_mk
  have hqImp : ∀ᵐ u ∂volume,
      u ∈ Ioi (0 : ℝ) → q0 u = q u :=
    ae_imp_of_ae_restrict hqeq
  have htriple : Integrable
      (orderedSignedDensity (curvatureSignedFubiniG h k) q)
      ((volume.prod volume).prod volume) := by
    apply H.curvatureSignedTriple_integrable hq
    simpa [q0] using hqeq
  have hsliceIntegrable : Integrable
      (fun u : ℝ => ∫ p : ℝ × ℝ,
        orderedSignedDensity (curvatureSignedFubiniG h k) q (p, u)
        ∂(volume.prod volume)) volume :=
    htriple.integral_prod_right
  have hsliceEq :
      (fun u : ℝ => ∫ p : ℝ × ℝ,
        orderedSignedDensity (curvatureSignedFubiniG h k) q (p, u)
        ∂(volume.prod volume)) =
      (fun u : ℝ => if 0 < u then q u * R h k u else 0) := by
    funext u
    exact integral_orderedSignedDensity_curvature_slice_all h k q u
  rw [hsliceEq] at hsliceIntegrable
  have hactual : Integrable
      (fun u : ℝ => if 0 < u then q0 u * R h k u else 0) volume := by
    apply hsliceIntegrable.congr
    filter_upwards [hqImp] with u huq
    by_cases hu : 0 < u
    · simp [hu, huq hu]
    · simp [hu]
  rw [← integrable_indicator_iff measurableSet_Ioi]
  apply hactual.congr
  filter_upwards with u
  by_cases hu : 0 < u
  · simp [hu, q0]
  · simp [hu]

/-- The canonical crossing point is strictly positive for the curvature range `k ≥ 1`. -/
lemma uStar_pos_of_curvatureHypotheses
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    0 < uStar h k := by
  exact lt_trans (xiMinus_pos h H.index) (uStar_spec h H.index).1.1

/-- Under `V'' ≥ 0`, the curvature pairing splits at the unique crossing into its positive
left lobe minus the absolute size of its negative right lobe.  This is an analytic helper for
the publication-facing Corollary 2.6; the manuscript corollary itself is stated only in
`CurvatureManuscriptForm.lean`. -/
theorem CurvaturePairingHypotheses.curvaturePairingIntegral_eq_left_sub_rightAbs
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k)
    (hconvex : ∀ u : ℝ, 0 < u → 0 ≤ deriv (deriv V) u) :
    (∫ u in Ioi (0 : ℝ), deriv (deriv V) u * R h k u) =
      (∫ u in (0 : ℝ)..uStar h k, deriv (deriv V) u * R h k u) -
        ∫ u in Ioi (uStar h k), deriv (deriv V) u * |R h k u| := by
  let f : ℝ → ℝ := fun u => deriv (deriv V) u * R h k u
  have huStar : 0 < uStar h k := uStar_pos_of_curvatureHypotheses H
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := by
    simpa [f] using H.curvaturePairingIntegrand_integrableOn_positive
  have htail : IntegrableOn f (Ioi (uStar h k)) :=
    hf.mono_set (Ioi_subset_Ioi huStar.le)
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (f := f) (a := (0 : ℝ)) (b := uStar h k) hf htail
  have htailEq :
      (∫ u in Ioi (uStar h k), f u) =
        -(∫ u in Ioi (uStar h k), deriv (deriv V) u * |R h k u|) := by
    rw [← integral_neg]
    apply integral_congr_ae
    change ∀ᵐ u ∂volume.restrict (Ioi (uStar h k)),
      f u = -(deriv (deriv V) u * |R h k u|)
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 < u := lt_trans huStar hu
    have hRneg : R h k u < 0 := R_neg_after_uStar h H.index hu
    have hVnonneg : 0 ≤ deriv (deriv V) u := hconvex u hu0
    simp only [f]
    rw [abs_of_neg hRneg]
    ring
  rw [htailEq] at hsplit
  simpa [f, sub_eq_add_neg] using hsplit.symm

end CrossBoundaryMomentKernels
