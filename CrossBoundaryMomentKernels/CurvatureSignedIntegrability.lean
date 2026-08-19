import CrossBoundaryMomentKernels.CurvatureSignedFubini

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace CrossBoundaryMomentKernels

/-- A globally measurable representative of the signed ordered pair density, including the
factor `2` produced by symmetry.  On the positive quadrant it is exactly twice the signed
manuscript density. -/
def curvatureSignedFubiniG
    (h : FullSupportMomentWeight) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  2 * (Real.exp (Real.log (p.1 * p.2) * momentA k) * (p.2 - p.1) *
    (tau h k - p.1 * p.2) * h p.1 * h p.2)

lemma curvatureSignedFubiniG_measurable
    (h : FullSupportMomentWeight) (k : ℕ) :
    Measurable (curvatureSignedFubiniG h k) := by
  unfold curvatureSignedFubiniG
  have hh1 : Measurable (fun p : ℝ × ℝ => h p.1) :=
    h.measurable_toFun.comp measurable_fst
  have hh2 : Measurable (fun p : ℝ × ℝ => h p.2) :=
    h.measurable_toFun.comp measurable_snd
  measurability

/-- On `0<y<z`, the absolute norm of the measurable signed representative is exactly the
nonnegative Tonelli density already controlled by the printed envelope `A_k`. -/
theorem ofReal_abs_curvatureSignedFubiniG_eq_envelopeTonelliDensity
    (h : FullSupportMomentWeight) (k : ℕ) {y z : ℝ}
    (hy : 0 < y) (hyz : y < z) :
    ENNReal.ofReal |curvatureSignedFubiniG h k (y, z)| =
      curvatureEnvelopeTonelliDensity h k (y, z) := by
  have hz : 0 < z := lt_trans hy hyz
  have hgap : 0 ≤ z - y := sub_nonneg.mpr hyz.le
  have hhy : 0 ≤ h y := h.nonneg hy
  have hhz : 0 ≤ h z := h.nonneg hz
  unfold curvatureSignedFubiniG curvatureEnvelopeTonelliDensity
    curvatureEnvelopeDensityMeasurableRep
  congr 1
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos (Real.exp_pos _), abs_of_nonneg hgap,
    abs_of_nonneg hhy, abs_of_nonneg hhz, abs_abs]
  ring

/-- The actual second derivative is a.e. measurable on the manuscript domain, as a direct
consequence of `V ∈ C²(0,∞)`. -/
theorem CurvaturePairingHypotheses.secondDeriv_aemeasurableOn_positive
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    AEMeasurable (fun u : ℝ => deriv (deriv V) u)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hD : ContDiffOn ℝ 1 (deriv V) (Ioi (0 : ℝ)) :=
    H.smooth.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hD2 : ContinuousOn (deriv (deriv V)) (Ioi (0 : ℝ)) :=
    hD.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact (hD2.aestronglyMeasurable measurableSet_Ioi).aemeasurable

/-- **Absolute convergence gate for signed Fubini.**
Let `q` be any globally measurable representative agreeing a.e. with `V''` on `(0,∞)`.
Then the signed ordered triple density is integrable.  The proof uses exactly the previously
established finite absolute Tonelli integral, hence ultimately only the printed hypothesis
`∫₀∞ |V''(u)| A_k(u) du < ∞`. -/
theorem CurvaturePairingHypotheses.curvatureSignedTriple_integrable
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) {q : ℝ → ℝ}
    (hq : Measurable q)
    (hqeq : (fun u : ℝ => deriv (deriv V) u) =ᵐ[volume.restrict (Ioi (0 : ℝ))] q) :
    Integrable
      (orderedSignedDensity (curvatureSignedFubiniG h k) q)
      ((volume.prod volume).prod volume) := by
  have hg : Measurable (curvatureSignedFubiniG h k) :=
    curvatureSignedFubiniG_measurable h k
  have hfmeas : Measurable
      (orderedSignedDensity (curvatureSignedFubiniG h k) q) :=
    orderedSignedDensity_measurable hg hq
  refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hgAbs : Measurable
      (fun p : ℝ × ℝ => ENNReal.ofReal |curvatureSignedFubiniG h k p|) :=
    ENNReal.measurable_ofReal.comp hg.abs
  have hqAbs : Measurable (fun u : ℝ => ENNReal.ofReal |q u|) :=
    ENNReal.measurable_ofReal.comp hq.abs
  have hordered : Measurable
      (orderedTonelliDensity
        (fun p : ℝ × ℝ => ENNReal.ofReal |curvatureSignedFubiniG h k p|)
        (fun u : ℝ => ENNReal.ofReal |q u|)) :=
    orderedTonelliDensity_measurable hgAbs hqAbs
  have hqImp : ∀ᵐ u ∂volume,
      u ∈ Ioi (0 : ℝ) → deriv (deriv V) u = q u :=
    ae_imp_of_ae_restrict hqeq
  calc
    (∫⁻ t : (ℝ × ℝ) × ℝ,
        ENNReal.ofReal ‖orderedSignedDensity (curvatureSignedFubiniG h k) q t‖
        ∂((volume.prod volume).prod volume)) =
        ∫⁻ t : (ℝ × ℝ) × ℝ,
          orderedTonelliDensity
            (fun p : ℝ × ℝ => ENNReal.ofReal |curvatureSignedFubiniG h k p|)
            (fun u : ℝ => ENNReal.ofReal |q u|) t
          ∂((volume.prod volume).prod volume) := by
      apply lintegral_congr
      intro t
      exact ofReal_norm_orderedSignedDensity_eq_orderedTonelliDensity
        (curvatureSignedFubiniG h k) q t
    _ = ∫⁻ p : ℝ × ℝ, ∫⁻ u : ℝ,
          orderedTonelliDensity
            (fun x : ℝ × ℝ => ENNReal.ofReal |curvatureSignedFubiniG h k x|)
            (fun v : ℝ => ENNReal.ofReal |q v|) (p, u)
          ∂volume ∂(volume.prod volume) := by
      rw [lintegral_prod _ hordered.aemeasurable]
    _ = ∫⁻ p : ℝ × ℝ,
        (if 0 < p.1 then
          ENNReal.ofReal |curvatureSignedFubiniG h k p| *
            ∫⁻ u : ℝ in Ioo p.1 p.2, ENNReal.ofReal |q u| ∂volume
        else 0) ∂(volume.prod volume) := by
      apply lintegral_congr
      intro p
      exact lintegral_orderedTonelliDensity_middle hqAbs p.1 p.2
    _ = ∫⁻ p : ℝ × ℝ,
        (if 0 < p.1 then
          ENNReal.ofReal |curvatureSignedFubiniG h k p| *
            ∫⁻ u : ℝ in Ioc p.1 p.2, ENNReal.ofReal |q u| ∂volume
        else 0) ∂(volume.prod volume) := by
      simp only [MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    _ = ∫⁻ p : ℝ × ℝ,
        (if 0 < p.1 then
          curvatureEnvelopeTonelliDensity h k p *
            ∫⁻ u : ℝ in Ioc p.1 p.2,
              ENNReal.ofReal |deriv (deriv V) u| ∂volume
        else 0) ∂(volume.prod volume) := by
      apply lintegral_congr_ae
      filter_upwards with p
      by_cases hy : 0 < p.1
      · rw [if_pos hy, if_pos hy]
        by_cases hyz : p.1 < p.2
        · rw [ofReal_abs_curvatureSignedFubiniG_eq_envelopeTonelliDensity h k hy hyz]
          have heq :
              (fun u : ℝ => ENNReal.ofReal |q u|) =ᵐ[volume.restrict (Ioc p.1 p.2)]
                (fun u : ℝ => ENNReal.ofReal |deriv (deriv V) u|) := by
            change ∀ᵐ u ∂volume.restrict (Ioc p.1 p.2),
              ENNReal.ofReal |q u| = ENNReal.ofReal |deriv (deriv V) u|
            rw [ae_restrict_iff' measurableSet_Ioc]
            filter_upwards [hqImp] with u huq hu
            have hupos : u ∈ Ioi (0 : ℝ) := lt_trans hy hu.1
            rw [← huq hupos]
          rw [lintegral_congr_ae heq]
        · simp [Ioc_eq_empty hyz]
      · rw [if_neg hy, if_neg hy]
    _ < ⊤ := H.absoluteTonelli_lintegral_lt_top

end CrossBoundaryMomentKernels
