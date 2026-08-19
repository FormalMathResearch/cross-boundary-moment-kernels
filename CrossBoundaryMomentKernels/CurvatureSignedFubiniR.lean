import CrossBoundaryMomentKernels.CurvatureSignedIntegrability

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- On the positive quadrant, the globally measurable signed representative is exactly twice the
signed manuscript density. -/
theorem curvatureSignedFubiniG_eq_two_signedEnvelopeDensity
    (h : FullSupportMomentWeight) (k : ℕ) {y z : ℝ}
    (hy : 0 < y) (hz : 0 < z) :
    curvatureSignedFubiniG h k (y, z) =
      2 * curvatureSignedEnvelopeDensity h k (y, z) := by
  unfold curvatureSignedFubiniG curvatureSignedEnvelopeDensity
  rw [Real.rpow_def_of_pos (mul_pos hy hz)]

/-- For fixed `u>0`, the inner `(y,z)` slice of the signed Fubini density is exactly
`q(u) R_k(u)`.  This is the formal version of the manuscript's inner-bracket identification. -/
theorem integral_orderedSignedDensity_curvature_slice
    (h : FullSupportMomentWeight) (k : ℕ) (q : ℝ → ℝ)
    {u : ℝ} (hu : 0 < u) :
    (∫ p : ℝ × ℝ,
        orderedSignedDensity (curvatureSignedFubiniG h k) q (p, u)
        ∂(volume.prod volume)) =
      q u * R h k u := by
  have heqIndicator :
      (fun p : ℝ × ℝ => orderedSignedDensity (curvatureSignedFubiniG h k) q (p, u)) =
        (Ioo (0 : ℝ) u ×ˢ Ioi u).indicator
          (fun p => curvatureSignedFubiniG h k p * q u) := by
    funext p
    simp only [orderedSignedDensity, Set.indicator, mem_prod, mem_Ioo, mem_Ioi]
    by_cases hp : 0 < p.1 ∧ p.1 < u ∧ u < p.2
    · rw [if_pos hp, if_pos ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩]
    · rw [if_neg hp]
      have hnot : ¬ (0 < p.1 ∧ p.1 < u) ∨ ¬ u < p.2 := by
        by_contra hn
        push_neg at hn
        exact hp ⟨hn.1.1, hn.1.2, hn.2⟩
      rcases hnot with hleft | hright
      · rw [if_neg (by simpa using hleft)]
      · rw [if_neg (by
          intro hm
          exact hright hm.2)]
  rw [heqIndicator, integral_indicator (measurableSet_Ioo.prod measurableSet_Ioi)]
  change (∫ p : ℝ × ℝ,
      curvatureSignedFubiniG h k p * q u
      ∂((volume.prod volume).restrict (Ioo (0 : ℝ) u ×ˢ Ioi u))) = _
  rw [← Measure.prod_restrict, MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  let μL : Measure ℝ := volume.restrict (Ioc (0 : ℝ) u)
  let μR : Measure ℝ := volume.restrict (Ioi u)
  change (∫ p : ℝ × ℝ, curvatureSignedFubiniG h k p * q u ∂(μL.prod μR)) = _
  have hleft : ∀ᵐ y ∂μL, y ∈ Ioc (0 : ℝ) u := by
    dsimp [μL]
    exact ae_restrict_mem measurableSet_Ioc
  have hright : ∀ᵐ z ∂μR, z ∈ Ioi u := by
    dsimp [μR]
    exact ae_restrict_mem measurableSet_Ioi
  have hrect : ∀ᵐ p ∂(μL.prod μR), p ∈ Ioc (0 : ℝ) u ×ˢ Ioi u := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioc.prod measurableSet_Ioi)).2 ?_
    filter_upwards [hleft] with y hy
    filter_upwards [hright] with z hz
    exact ⟨hy, hz⟩
  have heq :
      (fun p : ℝ × ℝ => curvatureSignedFubiniG h k p * q u) =ᵐ[μL.prod μR]
        (fun p => (2 * q u) * curvatureSignedEnvelopeDensity h k p) := by
    filter_upwards [hrect] with p hp
    have hy : 0 < p.1 := hp.1.1
    have hz : 0 < p.2 := lt_trans hu hp.2
    rw [curvatureSignedFubiniG_eq_two_signedEnvelopeDensity h k hy hz]
    ring
  calc
    (∫ p : ℝ × ℝ, curvatureSignedFubiniG h k p * q u ∂(μL.prod μR)) =
        ∫ p : ℝ × ℝ, (2 * q u) * curvatureSignedEnvelopeDensity h k p ∂(μL.prod μR) :=
      integral_congr_ae heq
    _ = (2 * q u) *
        ∫ p : ℝ × ℝ, curvatureSignedEnvelopeDensity h k p ∂(μL.prod μR) := by
      rw [integral_const_mul]
    _ = (2 * q u) * (R h k u / 2) := by
      rw [curvatureSignedEnvelopeIntegral_eq_R_half h k hu]
    _ = q u * R h k u := by ring

/-- The same slice identity globally: outside `u>0`, the ordered region is empty. -/
theorem integral_orderedSignedDensity_curvature_slice_all
    (h : FullSupportMomentWeight) (k : ℕ) (q : ℝ → ℝ) (u : ℝ) :
    (∫ p : ℝ × ℝ,
        orderedSignedDensity (curvatureSignedFubiniG h k) q (p, u)
        ∂(volume.prod volume)) =
      if 0 < u then q u * R h k u else 0 := by
  by_cases hu : 0 < u
  · rw [if_pos hu, integral_orderedSignedDensity_curvature_slice h k q hu]
  · rw [if_neg hu]
    have heqZero :
        (fun p : ℝ × ℝ => orderedSignedDensity (curvatureSignedFubiniG h k) q (p, u)) = 0 := by
      funext p
      unfold orderedSignedDensity
      rw [if_neg]
      intro hp
      exact hu (lt_trans hp.1 hp.2.1)
    rw [heqZero, integral_zero]

/-- **Signed Fubini identity in manuscript form.**
The ordered two-copy integral with `∫_y^z V''` is equal to `∫_0^∞ V''(u) R_k(u) du`.
Absolute integrability has already been proved from the printed envelope assumption before this
signed rearrangement is used. -/
theorem CurvaturePairingHypotheses.signedFubini_eq_R
    {h : FullSupportMomentWeight} {V : ℝ → ℝ} {k : ℕ}
    (H : CurvaturePairingHypotheses h V k) :
    (∫ p : ℝ × ℝ,
        (if 0 < p.1 then
          2 * curvatureSignedEnvelopeDensity h k p *
            ∫ u : ℝ in Ioc p.1 p.2, deriv (deriv V) u ∂volume
        else 0) ∂(volume.prod volume)) =
      ∫ u : ℝ in Ioi (0 : ℝ), deriv (deriv V) u * R h k u ∂volume := by
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
  have hFub := integral_orderedSigned_moving_domain_Ioc htriple
  have hleft :
      (∫ p : ℝ × ℝ,
          (if 0 < p.1 then
            curvatureSignedFubiniG h k p *
              ∫ u : ℝ in Ioc p.1 p.2, q u ∂volume
          else 0) ∂(volume.prod volume)) =
        ∫ p : ℝ × ℝ,
          (if 0 < p.1 then
            2 * curvatureSignedEnvelopeDensity h k p *
              ∫ u : ℝ in Ioc p.1 p.2, deriv (deriv V) u ∂volume
          else 0) ∂(volume.prod volume) := by
    apply integral_congr_ae
    filter_upwards with p
    by_cases hy : 0 < p.1
    · rw [if_pos hy, if_pos hy]
      by_cases hyz : p.1 < p.2
      · have hz : 0 < p.2 := lt_trans hy hyz
        rw [curvatureSignedFubiniG_eq_two_signedEnvelopeDensity h k hy hz]
        have heqInt :
            (∫ u : ℝ in Ioc p.1 p.2, q u ∂volume) =
              ∫ u : ℝ in Ioc p.1 p.2, deriv (deriv V) u ∂volume := by
          apply integral_congr_ae
          change ∀ᵐ u ∂volume.restrict (Ioc p.1 p.2),
            q u = deriv (deriv V) u
          rw [ae_restrict_iff' measurableSet_Ioc]
          filter_upwards [hqImp] with u huq hu
          have hupos : u ∈ Ioi (0 : ℝ) := lt_trans hy hu.1
          exact (huq hupos).symm
        rw [heqInt]
      · simp [Ioc_eq_empty hyz]
    · rw [if_neg hy, if_neg hy]
  have hright :
      (∫ u : ℝ, ∫ p : ℝ × ℝ,
          orderedSignedDensity (curvatureSignedFubiniG h k) q (p, u)
          ∂(volume.prod volume) ∂volume) =
        ∫ u : ℝ in Ioi (0 : ℝ), deriv (deriv V) u * R h k u ∂volume := by
    calc
      (∫ u : ℝ, ∫ p : ℝ × ℝ,
          orderedSignedDensity (curvatureSignedFubiniG h k) q (p, u)
          ∂(volume.prod volume) ∂volume) =
          ∫ u : ℝ, (if 0 < u then q u * R h k u else 0) ∂volume := by
        apply integral_congr_ae
        filter_upwards with u
        exact integral_orderedSignedDensity_curvature_slice_all h k q u
      _ = ∫ u : ℝ, (if 0 < u then deriv (deriv V) u * R h k u else 0) ∂volume := by
        apply integral_congr_ae
        filter_upwards [hqImp] with u huq
        by_cases hu : 0 < u
        · rw [if_pos hu, if_pos hu, ← huq hu]
          rfl
        · rw [if_neg hu, if_neg hu]
      _ = ∫ u : ℝ in Ioi (0 : ℝ), deriv (deriv V) u * R h k u ∂volume := by
        rw [← integral_indicator measurableSet_Ioi]
        apply integral_congr_ae
        filter_upwards with u
        by_cases hu : 0 < u
        · rw [if_pos hu, Set.indicator_of_mem hu]
        · rw [if_neg hu, Set.indicator_of_notMem hu]
  calc
    (∫ p : ℝ × ℝ,
        (if 0 < p.1 then
          2 * curvatureSignedEnvelopeDensity h k p *
            ∫ u : ℝ in Ioc p.1 p.2, deriv (deriv V) u ∂volume
        else 0) ∂(volume.prod volume)) =
        ∫ p : ℝ × ℝ,
          (if 0 < p.1 then
            curvatureSignedFubiniG h k p *
              ∫ u : ℝ in Ioc p.1 p.2, q u ∂volume
          else 0) ∂(volume.prod volume) := hleft.symm
    _ = ∫ u : ℝ, ∫ p : ℝ × ℝ,
        orderedSignedDensity (curvatureSignedFubiniG h k) q (p, u)
        ∂(volume.prod volume) ∂volume := hFub
    _ = ∫ u : ℝ in Ioi (0 : ℝ), deriv (deriv V) u * R h k u ∂volume := hright

end CrossBoundaryMomentKernels
