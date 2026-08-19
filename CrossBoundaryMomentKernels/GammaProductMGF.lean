import CrossBoundaryMomentKernels.GammaProductLaw

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ProbabilityTheory Topology

namespace CrossBoundaryMomentKernels

/-- The normalized product is a measurable real-valued observable. -/
lemma gammaNormalizedProduct_measurable (u : ℝ) : Measurable (gammaNormalizedProduct u) := by
  unfold gammaNormalizedProduct crossBoundaryProduct
  fun_prop

/-- The real Gamma density is integrable for every positive shape and positive rate. -/
lemma gammaPDFReal_integrable {α r : ℝ} (hα : 0 < α) (hr : 0 < r) :
    Integrable (ProbabilityTheory.gammaPDFReal α r) := by
  refine ⟨(ProbabilityTheory.measurable_gammaPDFReal α r).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun x => ProbabilityTheory.gammaPDFReal_nonneg hα hr x)]
  have hlin : (∫⁻ x, ProbabilityTheory.gammaPDF α r x) < ∞ := by
    rw [ProbabilityTheory.lintegral_gammaPDF_eq_one hα hr]
    simp
  simpa [ProbabilityTheory.gammaPDF] using hlin

/-- A Gamma law of rate one has finite exponential moments at every real `t < 1`. -/
theorem gammaMeasure_exp_integrable_of_lt_one {α t : ℝ} (hα : 0 < α) (ht : t < 1) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (ProbabilityTheory.gammaMeasure α 1) := by
  let r : ℝ := 1 - t
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hrpow : r ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hr α)
  have hGamma : Real.Gamma α ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hα)
  have hpdf := gammaPDFReal_integrable hα hr
  have hbase : Integrable
      (fun x : ℝ => ProbabilityTheory.gammaPDFReal α 1 x * Real.exp (t * x)) := by
    apply (hpdf.const_mul (r ^ α)⁻¹).congr
    filter_upwards with x
    by_cases hx : 0 ≤ x
    · rw [ProbabilityTheory.gammaPDFReal, if_pos hx,
        ProbabilityTheory.gammaPDFReal, if_pos hx]
      simp
      have hexp : Real.exp (-(r * x)) = Real.exp (-x) * Real.exp (t * x) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [r]
        ring
      calc
        (r ^ α)⁻¹ * (r ^ α / Real.Gamma α * x ^ (α - 1) * Real.exp (-(r * x))) =
            (Real.Gamma α)⁻¹ * x ^ (α - 1) * Real.exp (-(r * x)) := by
          field_simp [hrpow, hGamma]
        _ = (Real.Gamma α)⁻¹ * x ^ (α - 1) * Real.exp (-x) * Real.exp (t * x) := by
          rw [hexp]
          ring
    · rw [ProbabilityTheory.gammaPDFReal, if_neg hx,
        ProbabilityTheory.gammaPDFReal, if_neg hx]
      simp
  have hmeas : AEMeasurable (ProbabilityTheory.gammaPDF α 1) volume :=
    (ProbabilityTheory.measurable_gammaPDFReal α 1).ennreal_ofReal.aemeasurable
  have htop : ∀ᵐ x ∂volume, ProbabilityTheory.gammaPDF α 1 x < ∞ := by
    filter_upwards with x
    exact ENNReal.ofReal_lt_top
  rw [ProbabilityTheory.gammaMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas htop]
  apply hbase.congr
  filter_upwards with x
  have hxnonneg := ProbabilityTheory.gammaPDFReal_nonneg hα (by norm_num : (0 : ℝ) < 1) x
  simp [ProbabilityTheory.gammaPDF, ENNReal.toReal_ofReal hxnonneg, smul_eq_mul]

/-- The Lebesgue-density form of the preceding Gamma exponential-integrability statement. -/
lemma gammaPDFReal_mul_exp_integrable_of_lt_one {α t : ℝ} (hα : 0 < α) (ht : t < 1) :
    Integrable (fun x : ℝ =>
      ProbabilityTheory.gammaPDFReal α 1 x * Real.exp (t * x)) := by
  have h := gammaMeasure_exp_integrable_of_lt_one hα ht
  have hmeas : AEMeasurable (ProbabilityTheory.gammaPDF α 1) volume :=
    (ProbabilityTheory.measurable_gammaPDFReal α 1).ennreal_ofReal.aemeasurable
  have htop : ∀ᵐ x ∂volume, ProbabilityTheory.gammaPDF α 1 x < ∞ := by
    filter_upwards with x
    exact ENNReal.ofReal_lt_top
  rw [ProbabilityTheory.gammaMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas htop] at h
  apply h.congr
  filter_upwards with x
  have hxnonneg := ProbabilityTheory.gammaPDFReal_nonneg hα (by norm_num : (0 : ℝ) < 1) x
  simp [ProbabilityTheory.gammaPDF, ENNReal.toReal_ofReal hxnonneg, smul_eq_mul]

/-- A Gamma moment integrand retains an integrable upper tail after multiplication by `exp(z/2)`. -/
lemma gammaMomentIntegrand_mul_exp_half_integrable_Ioi
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    Integrable (fun z : ℝ =>
      momentIntegrand (gammaFullSupportWeight a ha) j z * Real.exp ((1 / 2 : ℝ) * z))
      (volume.restrict (Ioi u)) := by
  let α : ℝ := gammaAlpha a j
  have hα : 0 < α := gammaAlpha_pos ha j
  have hGamma : Real.Gamma α ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hα)
  have hpdf : Integrable (fun z : ℝ =>
      ProbabilityTheory.gammaPDFReal α 1 z * Real.exp ((1 / 2 : ℝ) * z)) :=
    gammaPDFReal_mul_exp_integrable_of_lt_one hα (by norm_num)
  have hscaled := hpdf.const_mul (Real.Gamma α)
  have hrestrict : Integrable
      (fun z : ℝ => Real.Gamma α *
        (ProbabilityTheory.gammaPDFReal α 1 z * Real.exp ((1 / 2 : ℝ) * z)))
      (volume.restrict (Ioi u)) :=
    hscaled.mono_measure Measure.restrict_le_self
  apply hrestrict.congr
  refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
  filter_upwards with z hz
  have hz0 : 0 < z := lt_trans hu hz
  change Real.Gamma α *
      (ProbabilityTheory.gammaPDFReal α 1 z * Real.exp ((1 / 2 : ℝ) * z)) =
    momentIntegrand (gammaModelWeight a) j z * Real.exp ((1 / 2 : ℝ) * z)
  rw [gammaMomentIntegrand_eq a j hz0]
  simp [ProbabilityTheory.gammaPDFReal, hz0.le]
  change Real.Gamma α *
      ((Real.Gamma α)⁻¹ * z ^ (α - 1) * Real.exp (-z) * Real.exp ((1 / 2 : ℝ) * z)) =
    Real.exp (-z) * z ^ (α - 1) * Real.exp ((1 / 2 : ℝ) * z)
  field_simp [hGamma]
  ring

/-- Under the Gamma cross-boundary law, the normalized product `X/u` is nonnegative almost surely. -/
lemma gammaNormalizedProduct_nonneg_ae
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    0 ≤ᵐ[crossBoundaryMeasure (gammaFullSupportWeight a ha) k u]
      gammaNormalizedProduct u := by
  have hbase : 0 ≤ᵐ[crossBoundaryBaseMeasure u] gammaNormalizedProduct u := by
    filter_upwards [ae_mem_crossBoundaryRect u] with p hp
    have hz : 0 < p.2 := lt_trans hu hp.2
    rw [gammaNormalizedProduct, crossBoundaryProduct]
    exact div_nonneg (mul_nonneg hp.1.1.le hz.le) hu.le
  have hac :
      crossBoundaryMeasure (gammaFullSupportWeight a ha) k u ≪ crossBoundaryBaseMeasure u := by
    rw [crossBoundaryMeasure]
    exact withDensity_absolutelyContinuous (crossBoundaryBaseMeasure u) _
  exact hac.ae_le hbase

/-- The negative half exponential moment of `X/u` is integrable; this supplies the left side of
an open MGF neighborhood around zero. -/
theorem gammaNormalizedProduct_exp_neg_half_integrable
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    Integrable (fun p => Real.exp (-(1 / 2 : ℝ) * gammaNormalizedProduct u p))
      (crossBoundaryMeasure (gammaFullSupportWeight a ha) k u) := by
  letI : IsProbabilityMeasure
      (crossBoundaryMeasure (gammaFullSupportWeight a ha) k u) :=
    crossBoundaryMeasure_isProbability (gammaFullSupportWeight a ha) k hu
  have hconst : Integrable (fun _ : ℝ × ℝ => (1 : ℝ))
      (crossBoundaryMeasure (gammaFullSupportWeight a ha) k u) := by
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fun p => Real.exp (-(1 / 2 : ℝ) * gammaNormalizedProduct u p))
      (crossBoundaryMeasure (gammaFullSupportWeight a ha) k u) := by
    exact (Real.measurable_exp.comp
      (measurable_const.mul (gammaNormalizedProduct_measurable u))).aestronglyMeasurable
  refine hconst.mono hmeas ?_
  filter_upwards [gammaNormalizedProduct_nonneg_ae ha k hu] with p hp
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
  have hcoef : (-(1 / 2 : ℝ)) ≤ 0 := by norm_num
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hcoef hp)

/-- The positive half exponential moment of `X/u` is integrable. The proof uses only the
cross-boundary rectangle `0<y≤u<z` and the Gamma upper-tail decay. -/
theorem gammaNormalizedProduct_exp_half_integrable
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    Integrable (fun p => Real.exp ((1 / 2 : ℝ) * gammaNormalizedProduct u p))
      (crossBoundaryMeasure (gammaFullSupportWeight a ha) k u) := by
  let h := gammaFullSupportWeight a ha
  let μL : Measure ℝ := volume.restrict (Ioc (0 : ℝ) u)
  let μR : Measure ℝ := volume.restrict (Ioi u)
  have hkL : Integrable (momentIntegrand h k) μL := by
    simpa [h, μL, IntegrableOn] using
      (h.momentIntegrable k).mono_set (by intro y hy; exact hy.1)
  have hk1R : Integrable
      (fun z : ℝ => momentIntegrand h (k + 1) z * Real.exp ((1 / 2 : ℝ) * z)) μR := by
    simpa [h, μR] using gammaMomentIntegrand_mul_exp_half_integrable_Ioi ha (k + 1) hu
  have hmajorProd : Integrable
      (fun p : ℝ × ℝ => momentIntegrand h k p.1 *
        (momentIntegrand h (k + 1) p.2 * Real.exp ((1 / 2 : ℝ) * p.2)))
      (μL.prod μR) := hkL.mul_prod hk1R
  have hmajor : Integrable
      (fun p : ℝ × ℝ => (K h k u)⁻¹ *
        (momentIntegrand h k p.1 *
          (momentIntegrand h (k + 1) p.2 * Real.exp ((1 / 2 : ℝ) * p.2))))
      (crossBoundaryBaseMeasure u) := by
    simpa [crossBoundaryBaseMeasure, μL, μR] using hmajorProd.const_mul (K h k u)⁻¹
  have hdenInt := crossBoundaryDensity_integrable h k hu
  have hexpMeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.exp ((1 / 2 : ℝ) * gammaNormalizedProduct u p))
      (crossBoundaryBaseMeasure u) :=
    (Real.measurable_exp.comp
      (measurable_const.mul (gammaNormalizedProduct_measurable u))).aestronglyMeasurable
  have htargetMeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => crossBoundaryDensity h k u p *
        Real.exp ((1 / 2 : ℝ) * gammaNormalizedProduct u p))
      (crossBoundaryBaseMeasure u) := hdenInt.1.mul hexpMeas
  have hbase : Integrable
      (fun p : ℝ × ℝ => crossBoundaryDensity h k u p *
        Real.exp ((1 / 2 : ℝ) * gammaNormalizedProduct u p))
      (crossBoundaryBaseMeasure u) := by
    refine hmajor.mono htargetMeas ?_
    filter_upwards [ae_mem_crossBoundaryRect u] with p hp
    have hy : 0 < p.1 := hp.1.1
    have hz : 0 < p.2 := lt_trans hu hp.2
    have hyz : p.1 < p.2 := lt_of_le_of_lt hp.1.2 hp.2
    have hMky : 0 ≤ momentIntegrand h k p.1 := momentIntegrand_nonneg h k hy
    have hMkz : 0 ≤ momentIntegrand h k p.2 := momentIntegrand_nonneg h k hz
    have hKinv : 0 ≤ (K h k u)⁻¹ := inv_nonneg.mpr (K_pos h k hu).le
    have hxle : gammaNormalizedProduct u p ≤ p.2 := by
      rw [gammaNormalizedProduct, crossBoundaryProduct, div_le_iff₀ hu]
      calc
        p.1 * p.2 ≤ u * p.2 := mul_le_mul_of_nonneg_right hp.1.2 hz.le
        _ = p.2 * u := by ring
    have hexpLe : Real.exp ((1 / 2 : ℝ) * gammaNormalizedProduct u p) ≤
        Real.exp ((1 / 2 : ℝ) * p.2) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxle (by norm_num))
    have hgap : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hyz.le
    have hgapLe : p.2 - p.1 ≤ p.2 := by linarith
    have hcore :
        (p.2 - p.1) * Real.exp ((1 / 2 : ℝ) * gammaNormalizedProduct u p) ≤
          p.2 * Real.exp ((1 / 2 : ℝ) * p.2) :=
      mul_le_mul hgapLe hexpLe (Real.exp_pos _).le hz.le
    have hcoeff : 0 ≤ (K h k u)⁻¹ * momentIntegrand h k p.1 *
        momentIntegrand h k p.2 := mul_nonneg (mul_nonneg hKinv hMky) hMkz
    have hsucc := momentIntegrand_succ h k hz
    rw [crossBoundaryDensity, crossBoundaryIntegrand, hsucc]
    rw [Real.norm_eq_abs]
    have hleftNonneg : 0 ≤
        (K h k u)⁻¹ * (momentIntegrand h k p.1 * momentIntegrand h k p.2 *
          (p.2 - p.1)) * Real.exp ((1 / 2 : ℝ) * gammaNormalizedProduct u p) := by
      positivity
    have hrightNonneg : 0 ≤
        (K h k u)⁻¹ *
          (momentIntegrand h k p.1 *
            (p.2 * momentIntegrand h k p.2 * Real.exp ((1 / 2 : ℝ) * p.2))) := by
      positivity
    rw [abs_of_nonneg hleftNonneg, abs_of_nonneg hrightNonneg]
    calc
      (K h k u)⁻¹ * (momentIntegrand h k p.1 * momentIntegrand h k p.2 *
          (p.2 - p.1)) * Real.exp ((1 / 2 : ℝ) * gammaNormalizedProduct u p) =
          ((K h k u)⁻¹ * momentIntegrand h k p.1 * momentIntegrand h k p.2) *
            ((p.2 - p.1) * Real.exp ((1 / 2 : ℝ) * gammaNormalizedProduct u p)) := by ring
      _ ≤ ((K h k u)⁻¹ * momentIntegrand h k p.1 * momentIntegrand h k p.2) *
            (p.2 * Real.exp ((1 / 2 : ℝ) * p.2)) :=
        mul_le_mul_of_nonneg_left hcore hcoeff
      _ = (K h k u)⁻¹ *
          (momentIntegrand h k p.1 *
            (p.2 * momentIntegrand h k p.2 * Real.exp ((1 / 2 : ℝ) * p.2))) := by ring
  have hmeas : AEMeasurable
      (fun p => ENNReal.ofReal (crossBoundaryDensity h k u p))
      (crossBoundaryBaseMeasure u) := hdenInt.1.aemeasurable.ennreal_ofReal
  have htop : ∀ᵐ p ∂crossBoundaryBaseMeasure u,
      ENNReal.ofReal (crossBoundaryDensity h k u p) < ∞ := by
    filter_upwards with p
    exact ENNReal.ofReal_lt_top
  rw [crossBoundaryMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas htop]
  apply hbase.congr
  filter_upwards [crossBoundaryDensity_nonneg_ae h k hu] with p hp
  simp [ENNReal.toReal_ofReal hp, smul_eq_mul]

end CrossBoundaryMomentKernels
