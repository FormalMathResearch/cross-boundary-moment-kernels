import CrossBoundaryMomentKernels.CurvatureTonelli

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace CrossBoundaryMomentKernels

/-- The three exponents occurring in the curvature envelope are exactly the consecutive
half-integer moment exponents. -/
lemma momentA_eq_halfExponent (k : ℕ) : momentA k = halfExponent k := by
  rw [momentA, halfExponent]

lemma momentB_eq_halfExponent_succ (k : ℕ) : momentB k = halfExponent (k + 1) := by
  rw [momentB, halfExponent]
  push_cast
  ring

lemma momentC_eq_halfExponent_add_two (k : ℕ) : momentC k = halfExponent (k + 2) := by
  rw [momentC, halfExponent]
  push_cast
  ring

lemma momentB_eq_A_add_one (k : ℕ) : momentB k = momentA k + 1 := by
  rw [momentA, momentB]
  ring

lemma momentC_eq_B_add_one (k : ℕ) : momentC k = momentB k + 1 := by
  rw [momentB, momentC]
  ring

/-- The moment factors at `a_k`, `b_k`, and `c_k` are integrable on `(0,∞)` solely from
Definition 2.1.  No curvature-specific analytic hypothesis is needed here. -/
theorem momentA_factor_integrable (h : FullSupportMomentWeight) (k : ℕ) :
    Integrable (fun y : ℝ => y ^ (momentA k) * h y) (volume.restrict (Ioi 0)) := by
  have hI := h.momentIntegrable k
  change Integrable (momentIntegrand h k) (volume.restrict (Ioi (0 : ℝ))) at hI
  simpa [momentIntegrand, momentA_eq_halfExponent] using hI

theorem momentB_factor_integrable (h : FullSupportMomentWeight) (k : ℕ) :
    Integrable (fun y : ℝ => y ^ (momentB k) * h y) (volume.restrict (Ioi 0)) := by
  have hI := h.momentIntegrable (k + 1)
  change Integrable (momentIntegrand h (k + 1)) (volume.restrict (Ioi (0 : ℝ))) at hI
  simpa [momentIntegrand, momentB_eq_halfExponent_succ] using hI

theorem momentC_factor_integrable (h : FullSupportMomentWeight) (k : ℕ) :
    Integrable (fun y : ℝ => y ^ (momentC k) * h y) (volume.restrict (Ioi 0)) := by
  have hI := h.momentIntegrable (k + 2)
  change Integrable (momentIntegrand h (k + 2)) (volume.restrict (Ioi (0 : ℝ))) at hI
  simpa [momentIntegrand, momentC_eq_halfExponent_add_two] using hI

/-- The real nonnegative density inside the manuscript envelope `A_k` on the ordered region. -/
def curvatureEnvelopeDensity
    (h : FullSupportMomentWeight) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  (p.1 * p.2) ^ (momentA k) * (p.2 - p.1) * |tau h k - p.1 * p.2| * h p.1 * h p.2

/-- A separable four-term majorant for the absolute curvature-envelope density.  Its factors
are precisely the `a_k`, `b_k`, and `c_k` moment densities. -/
def curvatureEnvelopeMomentMajorant
    (h : FullSupportMomentWeight) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  |tau h k| *
      ((p.1 ^ (momentA k) * h p.1) * (p.2 ^ (momentB k) * h p.2) +
       (p.1 ^ (momentB k) * h p.1) * (p.2 ^ (momentA k) * h p.2)) +
    ((p.1 ^ (momentB k) * h p.1) * (p.2 ^ (momentC k) * h p.2) +
     (p.1 ^ (momentC k) * h p.1) * (p.2 ^ (momentB k) * h p.2))

/-- The four-term moment majorant is integrable on the whole positive quadrant. -/
theorem curvatureEnvelopeMomentMajorant_integrableOn_positiveProduct
    (h : FullSupportMomentWeight) (k : ℕ) :
    IntegrableOn (curvatureEnvelopeMomentMajorant h k)
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (volume.prod volume) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hA : Integrable (fun y : ℝ => y ^ (momentA k) * h y) μ :=
    momentA_factor_integrable h k
  have hB : Integrable (fun y : ℝ => y ^ (momentB k) * h y) μ :=
    momentB_factor_integrable h k
  have hC : Integrable (fun y : ℝ => y ^ (momentC k) * h y) μ :=
    momentC_factor_integrable h k
  have hAB : Integrable
      (fun p : ℝ × ℝ =>
        (p.1 ^ (momentA k) * h p.1) * (p.2 ^ (momentB k) * h p.2)) (μ.prod μ) :=
    hA.mul_prod hB
  have hBA : Integrable
      (fun p : ℝ × ℝ =>
        (p.1 ^ (momentB k) * h p.1) * (p.2 ^ (momentA k) * h p.2)) (μ.prod μ) :=
    hB.mul_prod hA
  have hBC : Integrable
      (fun p : ℝ × ℝ =>
        (p.1 ^ (momentB k) * h p.1) * (p.2 ^ (momentC k) * h p.2)) (μ.prod μ) :=
    hB.mul_prod hC
  have hCB : Integrable
      (fun p : ℝ × ℝ =>
        (p.1 ^ (momentC k) * h p.1) * (p.2 ^ (momentB k) * h p.2)) (μ.prod μ) :=
    hC.mul_prod hB
  have hmaj : Integrable (curvatureEnvelopeMomentMajorant h k) (μ.prod μ) := by
    unfold curvatureEnvelopeMomentMajorant
    exact ((hAB.add hBA).const_mul |tau h k|).add (hBC.add hCB)
  change Integrable (curvatureEnvelopeMomentMajorant h k)
    ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
  simpa [μ, Measure.prod_restrict] using hmaj

/-- Pointwise domination on the positive quadrant.  Algebraically this is the manuscript bound
`|z-y| ≤ y+z`, `|τ-yz| ≤ |τ|+yz`, followed by expansion into the three consecutive moments. -/
theorem abs_curvatureEnvelopeDensity_le_momentMajorant
    (h : FullSupportMomentWeight) (k : ℕ) {y z : ℝ}
    (hy : 0 < y) (hz : 0 < z) :
    |curvatureEnvelopeDensity h k (y, z)| ≤
      curvatureEnvelopeMomentMajorant h k (y, z) := by
  have hy0 : 0 ≤ y := hy.le
  have hz0 : 0 ≤ z := hz.le
  have hyz0 : 0 ≤ y * z := mul_nonneg hy0 hz0
  have hp : 0 ≤ (y * z) ^ (momentA k) := Real.rpow_nonneg hyz0 _
  have hhy : 0 ≤ h y := h.nonneg hy
  have hhz : 0 ≤ h z := h.nonneg hz
  have hdiff : |z - y| ≤ y + z := by
    calc
      |z - y| ≤ |z| + |y| := abs_sub z y
      _ = y + z := by rw [abs_of_pos hz, abs_of_pos hy]; ring
  have htau : |tau h k - y * z| ≤ |tau h k| + y * z := by
    calc
      |tau h k - y * z| ≤ |tau h k| + |y * z| := abs_sub _ _
      _ = |tau h k| + y * z := by rw [abs_of_nonneg hyz0]
  have hcore :
      (y * z) ^ (momentA k) * |z - y| * |tau h k - y * z| ≤
        (y * z) ^ (momentA k) * (y + z) * (|tau h k| + y * z) := by
    gcongr
  have hprod :
      (y * z) ^ (momentA k) * |z - y| * |tau h k - y * z| * h y * h z ≤
        (y * z) ^ (momentA k) * (y + z) * (|tau h k| + y * z) * h y * h z := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcore hhy) hhz
  have hyB : y ^ (momentB k) = y ^ (momentA k) * y := by
    rw [momentB_eq_A_add_one, Real.rpow_add hy, Real.rpow_one]
  have hzB : z ^ (momentB k) = z ^ (momentA k) * z := by
    rw [momentB_eq_A_add_one, Real.rpow_add hz, Real.rpow_one]
  have hyC : y ^ (momentC k) = y ^ (momentB k) * y := by
    rw [momentC_eq_B_add_one, Real.rpow_add hy, Real.rpow_one]
  have hzC : z ^ (momentC k) = z ^ (momentB k) * z := by
    rw [momentC_eq_B_add_one, Real.rpow_add hz, Real.rpow_one]
  calc
    |curvatureEnvelopeDensity h k (y, z)| =
        (y * z) ^ (momentA k) * |z - y| * |tau h k - y * z| * h y * h z := by
      simp only [curvatureEnvelopeDensity, abs_mul, abs_abs,
        abs_of_nonneg hp, abs_of_nonneg hhy, abs_of_nonneg hhz]
    _ ≤ (y * z) ^ (momentA k) * (y + z) * (|tau h k| + y * z) * h y * h z := hprod
    _ = curvatureEnvelopeMomentMajorant h k (y, z) := by
      unfold curvatureEnvelopeMomentMajorant
      rw [Real.mul_rpow hy0 hz0, hyB, hzB, hyC, hzC]
      ring

/-- A globally measurable representative of the envelope density on the positive quadrant.
It agrees there with the `rpow` expression by the positive-base formula. -/
def curvatureEnvelopeDensityMeasurableRep
    (h : FullSupportMomentWeight) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (Real.log (p.1 * p.2) * momentA k) * (p.2 - p.1) *
    |tau h k - p.1 * p.2| * h p.1 * h p.2

lemma curvatureEnvelopeDensityMeasurableRep_measurable
    (h : FullSupportMomentWeight) (k : ℕ) :
    Measurable (curvatureEnvelopeDensityMeasurableRep h k) := by
  unfold curvatureEnvelopeDensityMeasurableRep
  fun_prop

/-- The actual envelope density is strongly measurable on the positive quadrant. -/
theorem curvatureEnvelopeDensity_aestronglyMeasurableOn_positiveProduct
    (h : FullSupportMomentWeight) (k : ℕ) :
    AEStronglyMeasurable (curvatureEnvelopeDensity h k)
      ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) := by
  have hrep : AEStronglyMeasurable (curvatureEnvelopeDensityMeasurableRep h k)
      ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) :=
    (curvatureEnvelopeDensityMeasurableRep_measurable h k).aestronglyMeasurable
  have heq : curvatureEnvelopeDensity h k =ᵐ[
      (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))]
      curvatureEnvelopeDensityMeasurableRep h k := by
    rw [ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
    filter_upwards with p hp
    unfold curvatureEnvelopeDensity curvatureEnvelopeDensityMeasurableRep
    rw [Real.rpow_def_of_pos (mul_pos hp.1 hp.2)]
  exact hrep.congr heq.symm

/-- Finiteness of the envelope's double integral is a consequence of the moment assumptions alone.
This is the key prerequisite before converting the manuscript's ordinary integrals to `lintegral`. -/
theorem curvatureEnvelopeDensity_integrableOn_positiveProduct
    (h : FullSupportMomentWeight) (k : ℕ) :
    IntegrableOn (curvatureEnvelopeDensity h k)
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (volume.prod volume) := by
  have hmaj := curvatureEnvelopeMomentMajorant_integrableOn_positiveProduct h k
  apply hmaj.mono'
  · exact curvatureEnvelopeDensity_aestronglyMeasurableOn_positiveProduct h k
  · rw [ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
    filter_upwards with p hp
    exact abs_curvatureEnvelopeDensity_le_momentMajorant h k hp.1 hp.2

/-- For every `u>0`, the manuscript rectangle `0<y≤u<z` inherits the same integrability. -/
theorem curvatureEnvelopeDensity_integrableOn_rectangle
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (curvatureEnvelopeDensity h k)
      (Ioc (0 : ℝ) u ×ˢ Ioi u) (volume.prod volume) := by
  apply (curvatureEnvelopeDensity_integrableOn_positiveProduct h k).mono_set
  rintro ⟨y, z⟩ ⟨hy, hz⟩
  exact ⟨hy.1, lt_trans hu hz⟩

/-- On the manuscript rectangle the envelope density is nonnegative. -/
theorem curvatureEnvelopeDensity_nonneg_on_rectangle
    (h : FullSupportMomentWeight) (k : ℕ) {u y z : ℝ}
    (hu : 0 < u) (hy : y ∈ Ioc (0 : ℝ) u) (hz : z ∈ Ioi u) :
    0 ≤ curvatureEnvelopeDensity h k (y, z) := by
  have hy0 : 0 ≤ y := hy.1.le
  have hzpos : 0 < z := lt_trans hu hz
  have hz0 : 0 ≤ z := hzpos.le
  have hp : 0 ≤ (y * z) ^ (momentA k) :=
    Real.rpow_nonneg (mul_nonneg hy0 hz0) _
  have hzy : 0 ≤ z - y := sub_nonneg.mpr (le_trans hy.2 hz.le)
  have hhy : 0 ≤ h y := h.nonneg hy.1
  have hhz : 0 ≤ h z := h.nonneg hzpos
  unfold curvatureEnvelopeDensity
  positivity

/-- Fubini identifies the nested ordinary integral in the definition of `A_k(u)` with the
product integral once the moment-derived integrability has been established. -/
theorem curvatureEnvelope_eq_two_mul_productIntegral
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    curvatureEnvelope h k u =
      2 * ∫ p in Ioc (0 : ℝ) u ×ˢ Ioi u,
        curvatureEnvelopeDensity h k p ∂(volume.prod volume) := by
  rw [curvatureEnvelope]
  have hf := curvatureEnvelopeDensity_integrableOn_rectangle h k hu
  rw [MeasureTheory.setIntegral_prod (curvatureEnvelopeDensity h k) hf]
  rfl

/-- Exact bridge from the manuscript envelope `A_k(u)` to its nonnegative `lintegral`
representation.  In particular this proves, before the Tonelli/Fubini rearrangement, that the
ordinary double integral defining `A_k(u)` is finite. -/
theorem ofReal_curvatureEnvelope_eq_two_mul_lintegral
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    ENNReal.ofReal (curvatureEnvelope h k u) =
      2 * ∫⁻ p in Ioc (0 : ℝ) u ×ˢ Ioi u,
        ENNReal.ofReal (curvatureEnvelopeDensity h k p) ∂(volume.prod volume) := by
  rw [curvatureEnvelope_eq_two_mul_productIntegral h k hu]
  have hf := curvatureEnvelopeDensity_integrableOn_rectangle h k hu
  have hnn :
      0 ≤ᵐ[(volume.prod volume).restrict (Ioc (0 : ℝ) u ×ˢ Ioi u)]
        curvatureEnvelopeDensity h k := by
    change ∀ᵐ p ∂(volume.prod volume).restrict (Ioc (0 : ℝ) u ×ˢ Ioi u),
      0 ≤ curvatureEnvelopeDensity h k p
    rw [ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioi)]
    filter_upwards with p hp
    exact curvatureEnvelopeDensity_nonneg_on_rectangle h k hu hp.1 hp.2
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [ENNReal.ofReal_ofNat]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf hnn]

end CrossBoundaryMomentKernels
