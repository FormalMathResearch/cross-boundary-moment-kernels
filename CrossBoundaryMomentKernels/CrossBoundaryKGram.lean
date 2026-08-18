import CrossBoundaryMomentKernels.SizeBiasShift

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- The two-copy Gram square for the cross-boundary `K`-moment sequence. -/
def crossBoundaryKGramIntegrand
    (h : ℝ → ℝ) (k : ℕ) (P : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  crossBoundaryIntegrand h k P.1 * crossBoundaryIntegrand h k P.2 *
    (crossBoundaryProduct P.1 - crossBoundaryProduct P.2) ^ 2

/-- Linear symmetrized normal form of the two-copy Gram square. -/
def crossBoundaryKGramLinear
    (h : ℝ → ℝ) (k : ℕ) (P : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  crossBoundaryIntegrand h k P.1 * crossBoundaryIntegrand h (k + 2) P.2 +
    crossBoundaryIntegrand h (k + 2) P.1 * crossBoundaryIntegrand h k P.2 -
      (crossBoundaryIntegrand h (k + 1) P.1 * crossBoundaryIntegrand h (k + 1) P.2 +
        crossBoundaryIntegrand h (k + 1) P.1 * crossBoundaryIntegrand h (k + 1) P.2)

/-- The linear normal form equals the manifest square whenever both cross-boundary points
have positive coordinates. -/
lemma crossBoundaryKGramLinear_eq_of_pos
    (h : FullSupportMomentWeight) (k : ℕ)
    {p q : ℝ × ℝ} (hp1 : 0 < p.1) (hp2 : 0 < p.2)
    (hq1 : 0 < q.1) (hq2 : 0 < q.2) :
    crossBoundaryKGramLinear h k (p, q) = crossBoundaryKGramIntegrand h k (p, q) := by
  have hpK1 := crossBoundaryIntegrand_add_index h k 1 hp1 hp2
  have hpK2 := crossBoundaryIntegrand_add_index h k 2 hp1 hp2
  have hqK1 := crossBoundaryIntegrand_add_index h k 1 hq1 hq2
  have hqK2 := crossBoundaryIntegrand_add_index h k 2 hq1 hq2
  rw [crossBoundaryKGramLinear, crossBoundaryKGramIntegrand, hpK1, hpK2, hqK1, hqK2]
  simp only [pow_one, pow_two]
  ring

/-- The two-copy Gram square is integrable. -/
lemma crossBoundaryKGramIntegrand_integrable
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    Integrable (crossBoundaryKGramIntegrand h k)
      ((crossBoundaryBaseMeasure u).prod (crossBoundaryBaseMeasure u)) := by
  let μ : Measure (ℝ × ℝ) := crossBoundaryBaseMeasure u
  letI : SFinite μ := by
    dsimp [μ, crossBoundaryBaseMeasure]
    infer_instance
  have hk : Integrable (crossBoundaryIntegrand h k) μ :=
    crossBoundaryIntegrand_integrable_base h k hu
  have hk1 : Integrable (crossBoundaryIntegrand h (k + 1)) μ :=
    crossBoundaryIntegrand_integrable_base h (k + 1) hu
  have hk2 : Integrable (crossBoundaryIntegrand h (k + 2)) μ :=
    crossBoundaryIntegrand_integrable_base h (k + 2) hu
  have ht1 : Integrable
      (fun P : (ℝ × ℝ) × (ℝ × ℝ) ↦
        crossBoundaryIntegrand h k P.1 * crossBoundaryIntegrand h (k + 2) P.2)
      (μ.prod μ) := hk.mul_prod hk2
  have ht2 : Integrable
      (fun P : (ℝ × ℝ) × (ℝ × ℝ) ↦
        crossBoundaryIntegrand h (k + 2) P.1 * crossBoundaryIntegrand h k P.2)
      (μ.prod μ) := hk2.mul_prod hk
  have ht3 : Integrable
      (fun P : (ℝ × ℝ) × (ℝ × ℝ) ↦
        crossBoundaryIntegrand h (k + 1) P.1 * crossBoundaryIntegrand h (k + 1) P.2)
      (μ.prod μ) := hk1.mul_prod hk1
  have hlin : Integrable (crossBoundaryKGramLinear h k) (μ.prod μ) := by
    change Integrable
      (fun P : (ℝ × ℝ) × (ℝ × ℝ) ↦
        crossBoundaryIntegrand h k P.1 * crossBoundaryIntegrand h (k + 2) P.2 +
          crossBoundaryIntegrand h (k + 2) P.1 * crossBoundaryIntegrand h k P.2 -
            (crossBoundaryIntegrand h (k + 1) P.1 * crossBoundaryIntegrand h (k + 1) P.2 +
              crossBoundaryIntegrand h (k + 1) P.1 * crossBoundaryIntegrand h (k + 1) P.2))
      (μ.prod μ)
    exact (ht1.add ht2).sub (ht3.add ht3)
  have hrect : ∀ᵐ p ∂μ, p ∈ Ioc (0 : ℝ) u ×ˢ Ioi u := by
    simpa [μ] using ae_mem_crossBoundaryRect u
  have hpair : ∀ᵐ P ∂(μ.prod μ),
      P.1 ∈ Ioc (0 : ℝ) u ×ˢ Ioi u ∧ P.2 ∈ Ioc (0 : ℝ) u ×ˢ Ioi u := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      ((measurableSet_Ioc.prod measurableSet_Ioi).prod
        (measurableSet_Ioc.prod measurableSet_Ioi))).2 ?_
    filter_upwards [hrect] with p hp
    filter_upwards [hrect] with q hq
    exact ⟨hp, hq⟩
  have hEq : crossBoundaryKGramLinear h k =ᵐ[μ.prod μ] crossBoundaryKGramIntegrand h k := by
    filter_upwards [hpair] with P hP
    have hp2 : 0 < P.1.2 := lt_trans hu hP.1.2
    have hq2 : 0 < P.2.2 := lt_trans hu hP.2.2
    exact crossBoundaryKGramLinear_eq_of_pos h k hP.1.1.1 hp2 hP.2.1.1 hq2
  simpa [μ] using hlin.congr hEq

/-- Exact two-copy Gram identity for the `K` hierarchy. -/
theorem integral_crossBoundaryKGramIntegrand
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    ∫ P, crossBoundaryKGramIntegrand h k P
        ∂((crossBoundaryBaseMeasure u).prod (crossBoundaryBaseMeasure u)) =
      2 * (K h k u * K h (k + 2) u - (K h (k + 1) u) ^ 2) := by
  let μ : Measure (ℝ × ℝ) := crossBoundaryBaseMeasure u
  letI : SFinite μ := by
    dsimp [μ, crossBoundaryBaseMeasure]
    infer_instance
  have hk : Integrable (crossBoundaryIntegrand h k) μ :=
    crossBoundaryIntegrand_integrable_base h k hu
  have hk1 : Integrable (crossBoundaryIntegrand h (k + 1)) μ :=
    crossBoundaryIntegrand_integrable_base h (k + 1) hu
  have hk2 : Integrable (crossBoundaryIntegrand h (k + 2)) μ :=
    crossBoundaryIntegrand_integrable_base h (k + 2) hu
  have ht1 : Integrable
      (fun P : (ℝ × ℝ) × (ℝ × ℝ) ↦
        crossBoundaryIntegrand h k P.1 * crossBoundaryIntegrand h (k + 2) P.2)
      (μ.prod μ) := hk.mul_prod hk2
  have ht2 : Integrable
      (fun P : (ℝ × ℝ) × (ℝ × ℝ) ↦
        crossBoundaryIntegrand h (k + 2) P.1 * crossBoundaryIntegrand h k P.2)
      (μ.prod μ) := hk2.mul_prod hk
  have ht3 : Integrable
      (fun P : (ℝ × ℝ) × (ℝ × ℝ) ↦
        crossBoundaryIntegrand h (k + 1) P.1 * crossBoundaryIntegrand h (k + 1) P.2)
      (μ.prod μ) := hk1.mul_prod hk1
  have hkInt : ∫ p, crossBoundaryIntegrand h k p ∂μ = K h k u := by
    simpa [μ, crossBoundaryBaseMeasure] using (K_eq_crossBoundaryIntegral h k hu).symm
  have hk1Int : ∫ p, crossBoundaryIntegrand h (k + 1) p ∂μ = K h (k + 1) u := by
    simpa [μ, crossBoundaryBaseMeasure] using
      (K_eq_crossBoundaryIntegral h (k + 1) hu).symm
  have hk2Int : ∫ p, crossBoundaryIntegrand h (k + 2) p ∂μ = K h (k + 2) u := by
    simpa [μ, crossBoundaryBaseMeasure] using
      (K_eq_crossBoundaryIntegral h (k + 2) hu).symm
  have hlinInt :
      ∫ P, crossBoundaryKGramLinear h k P ∂(μ.prod μ) =
        2 * (K h k u * K h (k + 2) u - (K h (k + 1) u) ^ 2) := by
    calc
      ∫ P, crossBoundaryKGramLinear h k P ∂(μ.prod μ) =
          (∫ P,
            crossBoundaryIntegrand h k P.1 * crossBoundaryIntegrand h (k + 2) P.2 +
              crossBoundaryIntegrand h (k + 2) P.1 * crossBoundaryIntegrand h k P.2
            ∂(μ.prod μ)) -
          ∫ P,
            crossBoundaryIntegrand h (k + 1) P.1 * crossBoundaryIntegrand h (k + 1) P.2 +
              crossBoundaryIntegrand h (k + 1) P.1 * crossBoundaryIntegrand h (k + 1) P.2
            ∂(μ.prod μ) := by
          change (∫ P,
            (crossBoundaryIntegrand h k P.1 * crossBoundaryIntegrand h (k + 2) P.2 +
              crossBoundaryIntegrand h (k + 2) P.1 * crossBoundaryIntegrand h k P.2) -
            (crossBoundaryIntegrand h (k + 1) P.1 * crossBoundaryIntegrand h (k + 1) P.2 +
              crossBoundaryIntegrand h (k + 1) P.1 * crossBoundaryIntegrand h (k + 1) P.2)
            ∂(μ.prod μ)) = _
          exact integral_sub (ht1.add ht2) (ht3.add ht3)
      _ =
          ((∫ P, crossBoundaryIntegrand h k P.1 * crossBoundaryIntegrand h (k + 2) P.2
              ∂(μ.prod μ)) +
            (∫ P, crossBoundaryIntegrand h (k + 2) P.1 * crossBoundaryIntegrand h k P.2
              ∂(μ.prod μ))) -
          ((∫ P, crossBoundaryIntegrand h (k + 1) P.1 * crossBoundaryIntegrand h (k + 1) P.2
              ∂(μ.prod μ)) +
            (∫ P, crossBoundaryIntegrand h (k + 1) P.1 * crossBoundaryIntegrand h (k + 1) P.2
              ∂(μ.prod μ))) := by
          rw [integral_add ht1 ht2, integral_add ht3 ht3]
      _ =
          K h k u * K h (k + 2) u + K h (k + 2) u * K h k u -
            (K h (k + 1) u * K h (k + 1) u + K h (k + 1) u * K h (k + 1) u) := by
          rw [integral_prod_mul, hkInt, hk1Int, hk2Int]
      _ = 2 * (K h k u * K h (k + 2) u - (K h (k + 1) u) ^ 2) := by ring
  have hrect : ∀ᵐ p ∂μ, p ∈ Ioc (0 : ℝ) u ×ˢ Ioi u := by
    simpa [μ] using ae_mem_crossBoundaryRect u
  have hpair : ∀ᵐ P ∂(μ.prod μ),
      P.1 ∈ Ioc (0 : ℝ) u ×ˢ Ioi u ∧ P.2 ∈ Ioc (0 : ℝ) u ×ˢ Ioi u := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      ((measurableSet_Ioc.prod measurableSet_Ioi).prod
        (measurableSet_Ioc.prod measurableSet_Ioi))).2 ?_
    filter_upwards [hrect] with p hp
    filter_upwards [hrect] with q hq
    exact ⟨hp, hq⟩
  calc
    ∫ P, crossBoundaryKGramIntegrand h k P ∂(μ.prod μ) =
        ∫ P, crossBoundaryKGramLinear h k P ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [hpair] with P hP
      have hp2 : 0 < P.1.2 := lt_trans hu hP.1.2
      have hq2 : 0 < P.2.2 := lt_trans hu hP.2.2
      exact (crossBoundaryKGramLinear_eq_of_pos h k hP.1.1.1 hp2 hP.2.1.1 hq2).symm
    _ = 2 * (K h k u * K h (k + 2) u - (K h (k + 1) u) ^ 2) := hlinInt

/-- Full support makes the two-copy cross-boundary Gram square strictly positive. -/
lemma integral_crossBoundaryKGramIntegrand_pos
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    0 < ∫ P, crossBoundaryKGramIntegrand h k P
      ∂((crossBoundaryBaseMeasure u).prod (crossBoundaryBaseMeasure u)) := by
  let μL : Measure ℝ := volume.restrict (Ioc (0 : ℝ) u)
  let μR : Measure ℝ := volume.restrict (Ioi u)
  let μ : Measure (ℝ × ℝ) := μL.prod μR
  letI : SFinite μ := by
    dsimp [μ, μL, μR]
    infer_instance
  let A : Set ℝ := Function.support (h : ℝ → ℝ) ∩ Ioc (u / 4) (u / 3)
  let B : Set ℝ := Function.support (h : ℝ → ℝ) ∩ Ioc (2 * u / 3) (3 * u / 4)
  let C : Set ℝ := Function.support (h : ℝ → ℝ) ∩ Ioc (2 * u) (5 * u / 2)
  let Slo : Set (ℝ × ℝ) := A ×ˢ C
  let Shi : Set (ℝ × ℝ) := B ×ˢ C
  have hAvol : 0 < volume A := by
    dsimp [A]
    exact support_h_measure_pos_Ioc h (by nlinarith [hu]) (by nlinarith [hu])
  have hBvol : 0 < volume B := by
    dsimp [B]
    exact support_h_measure_pos_Ioc h (by nlinarith [hu]) (by nlinarith [hu])
  have hCvol : 0 < volume C := by
    dsimp [C]
    exact support_h_measure_pos_Ioc h (by nlinarith [hu]) (by nlinarith [hu])
  have hμLA : 0 < μL A := by
    dsimp [μL, A]
    rw [Measure.restrict_apply' measurableSet_Ioc]
    have hsub : Function.support (h : ℝ → ℝ) ∩ Ioc (u / 4) (u / 3) ⊆ Ioc (0 : ℝ) u := by
      intro y hy
      exact ⟨by nlinarith [hy.2.1, hu], by nlinarith [hy.2.2, hu]⟩
    rw [inter_eq_left.2 hsub]
    exact hAvol
  have hμLB : 0 < μL B := by
    dsimp [μL, B]
    rw [Measure.restrict_apply' measurableSet_Ioc]
    have hsub : Function.support (h : ℝ → ℝ) ∩ Ioc (2 * u / 3) (3 * u / 4) ⊆ Ioc (0 : ℝ) u := by
      intro y hy
      exact ⟨by nlinarith [hy.2.1, hu], by nlinarith [hy.2.2, hu]⟩
    rw [inter_eq_left.2 hsub]
    exact hBvol
  have hμRC : 0 < μR C := by
    dsimp [μR, C]
    rw [Measure.restrict_apply' measurableSet_Ioi]
    have hsub : Function.support (h : ℝ → ℝ) ∩ Ioc (2 * u) (5 * u / 2) ⊆ Ioi u := by
      intro z hz
      change u < z
      nlinarith [hz.2.1, hu]
    rw [inter_eq_left.2 hsub]
    exact hCvol
  have hSlo : 0 < μ Slo := by
    dsimp [μ, Slo]
    rw [Measure.prod_prod, CanonicallyOrderedAdd.mul_pos]
    exact ⟨hμLA, hμRC⟩
  have hShi : 0 < μ Shi := by
    dsimp [μ, Shi]
    rw [Measure.prod_prod, CanonicallyOrderedAdd.mul_pos]
    exact ⟨hμLB, hμRC⟩
  have hpairPos : 0 < (μ.prod μ) (Slo ×ˢ Shi) := by
    rw [Measure.prod_prod, CanonicallyOrderedAdd.mul_pos]
    exact ⟨hSlo, hShi⟩
  have hsupport : Slo ×ˢ Shi ⊆ Function.support (crossBoundaryKGramIntegrand h k) := by
    intro P hP
    rcases hP with ⟨hpLo, hqHi⟩
    rcases hpLo with ⟨hyA, hzC⟩
    rcases hqHi with ⟨hyB, hzC'⟩
    change P.1.1 ∈ Function.support (h : ℝ → ℝ) ∩ Ioc (u / 4) (u / 3) at hyA
    change P.1.2 ∈ Function.support (h : ℝ → ℝ) ∩ Ioc (2 * u) (5 * u / 2) at hzC
    change P.2.1 ∈ Function.support (h : ℝ → ℝ) ∩ Ioc (2 * u / 3) (3 * u / 4) at hyB
    change P.2.2 ∈ Function.support (h : ℝ → ℝ) ∩ Ioc (2 * u) (5 * u / 2) at hzC'
    have hpY0 : 0 < P.1.1 := by nlinarith [hyA.2.1, hu]
    have hpZ0 : 0 < P.1.2 := by nlinarith [hzC.2.1, hu]
    have hqY0 : 0 < P.2.1 := by nlinarith [hyB.2.1, hu]
    have hqZ0 : 0 < P.2.2 := by nlinarith [hzC'.2.1, hu]
    have hpYZ : P.1.1 < P.1.2 := by nlinarith [hyA.2.2, hzC.2.1, hu]
    have hqYZ : P.2.1 < P.2.2 := by nlinarith [hyB.2.2, hzC'.2.1, hu]
    have hpInt : 0 < crossBoundaryIntegrand h k P.1 := by
      rw [crossBoundaryIntegrand]
      exact mul_pos
        (mul_pos
          (momentIntegrand_pos_of_mem_support h k hpY0 hyA.1)
          (momentIntegrand_pos_of_mem_support h k hpZ0 hzC.1))
        (sub_pos.mpr hpYZ)
    have hqInt : 0 < crossBoundaryIntegrand h k P.2 := by
      rw [crossBoundaryIntegrand]
      exact mul_pos
        (mul_pos
          (momentIntegrand_pos_of_mem_support h k hqY0 hyB.1)
          (momentIntegrand_pos_of_mem_support h k hqZ0 hzC'.1))
        (sub_pos.mpr hqYZ)
    have hpXlt : crossBoundaryProduct P.1 < u ^ 2 := by
      rw [crossBoundaryProduct]
      nlinarith [hyA.2.2, hzC.2.2, hu]
    have hqXgt : u ^ 2 < crossBoundaryProduct P.2 := by
      rw [crossBoundaryProduct]
      nlinarith [hyB.2.1, hzC'.2.1, hu]
    have hsq : 0 < (crossBoundaryProduct P.1 - crossBoundaryProduct P.2) ^ 2 := by
      nlinarith
    show crossBoundaryKGramIntegrand h k P ≠ 0
    rw [crossBoundaryKGramIntegrand]
    exact ne_of_gt (mul_pos (mul_pos hpInt hqInt) hsq)
  have hSupportPos : 0 < (μ.prod μ) (Function.support (crossBoundaryKGramIntegrand h k)) :=
    lt_of_lt_of_le hpairPos (measure_mono hsupport)
  have hInt : Integrable (crossBoundaryKGramIntegrand h k) (μ.prod μ) := by
    simpa [μ, μL, μR, crossBoundaryBaseMeasure] using
      crossBoundaryKGramIntegrand_integrable h k hu
  have hrect : ∀ᵐ p ∂μ, p ∈ Ioc (0 : ℝ) u ×ˢ Ioi u := by
    simpa [μ, μL, μR, crossBoundaryBaseMeasure] using ae_mem_crossBoundaryRect u
  have hpair : ∀ᵐ P ∂(μ.prod μ),
      P.1 ∈ Ioc (0 : ℝ) u ×ˢ Ioi u ∧ P.2 ∈ Ioc (0 : ℝ) u ×ˢ Ioi u := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      ((measurableSet_Ioc.prod measurableSet_Ioi).prod
        (measurableSet_Ioc.prod measurableSet_Ioi))).2 ?_
    filter_upwards [hrect] with p hp
    filter_upwards [hrect] with q hq
    exact ⟨hp, hq⟩
  have hNonneg : 0 ≤ᵐ[μ.prod μ] crossBoundaryKGramIntegrand h k := by
    filter_upwards [hpair] with P hP
    have hpZ0 : 0 < P.1.2 := lt_trans hu hP.1.2
    have hqZ0 : 0 < P.2.2 := lt_trans hu hP.2.2
    have hpYZ : P.1.1 < P.1.2 := lt_of_le_of_lt hP.1.1.2 hP.1.2
    have hqYZ : P.2.1 < P.2.2 := lt_of_le_of_lt hP.2.1.2 hP.2.2
    rw [crossBoundaryKGramIntegrand, crossBoundaryIntegrand, crossBoundaryIntegrand]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (momentIntegrand_nonneg h k hP.1.1.1)
            (momentIntegrand_nonneg h k hpZ0))
          (sub_nonneg.mpr hpYZ.le))
        (mul_nonneg
          (mul_nonneg (momentIntegrand_nonneg h k hP.2.1.1)
            (momentIntegrand_nonneg h k hqZ0))
          (sub_nonneg.mpr hqYZ.le)))
      (sq_nonneg _)
  have hpos : 0 < ∫ P, crossBoundaryKGramIntegrand h k P ∂(μ.prod μ) :=
    (integral_pos_iff_support_of_nonneg_ae hNonneg hInt).2 hSupportPos
  simpa [μ, μL, μR, crossBoundaryBaseMeasure] using hpos

/-- Strict log-convexity of the cross-boundary kernel sequence in its discrete index. -/
theorem strict_crossBoundary_K_logConvexity
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    (K h (k + 1) u) ^ 2 < K h k u * K h (k + 2) u := by
  have hId := integral_crossBoundaryKGramIntegrand h k hu
  have hPos := integral_crossBoundaryKGramIntegrand_pos h k hu
  nlinarith

end CrossBoundaryMomentKernels
