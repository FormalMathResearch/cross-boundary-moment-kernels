import CrossBoundaryMomentKernels.TotalPositivityHierarchy

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- The truncated mean `μ_k(u) = J_{k+2}(u) / J_{k+1}(u)` from Theorem 2.2(v). -/
def truncatedMu (h : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  J h (k + 2) u / J h (k + 1) u

/-- The truncated variance term
`v_k(u) = J_{k+3}(u) / J_{k+1}(u) - μ_k(u)^2` from Theorem 2.2(v). -/
def truncatedVar (h : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  J h (k + 3) u / J h (k + 1) u - (truncatedMu h k u) ^ 2

/-- The factorized Gram integrand on the truncated product domain. -/
def truncatedGramIntegrand (h : ℝ → ℝ) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  momentIntegrand h j p.1 * momentIntegrand h j p.2 * (p.1 - p.2) ^ 2

/-- The linear symmetrized normal form used to establish integrability of the Gram integrand. -/
def truncatedGramLinearIntegrand (h : ℝ → ℝ) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  momentIntegrand h j p.1 * momentIntegrand h (j + 2) p.2 +
    momentIntegrand h (j + 2) p.1 * momentIntegrand h j p.2 -
      (momentIntegrand h (j + 1) p.1 * momentIntegrand h (j + 1) p.2 +
        momentIntegrand h (j + 1) p.1 * momentIntegrand h (j + 1) p.2)

/-- Every moment integrand is integrable on a positive truncated interval. -/
lemma momentIntegrand_integrable_Ioc
    (h : FullSupportMomentWeight) (j : ℕ) (u : ℝ) :
    Integrable (momentIntegrand h j) (volume.restrict (Ioc (0 : ℝ) u)) := by
  simpa [IntegrableOn] using
    (h.momentIntegrable j).mono_set (by intro x hx; exact hx.1)

/-- Every truncated half-integer moment is strictly positive at a positive truncation point. -/
lemma J_pos (h : FullSupportMomentWeight) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    0 < J h j u := by
  have hInt : IntegrableOn (momentIntegrand h j) (Ioc (0 : ℝ) u) :=
    (h.momentIntegrable j).mono_set (by intro x hx; exact hx.1)
  have hNonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) u)] momentIntegrand h j := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with x hx
    exact momentIntegrand_nonneg h j hx.1
  have hsupp :
      Function.support (h : ℝ → ℝ) ∩ Ioc (u / 2) u ⊆
        Function.support (momentIntegrand h j) ∩ Ioc (0 : ℝ) u := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.2.1, hu]
    refine ⟨?_, ⟨hx0, hx.2.2⟩⟩
    exact ne_of_gt (momentIntegrand_pos_of_mem_support h j hx0 hx.1)
  have hSuppPos :
      0 < volume (Function.support (momentIntegrand h j) ∩ Ioc (0 : ℝ) u) := by
    have hinner :
        0 < volume (Function.support (h : ℝ → ℝ) ∩ Ioc (u / 2) u) :=
      support_h_measure_pos_Ioc h (by linarith [hu]) (by linarith [hu])
    exact lt_of_lt_of_le hinner (measure_mono hsupp)
  have hpos :
      0 < ∫ x, momentIntegrand h j x ∂(volume.restrict (Ioc (0 : ℝ) u)) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hNonneg hInt).2 hSuppPos
  simpa [J] using hpos

/-- The linear symmetrized integrand equals the manifest square form on the positive quadrant. -/
lemma truncatedGramLinearIntegrand_eq
    (h : FullSupportMomentWeight) (j : ℕ) {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    truncatedGramLinearIntegrand h j (y, z) = truncatedGramIntegrand h j (y, z) := by
  have hy₁ : momentIntegrand h (j + 1) y = y * momentIntegrand h j y :=
    momentIntegrand_succ h j hy
  have hz₁ : momentIntegrand h (j + 1) z = z * momentIntegrand h j z :=
    momentIntegrand_succ h j hz
  have hy₂ : momentIntegrand h (j + 2) y = y * momentIntegrand h (j + 1) y := by
    convert momentIntegrand_succ h (j + 1) hy using 1
  have hz₂ : momentIntegrand h (j + 2) z = z * momentIntegrand h (j + 1) z := by
    convert momentIntegrand_succ h (j + 1) hz using 1
  rw [truncatedGramLinearIntegrand, truncatedGramIntegrand, hy₂, hz₂, hy₁, hz₁]
  ring

/-- The factorized Gram integrand is integrable on every truncated product domain. -/
lemma truncatedGramIntegrand_integrable
    (h : FullSupportMomentWeight) (j : ℕ) {u : ℝ} (_hu : 0 < u) :
    Integrable (truncatedGramIntegrand h j)
      ((volume.restrict (Ioc (0 : ℝ) u)).prod (volume.restrict (Ioc (0 : ℝ) u))) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) u)
  have hj : Integrable (momentIntegrand h j) μ := by
    simpa [μ] using momentIntegrand_integrable_Ioc h j u
  have hj₁ : Integrable (momentIntegrand h (j + 1)) μ := by
    simpa [μ] using momentIntegrand_integrable_Ioc h (j + 1) u
  have hj₂ : Integrable (momentIntegrand h (j + 2)) μ := by
    simpa [μ] using momentIntegrand_integrable_Ioc h (j + 2) u
  have ht₁ : Integrable
      (fun p : ℝ × ℝ ↦ momentIntegrand h j p.1 * momentIntegrand h (j + 2) p.2)
      (μ.prod μ) := hj.mul_prod hj₂
  have ht₂ : Integrable
      (fun p : ℝ × ℝ ↦ momentIntegrand h (j + 2) p.1 * momentIntegrand h j p.2)
      (μ.prod μ) := hj₂.mul_prod hj
  have ht₃ : Integrable
      (fun p : ℝ × ℝ ↦ momentIntegrand h (j + 1) p.1 * momentIntegrand h (j + 1) p.2)
      (μ.prod μ) := hj₁.mul_prod hj₁
  have hlin : Integrable (truncatedGramLinearIntegrand h j) (μ.prod μ) := by
    change Integrable
      (fun p : ℝ × ℝ ↦
        momentIntegrand h j p.1 * momentIntegrand h (j + 2) p.2 +
          momentIntegrand h (j + 2) p.1 * momentIntegrand h j p.2 -
            (momentIntegrand h (j + 1) p.1 * momentIntegrand h (j + 1) p.2 +
              momentIntegrand h (j + 1) p.1 * momentIntegrand h (j + 1) p.2))
      (μ.prod μ)
    exact (ht₁.add ht₂).sub (ht₃.add ht₃)
  have hquadrant : ∀ᵐ p ∂(μ.prod μ), p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioi.prod measurableSet_Ioi)).2 ?_
    have hμpos : ∀ᵐ x ∂μ, 0 < x := by
      dsimp [μ]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hx.1
    filter_upwards [hμpos] with y hy
    filter_upwards [hμpos] with z hz
    exact ⟨hy, hz⟩
  have hcongr :
      truncatedGramLinearIntegrand h j =ᵐ[μ.prod μ] truncatedGramIntegrand h j := by
    filter_upwards [hquadrant] with p hp
    exact truncatedGramLinearIntegrand_eq h j hp.1 hp.2
  simpa [μ] using hlin.congr hcongr

/-- Exact integral of the factorized Gram square. -/
theorem integral_truncatedGramIntegrand
    (h : FullSupportMomentWeight) (j : ℕ) {u : ℝ} (_hu : 0 < u) :
    ∫ p, truncatedGramIntegrand h j p
        ∂((volume.restrict (Ioc (0 : ℝ) u)).prod (volume.restrict (Ioc (0 : ℝ) u))) =
      2 * (J h j u * J h (j + 2) u - (J h (j + 1) u) ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) u)
  have hj : Integrable (momentIntegrand h j) μ := by
    simpa [μ] using momentIntegrand_integrable_Ioc h j u
  have hj₁ : Integrable (momentIntegrand h (j + 1)) μ := by
    simpa [μ] using momentIntegrand_integrable_Ioc h (j + 1) u
  have hj₂ : Integrable (momentIntegrand h (j + 2)) μ := by
    simpa [μ] using momentIntegrand_integrable_Ioc h (j + 2) u
  have ht₁ : Integrable
      (fun p : ℝ × ℝ ↦ momentIntegrand h j p.1 * momentIntegrand h (j + 2) p.2)
      (μ.prod μ) := hj.mul_prod hj₂
  have ht₂ : Integrable
      (fun p : ℝ × ℝ ↦ momentIntegrand h (j + 2) p.1 * momentIntegrand h j p.2)
      (μ.prod μ) := hj₂.mul_prod hj
  have ht₃ : Integrable
      (fun p : ℝ × ℝ ↦ momentIntegrand h (j + 1) p.1 * momentIntegrand h (j + 1) p.2)
      (μ.prod μ) := hj₁.mul_prod hj₁
  have hlinInt :
      ∫ p, truncatedGramLinearIntegrand h j p ∂(μ.prod μ) =
        2 * (J h j u * J h (j + 2) u - (J h (j + 1) u) ^ 2) := by
    calc
      ∫ p, truncatedGramLinearIntegrand h j p ∂(μ.prod μ) =
          (∫ p,
              momentIntegrand h j p.1 * momentIntegrand h (j + 2) p.2 +
                momentIntegrand h (j + 2) p.1 * momentIntegrand h j p.2
              ∂(μ.prod μ)) -
            ∫ p,
              momentIntegrand h (j + 1) p.1 * momentIntegrand h (j + 1) p.2 +
                momentIntegrand h (j + 1) p.1 * momentIntegrand h (j + 1) p.2
              ∂(μ.prod μ) := by
            change
              (∫ p,
                (momentIntegrand h j p.1 * momentIntegrand h (j + 2) p.2 +
                  momentIntegrand h (j + 2) p.1 * momentIntegrand h j p.2) -
                  (momentIntegrand h (j + 1) p.1 * momentIntegrand h (j + 1) p.2 +
                    momentIntegrand h (j + 1) p.1 * momentIntegrand h (j + 1) p.2)
                ∂(μ.prod μ)) = _
            exact integral_sub (ht₁.add ht₂) (ht₃.add ht₃)
      _ =
          ((∫ p, momentIntegrand h j p.1 * momentIntegrand h (j + 2) p.2 ∂(μ.prod μ)) +
            (∫ p, momentIntegrand h (j + 2) p.1 * momentIntegrand h j p.2 ∂(μ.prod μ))) -
              ((∫ p, momentIntegrand h (j + 1) p.1 * momentIntegrand h (j + 1) p.2
                  ∂(μ.prod μ)) +
                (∫ p, momentIntegrand h (j + 1) p.1 * momentIntegrand h (j + 1) p.2
                  ∂(μ.prod μ))) := by
            rw [integral_add ht₁ ht₂, integral_add ht₃ ht₃]
      _ =
          J h j u * J h (j + 2) u + J h (j + 2) u * J h j u -
            (J h (j + 1) u * J h (j + 1) u + J h (j + 1) u * J h (j + 1) u) := by
            simp only [integral_prod_mul, J, μ]
      _ = 2 * (J h j u * J h (j + 2) u - (J h (j + 1) u) ^ 2) := by ring
  have hquadrant : ∀ᵐ p ∂(μ.prod μ), p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioi.prod measurableSet_Ioi)).2 ?_
    have hμpos : ∀ᵐ x ∂μ, 0 < x := by
      dsimp [μ]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hx.1
    filter_upwards [hμpos] with y hy
    filter_upwards [hμpos] with z hz
    exact ⟨hy, hz⟩
  calc
    ∫ p, truncatedGramIntegrand h j p ∂(μ.prod μ) =
        ∫ p, truncatedGramLinearIntegrand h j p ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [hquadrant] with p hp
      exact (truncatedGramLinearIntegrand_eq h j hp.1 hp.2).symm
    _ = 2 * (J h j u * J h (j + 2) u - (J h (j + 1) u) ^ 2) := hlinInt

/-- Full support makes the factorized Gram square strictly positive in integral. -/
lemma integral_truncatedGramIntegrand_pos
    (h : FullSupportMomentWeight) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    0 < ∫ p, truncatedGramIntegrand h j p
      ∂((volume.restrict (Ioc (0 : ℝ) u)).prod (volume.restrict (Ioc (0 : ℝ) u))) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) u)
  have hInt : Integrable (truncatedGramIntegrand h j) (μ.prod μ) := by
    simpa [μ] using truncatedGramIntegrand_integrable h j hu
  have hquadrant : ∀ᵐ p ∂(μ.prod μ), p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioi.prod measurableSet_Ioi)).2 ?_
    have hμpos : ∀ᵐ x ∂μ, 0 < x := by
      dsimp [μ]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hx.1
    filter_upwards [hμpos] with y hy
    filter_upwards [hμpos] with z hz
    exact ⟨hy, hz⟩
  have hNonneg : 0 ≤ᵐ[μ.prod μ] truncatedGramIntegrand h j := by
    filter_upwards [hquadrant] with p hp
    rw [truncatedGramIntegrand]
    exact mul_nonneg
      (mul_nonneg (momentIntegrand_nonneg h j hp.1) (momentIntegrand_nonneg h j hp.2))
      (sq_nonneg (p.1 - p.2))
  let A : Set ℝ := Function.support (h : ℝ → ℝ) ∩ Ioc (u / 4) (u / 2)
  let B : Set ℝ := Function.support (h : ℝ → ℝ) ∩ Ioc (3 * u / 4) u
  have hAvol : 0 < volume A := by
    dsimp [A]
    exact support_h_measure_pos_Ioc h (by nlinarith [hu]) (by nlinarith [hu])
  have hBvol : 0 < volume B := by
    dsimp [B]
    exact support_h_measure_pos_Ioc h (by nlinarith [hu]) (by nlinarith [hu])
  have hμA : 0 < μ A := by
    dsimp [μ, A]
    rw [Measure.restrict_apply' measurableSet_Ioc]
    have hsub :
        Function.support (h : ℝ → ℝ) ∩ Ioc (u / 4) (u / 2) ⊆ Ioc (0 : ℝ) u := by
      intro x hx
      constructor
      · nlinarith [hx.2.1, hu]
      · nlinarith [hx.2.2, hu]
    rw [inter_eq_left.2 hsub]
    exact hAvol
  have hμB : 0 < μ B := by
    dsimp [μ, B]
    rw [Measure.restrict_apply' measurableSet_Ioc]
    have hsub :
        Function.support (h : ℝ → ℝ) ∩ Ioc (3 * u / 4) u ⊆ Ioc (0 : ℝ) u := by
      intro x hx
      constructor
      · nlinarith [hx.2.1, hu]
      · exact hx.2.2
    rw [inter_eq_left.2 hsub]
    exact hBvol
  have hrectPos : 0 < (μ.prod μ) (A ×ˢ B) := by
    rw [Measure.prod_prod, CanonicallyOrderedAdd.mul_pos]
    exact ⟨hμA, hμB⟩
  have hrectSupport : A ×ˢ B ⊆ Function.support (truncatedGramIntegrand h j) := by
    intro p hp
    rcases hp with ⟨hyA, hzB⟩
    change p.1 ∈ Function.support (h : ℝ → ℝ) ∩ Ioc (u / 4) (u / 2) at hyA
    change p.2 ∈ Function.support (h : ℝ → ℝ) ∩ Ioc (3 * u / 4) u at hzB
    have hy0 : 0 < p.1 := by nlinarith [hyA.2.1, hu]
    have hz0 : 0 < p.2 := by nlinarith [hzB.2.1, hu]
    have hyz : p.1 < p.2 := by nlinarith [hyA.2.2, hzB.2.1, hu]
    have hfy := momentIntegrand_pos_of_mem_support h j hy0 hyA.1
    have hfz := momentIntegrand_pos_of_mem_support h j hz0 hzB.1
    have hsq : 0 < (p.1 - p.2) ^ 2 := by nlinarith
    show truncatedGramIntegrand h j p ≠ 0
    rw [truncatedGramIntegrand]
    exact ne_of_gt (mul_pos (mul_pos hfy hfz) hsq)
  have hSupportPos : 0 < (μ.prod μ) (Function.support (truncatedGramIntegrand h j)) :=
    lt_of_lt_of_le hrectPos (measure_mono hrectSupport)
  have hpos : 0 < ∫ p, truncatedGramIntegrand h j p ∂(μ.prod μ) :=
    (integral_pos_iff_support_of_nonneg_ae hNonneg hInt).2 hSupportPos
  simpa [μ] using hpos

/-- Strict log-convexity of every positive truncated moment sequence. -/
theorem strict_truncated_moment_logConvexity
    (h : FullSupportMomentWeight) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    (J h (j + 1) u) ^ 2 < J h j u * J h (j + 2) u := by
  have hInt := integral_truncatedGramIntegrand h j hu
  have hPos := integral_truncatedGramIntegrand_pos h j hu
  nlinarith

/-- The exact factorized Gram identity for the truncated Hankel minor. -/
theorem truncated_hankel_gram_identity
    (h : FullSupportMomentWeight) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    J h j u * J h (j + 2) u - (J h (j + 1) u) ^ 2 =
      (1 / 2 : ℝ) *
        ∫ p, truncatedGramIntegrand h j p
          ∂((volume.restrict (Ioc (0 : ℝ) u)).prod (volume.restrict (Ioc (0 : ℝ) u))) := by
  have hInt := integral_truncatedGramIntegrand h j hu
  linarith

/-- Algebraic Hankel-ratio form of the truncated variance term. -/
lemma truncatedVar_eq_hankel_ratio
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    truncatedVar h k u =
      (J h (k + 1) u * J h (k + 3) u - (J h (k + 2) u) ^ 2) /
        (J h (k + 1) u) ^ 2 := by
  have hJ : J h (k + 1) u ≠ 0 := ne_of_gt (J_pos h (k + 1) hu)
  rw [truncatedVar, truncatedMu]
  field_simp

/-- The truncated variance term is strictly positive. -/
theorem truncatedVar_pos
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    0 < truncatedVar h k u := by
  have hdet :
      0 < J h (k + 1) u * J h (k + 3) u - (J h (k + 2) u) ^ 2 := by
    have hlog := strict_truncated_moment_logConvexity h (k + 1) hu
    have hk2 : k + 1 + 1 = k + 2 := by omega
    have hk3 : k + 1 + 2 = k + 3 := by omega
    rw [hk2, hk3] at hlog
    exact sub_pos.mpr hlog
  have hJ : 0 < J h (k + 1) u := J_pos h (k + 1) hu
  rw [truncatedVar_eq_hankel_ratio h k hu]
  exact div_pos hdet (sq_pos_of_pos hJ)

/-- Exact Gram-plus-transport decomposition from manuscript Theorem 2.2(v). -/
theorem crossing_kernel_succ_gram_decomposition
    (h : FullSupportMomentWeight) {k : ℕ} (_hk : 1 ≤ k) {u : ℝ} (hu : 0 < u) :
    R h (k + 1) u / (2 * I h (k + 2) * J h (k + 1) u) =
      truncatedVar h k u + crossingQ h (k + 1) (truncatedMu h k u) := by
  have hI : I h (k + 2) ≠ 0 := ne_of_gt (h.momentPositive (k + 2))
  have hJ : J h (k + 1) u ≠ 0 := ne_of_gt (J_pos h (k + 1) hu)
  rw [R, K, K, truncatedVar, truncatedMu, crossingQ, crossingA]
  field_simp
  ring

end CrossBoundaryMomentKernels
