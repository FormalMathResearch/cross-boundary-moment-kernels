import CrossBoundaryMomentKernels.Basic

noncomputable section

open MeasureTheory Set

namespace CrossBoundaryMomentKernels

/-- The consecutive-moment ratio `γ_k = I_{k+1} / I_k` from the manuscript. -/
def gamma (h : ℝ → ℝ) (k : ℕ) : ℝ :=
  I h (k + 1) / I h k

/-- Advancing the moment index raises the half-integer exponent by one. -/
lemma halfExponent_succ (j : ℕ) :
    halfExponent (j + 1) = halfExponent j + 1 := by
  simp [halfExponent]
  ring

/-- On the positive half-line, the `(j+1)`-st moment integrand is obtained by
multiplying the `j`-th moment integrand by the integration variable. -/
lemma momentIntegrand_succ (h : ℝ → ℝ) (j : ℕ) {y : ℝ} (hy : 0 < y) :
    momentIntegrand h (j + 1) y = y * momentIntegrand h j y := by
  rw [momentIntegrand, momentIntegrand, halfExponent_succ]
  change (y ^ (halfExponent j + 1)) * h y = y * (y ^ halfExponent j * h y)
  rw [Real.rpow_add hy (halfExponent j) 1, Real.rpow_one]
  ring

/-- The moment integrand is nonnegative on the positive half-line. -/
lemma momentIntegrand_nonneg (h : FullSupportMomentWeight) (j : ℕ) {y : ℝ} (hy : 0 < y) :
    0 ≤ momentIntegrand h j y := by
  exact mul_nonneg (Real.rpow_nonneg hy.le _) (h.nonneg hy)

/-- On the support of the weight, the moment integrand is strictly positive. -/
lemma momentIntegrand_pos_of_mem_support (h : FullSupportMomentWeight) (j : ℕ) {y : ℝ}
    (hy : 0 < y) (hy_support : y ∈ Function.support (h : ℝ → ℝ)) :
    0 < momentIntegrand h j y := by
  have hh_pos : 0 < h y := lt_of_le_of_ne (h.nonneg hy) (Ne.symm hy_support)
  exact mul_pos (Real.rpow_pos_of_pos hy _) hh_pos

/-- Every consecutive-moment ratio is strictly positive for a full-support moment weight. -/
lemma gamma_pos (h : FullSupportMomentWeight) (k : ℕ) :
    0 < gamma h k := by
  exact div_pos (h.momentPositive (k + 1)) (h.momentPositive k)

/-- **Strict moment log-convexity (manuscript Lemma 3.1).**

For every full-support moment weight and every `k ≥ 0`, the consecutive Hankel minor is
strictly positive. The same end-to-end proof also derives the strict increase of the
consecutive-moment ratio `γ_k = I_{k+1}/I_k`.

The proof keeps the manuscript's symmetrization visible: a product-space integrand is shown
pointwise to equal `f_k(y) f_k(z) (y-z)^2`. Strictness is then forced by full support on the
disjoint intervals `(1,2]` and `(3,4]`.
-/
theorem strict_moment_logConvexity_and_gamma_lt
    (h : FullSupportMomentWeight) (k : ℕ) :
    (I h (k + 1)) ^ 2 < I h k * I h (k + 2) ∧
      gamma h k < gamma h (k + 1) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let G : ℝ × ℝ → ℝ := fun p ↦
    momentIntegrand h k p.1 * momentIntegrand h (k + 2) p.2 +
      momentIntegrand h (k + 2) p.1 * momentIntegrand h k p.2 -
        (momentIntegrand h (k + 1) p.1 * momentIntegrand h (k + 1) p.2 +
          momentIntegrand h (k + 1) p.1 * momentIntegrand h (k + 1) p.2)

  have hIk_int : Integrable (momentIntegrand h k) μ := by
    simpa [μ, IntegrableOn] using h.momentIntegrable k
  have hIk1_int : Integrable (momentIntegrand h (k + 1)) μ := by
    simpa [μ, IntegrableOn] using h.momentIntegrable (k + 1)
  have hIk2_int : Integrable (momentIntegrand h (k + 2)) μ := by
    simpa [μ, IntegrableOn] using h.momentIntegrable (k + 2)

  have hterm₁ : Integrable
      (fun p : ℝ × ℝ ↦ momentIntegrand h k p.1 * momentIntegrand h (k + 2) p.2)
      (μ.prod μ) :=
    hIk_int.mul_prod hIk2_int
  have hterm₂ : Integrable
      (fun p : ℝ × ℝ ↦ momentIntegrand h (k + 2) p.1 * momentIntegrand h k p.2)
      (μ.prod μ) :=
    hIk2_int.mul_prod hIk_int
  have hterm₃ : Integrable
      (fun p : ℝ × ℝ ↦ momentIntegrand h (k + 1) p.1 * momentIntegrand h (k + 1) p.2)
      (μ.prod μ) :=
    hIk1_int.mul_prod hIk1_int

  have hG_integrable : Integrable G (μ.prod μ) := by
    dsimp [G]
    exact (hterm₁.add hterm₂).sub (hterm₃.add hterm₃)

  have hG_integral :
      (∫ p, G p ∂(μ.prod μ)) =
        2 * (I h k * I h (k + 2) - (I h (k + 1)) ^ 2) := by
    calc
      (∫ p, G p ∂(μ.prod μ)) =
          ∫ p,
            ((fun q : ℝ × ℝ ↦
                momentIntegrand h k q.1 * momentIntegrand h (k + 2) q.2) +
              (fun q : ℝ × ℝ ↦
                momentIntegrand h (k + 2) q.1 * momentIntegrand h k q.2) -
              ((fun q : ℝ × ℝ ↦
                  momentIntegrand h (k + 1) q.1 * momentIntegrand h (k + 1) q.2) +
                (fun q : ℝ × ℝ ↦
                  momentIntegrand h (k + 1) q.1 * momentIntegrand h (k + 1) q.2))) p
              ∂(μ.prod μ) := by rfl
      _ =
          (∫ p, momentIntegrand h k p.1 * momentIntegrand h (k + 2) p.2 ∂(μ.prod μ)) +
            (∫ p, momentIntegrand h (k + 2) p.1 * momentIntegrand h k p.2 ∂(μ.prod μ)) -
              ((∫ p, momentIntegrand h (k + 1) p.1 * momentIntegrand h (k + 1) p.2
                  ∂(μ.prod μ)) +
                (∫ p, momentIntegrand h (k + 1) p.1 * momentIntegrand h (k + 1) p.2
                  ∂(μ.prod μ))) := by
            rw [integral_sub (hterm₁.add hterm₂) (hterm₃.add hterm₃),
              integral_add hterm₁ hterm₂, integral_add hterm₃ hterm₃]
      _ =
          I h k * I h (k + 2) + I h (k + 2) * I h k -
            (I h (k + 1) * I h (k + 1) + I h (k + 1) * I h (k + 1)) := by
            rw [integral_prod_mul, integral_prod_mul, integral_prod_mul, integral_prod_mul]
            rfl
      _ = 2 * (I h k * I h (k + 2) - (I h (k + 1)) ^ 2) := by ring

  have hG_square (y z : ℝ) (hy : 0 < y) (hz : 0 < z) :
      G (y, z) = momentIntegrand h k y * momentIntegrand h k z * (y - z) ^ 2 := by
    have hy₁ : momentIntegrand h (k + 1) y = y * momentIntegrand h k y :=
      momentIntegrand_succ h k hy
    have hz₁ : momentIntegrand h (k + 1) z = z * momentIntegrand h k z :=
      momentIntegrand_succ h k hz
    have hy₂ : momentIntegrand h (k + 2) y = y * momentIntegrand h (k + 1) y := by
      convert momentIntegrand_succ h (k + 1) hy using 1 <;> omega
    have hz₂ : momentIntegrand h (k + 2) z = z * momentIntegrand h (k + 1) z := by
      convert momentIntegrand_succ h (k + 1) hz using 1 <;> omega
    dsimp [G]
    rw [hy₂, hz₂, hy₁, hz₁]
    ring

  have hμ_ae_pos : ∀ᵐ y ∂μ, 0 < y := by
    dsimp [μ]
    exact ae_restrict_mem measurableSet_Ioi

  have hquadrant_ae : ∀ᵐ p ∂(μ.prod μ), p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioi.prod measurableSet_Ioi)).2 ?_
    filter_upwards [hμ_ae_pos] with y hy
    filter_upwards [hμ_ae_pos] with z hz
    exact ⟨hy, hz⟩

  have hG_nonneg : 0 ≤ᵐ[μ.prod μ] G := by
    filter_upwards [hquadrant_ae] with p hp
    rw [hG_square p.1 p.2 hp.1 hp.2]
    exact mul_nonneg
      (mul_nonneg (momentIntegrand_nonneg h k hp.1) (momentIntegrand_nonneg h k hp.2))
      (sq_nonneg (p.1 - p.2))

  have hfull_A :
      0 < ∫ y, h y ∂(volume.restrict (Ioc (1 : ℝ) 2)) :=
    h.fullSupport (by norm_num) (by norm_num)
  have hfull_B :
      0 < ∫ y, h y ∂(volume.restrict (Ioc (3 : ℝ) 4)) :=
    h.fullSupport (by norm_num) (by norm_num)

  have hh_int_A : IntegrableOn (h : ℝ → ℝ) (Ioc (1 : ℝ) 2) := by
    by_contra hnot
    have hzero : ∫ y, h y ∂(volume.restrict (Ioc (1 : ℝ) 2)) = 0 :=
      integral_undef hnot
    linarith
  have hh_int_B : IntegrableOn (h : ℝ → ℝ) (Ioc (3 : ℝ) 4) := by
    by_contra hnot
    have hzero : ∫ y, h y ∂(volume.restrict (Ioc (3 : ℝ) 4)) = 0 :=
      integral_undef hnot
    linarith

  have hh_nonneg_A : 0 ≤ᵐ[volume.restrict (Ioc (1 : ℝ) 2)] (h : ℝ → ℝ) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with y hy
    exact h.nonneg (by linarith [hy.1])
  have hh_nonneg_B : 0 ≤ᵐ[volume.restrict (Ioc (3 : ℝ) 4)] (h : ℝ → ℝ) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards with y hy
    exact h.nonneg (by linarith [hy.1])

  have hsupp_A_vol :
      0 < volume (Function.support (h : ℝ → ℝ) ∩ Ioc (1 : ℝ) 2) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hh_nonneg_A hh_int_A).mp hfull_A
  have hsupp_B_vol :
      0 < volume (Function.support (h : ℝ → ℝ) ∩ Ioc (3 : ℝ) 4) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hh_nonneg_B hh_int_B).mp hfull_B

  let A : Set ℝ := Function.support (h : ℝ → ℝ) ∩ Ioc (1 : ℝ) 2
  let B : Set ℝ := Function.support (h : ℝ → ℝ) ∩ Ioc (3 : ℝ) 4

  have hμA : 0 < μ A := by
    dsimp [μ, A]
    rw [Measure.restrict_apply' measurableSet_Ioi]
    have hsub : Function.support (h : ℝ → ℝ) ∩ Ioc (1 : ℝ) 2 ⊆ Ioi (0 : ℝ) := by
      intro y hy
      exact show 0 < y by linarith [hy.2.1]
    rw [inter_eq_left.2 hsub]
    exact hsupp_A_vol
  have hμB : 0 < μ B := by
    dsimp [μ, B]
    rw [Measure.restrict_apply' measurableSet_Ioi]
    have hsub : Function.support (h : ℝ → ℝ) ∩ Ioc (3 : ℝ) 4 ⊆ Ioi (0 : ℝ) := by
      intro y hy
      exact show 0 < y by linarith [hy.2.1]
    rw [inter_eq_left.2 hsub]
    exact hsupp_B_vol

  have hrect_pos : 0 < (μ.prod μ) (A ×ˢ B) := by
    rw [Measure.prod_prod, CanonicallyOrderedAdd.mul_pos]
    exact ⟨hμA, hμB⟩

  have hrect_support : A ×ˢ B ⊆ Function.support G := by
    intro p hp
    rcases hp with ⟨hyA, hzB⟩
    change p.1 ∈ Function.support (h : ℝ → ℝ) ∩ Ioc (1 : ℝ) 2 at hyA
    change p.2 ∈ Function.support (h : ℝ → ℝ) ∩ Ioc (3 : ℝ) 4 at hzB
    have hy_pos : 0 < p.1 := by linarith [hyA.2.1]
    have hz_pos : 0 < p.2 := by linarith [hzB.2.1]
    have hyz : p.1 < p.2 := by linarith [hyA.2.2, hzB.2.1]
    have hfy_pos := momentIntegrand_pos_of_mem_support h k hy_pos hyA.1
    have hfz_pos := momentIntegrand_pos_of_mem_support h k hz_pos hzB.1
    have hsq_pos : 0 < (p.1 - p.2) ^ 2 := by nlinarith
    have hprod_pos :
        0 < momentIntegrand h k p.1 * momentIntegrand h k p.2 * (p.1 - p.2) ^ 2 :=
      mul_pos (mul_pos hfy_pos hfz_pos) hsq_pos
    show G p ≠ 0
    rw [show p = (p.1, p.2) by cases p <;> rfl, hG_square p.1 p.2 hy_pos hz_pos]
    exact ne_of_gt hprod_pos

  have hG_support_pos : 0 < (μ.prod μ) (Function.support G) :=
    lt_of_lt_of_le hrect_pos (measure_mono hrect_support)

  have hG_pos : 0 < ∫ p, G p ∂(μ.prod μ) :=
    (integral_pos_iff_support_of_nonneg_ae hG_nonneg hG_integrable).2 hG_support_pos

  have hlogconv : (I h (k + 1)) ^ 2 < I h k * I h (k + 2) := by
    rw [hG_integral] at hG_pos
    nlinarith

  have hratio : gamma h k < gamma h (k + 1) := by
    rw [gamma, gamma, div_lt_div_iff₀ (h.momentPositive k) (h.momentPositive (k + 1))]
    have hk2 : k + 1 + 1 = k + 2 := by omega
    rw [hk2]
    nlinarith [hlogconv]

  exact ⟨hlogconv, hratio⟩

end CrossBoundaryMomentKernels
