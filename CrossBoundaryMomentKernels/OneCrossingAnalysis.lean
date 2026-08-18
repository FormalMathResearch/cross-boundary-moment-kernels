import CrossBoundaryMomentKernels.OneCrossing

noncomputable section

open MeasureTheory Set

namespace CrossBoundaryMomentKernels

/-- An integrability-friendly linear normal form for the derivative density of `R_k`. -/
def rLinearIntegrand (h : ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  2 *
    (tau h k * I h (k + 1) * momentIntegrand h k x +
      I h (k + 1) * momentIntegrand h (k + 2) x -
      (tau h k * I h k + I h (k + 2)) * momentIntegrand h (k + 1) x)

/-- On the positive half-line, the linear normal form is exactly the manuscript density
`2 I_{k+1} x^(k-1/2) h(x) Q_k(x)`. -/
lemma rLinearIntegrand_eq_rDerivativeIntegrand
    (h : FullSupportMomentWeight) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    rLinearIntegrand h k x = rDerivativeIntegrand h k x := by
  have hx₁ := momentIntegrand_succ h k hx
  have hx₂ : momentIntegrand h (k + 2) x = x * momentIntegrand h (k + 1) x := by
    convert momentIntegrand_succ h (k + 1) hx using 1
  rw [rLinearIntegrand, rDerivativeIntegrand, crossingQ, crossingA, hx₂, hx₁]
  field_simp [ne_of_gt (h.momentPositive (k + 1))]
  ring

/-- The linear derivative density is integrable on the positive half-line. -/
lemma rLinearIntegrand_integrable
    (h : FullSupportMomentWeight) (k : ℕ) :
    Integrable (rLinearIntegrand h k) (volume.restrict (Ioi (0 : ℝ))) := by
  have hk : Integrable (momentIntegrand h k) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using h.momentIntegrable k
  have hk₁ : Integrable (momentIntegrand h (k + 1)) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using h.momentIntegrable (k + 1)
  have hk₂ : Integrable (momentIntegrand h (k + 2)) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using h.momentIntegrable (k + 2)
  have ht₀ : Integrable
      (fun x ↦ tau h k * I h (k + 1) * momentIntegrand h k x)
      (volume.restrict (Ioi (0 : ℝ))) := by
    exact hk.const_mul _
  have ht₁ : Integrable
      (fun x ↦ I h (k + 1) * momentIntegrand h (k + 2) x)
      (volume.restrict (Ioi (0 : ℝ))) := by
    exact hk₂.const_mul _
  have ht₂ : Integrable
      (fun x ↦ (tau h k * I h k + I h (k + 2)) * momentIntegrand h (k + 1) x)
      (volume.restrict (Ioi (0 : ℝ))) := by
    exact hk₁.const_mul _
  have hcore : Integrable
      (fun x ↦
        tau h k * I h (k + 1) * momentIntegrand h k x +
          I h (k + 1) * momentIntegrand h (k + 2) x -
          (tau h k * I h k + I h (k + 2)) * momentIntegrand h (k + 1) x)
      (volume.restrict (Ioi (0 : ℝ))) := by
    exact (ht₀.add ht₁).sub ht₂
  change Integrable
    (fun x ↦
      2 *
        (tau h k * I h (k + 1) * momentIntegrand h k x +
          I h (k + 1) * momentIntegrand h (k + 2) x -
          (tau h k * I h k + I h (k + 2)) * momentIntegrand h (k + 1) x))
    (volume.restrict (Ioi (0 : ℝ)))
  exact hcore.const_mul (2 : ℝ)

/-- The manuscript derivative density is integrable on the positive half-line. -/
lemma rDerivativeIntegrand_integrable
    (h : FullSupportMomentWeight) (k : ℕ) :
    Integrable (rDerivativeIntegrand h k) (volume.restrict (Ioi (0 : ℝ))) := by
  apply (rLinearIntegrand_integrable h k).congr
  have hpos : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), 0 < x :=
    ae_restrict_mem measurableSet_Ioi
  filter_upwards [hpos] with x hx
  exact rLinearIntegrand_eq_rDerivativeIntegrand h k hx

end CrossBoundaryMomentKernels
