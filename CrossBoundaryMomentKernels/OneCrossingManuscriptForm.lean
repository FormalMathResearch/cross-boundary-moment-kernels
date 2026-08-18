import CrossBoundaryMomentKernels.OneCrossingGeometry

noncomputable section

open MeasureTheory Set

namespace CrossBoundaryMomentKernels

/-- Manuscript-exact a.e. derivative formula from Theorem 2.2(ii). -/
theorem R_ae_hasDerivAt_manuscript
    (h : FullSupportMomentWeight) (k : ℕ) :
    ∀ᵐ x, 0 < x →
      HasDerivAt (R h k)
        (2 * I h (k + 1) * (Real.rpow x (halfExponent k) * h x) * crossingQ h k x) x := by
  filter_upwards [R_ae_hasDerivAt h k] with x hx
  intro hxpos
  simpa [rDerivativeIntegrand, momentIntegrand] using hx hxpos

end CrossBoundaryMomentKernels
