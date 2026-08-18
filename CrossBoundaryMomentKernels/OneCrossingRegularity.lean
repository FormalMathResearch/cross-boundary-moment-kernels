import CrossBoundaryMomentKernels.OneCrossingSigns
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace CrossBoundaryMomentKernels

/-- Extend the manuscript derivative density by zero off the positive half-line. -/
def positiveRDerivative (h : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator (rDerivativeIntegrand h k)

/-- The zero-extended derivative density is globally integrable. -/
lemma positiveRDerivative_integrable
    (h : FullSupportMomentWeight) (k : ℕ) :
    Integrable (positiveRDerivative h k) volume := by
  have hdOn : IntegrableOn (rDerivativeIntegrand h k) (Ioi (0 : ℝ)) := by
    simpa [IntegrableOn] using rDerivativeIntegrand_integrable h k
  exact hdOn.integrable_indicator measurableSet_Ioi

/-- On `x > 0` the zero extension agrees with the manuscript derivative density. -/
lemma positiveRDerivative_eq
    (h : ℝ → ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    positiveRDerivative h k x = rDerivativeIntegrand h k x := by
  simp [positiveRDerivative, hx]

/-- Interval-integral version of the primitive identity. -/
lemma R_eq_intervalIntegral_positiveRDerivative
    (h : FullSupportMomentWeight) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    R h k u = ∫ x in (0 : ℝ)..u, positiveRDerivative h k x := by
  rw [intervalIntegral.integral_of_le hu.le]
  calc
    R h k u =
        ∫ x, rDerivativeIntegrand h k x ∂(volume.restrict (Ioc (0 : ℝ) u)) :=
      R_eq_setIntegral_rDerivativeIntegrand h k hu
    _ = ∫ x, positiveRDerivative h k x ∂(volume.restrict (Ioc (0 : ℝ) u)) := by
      apply integral_congr_ae
      have hmem : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) u)), x ∈ Ioc (0 : ℝ) u :=
        ae_restrict_mem measurableSet_Ioc
      filter_upwards [hmem] with x hx
      exact (positiveRDerivative_eq h k hx.1).symm

/-- Absolute continuity is invariant under changing a function pointwise on the underlying interval. -/
lemma absolutelyContinuousOnInterval_congr_eqOn
    {f g : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hfg : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  rcases hf ε hε with ⟨δ, hδ, hmain⟩
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlen
  have hlt := hmain E hE hlen
  calc
    ∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2) =
        ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi_mem := hE.1 i hi
      rw [hfg hi_mem.1, hfg hi_mem.2]
    _ < ε := hlt

/-- **Local absolute continuity from Theorem 2.2(ii).** No regularity of `h` beyond the manuscript
hypotheses is used. -/
theorem R_absolutelyContinuousOnInterval
    (h : FullSupportMomentWeight) (k : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (R h k) a b := by
  have hb : 0 ≤ b := le_trans ha.le hab
  have hdInt : IntervalIntegrable (positiveRDerivative h k) volume (0 : ℝ) b :=
    (positiveRDerivative_integrable h k).intervalIntegrable
  have hprim :
      AbsolutelyContinuousOnInterval
        (fun x ↦ ∫ t in (0 : ℝ)..x, positiveRDerivative h k t) (0 : ℝ) b :=
    hdInt.absolutelyContinuousOnInterval_intervalIntegral (left_mem_Icc.2 hb)
  have hsubset : uIcc a b ⊆ uIcc (0 : ℝ) b := by
    rw [uIcc_of_le hab, uIcc_of_le hb]
    intro x hx
    exact ⟨le_trans ha.le hx.1, hx.2⟩
  have hprim_ab :
      AbsolutelyContinuousOnInterval
        (fun x ↦ ∫ t in (0 : ℝ)..x, positiveRDerivative h k t) a b :=
    hprim.mono hsubset
  apply absolutelyContinuousOnInterval_congr_eqOn hprim_ab
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact (R_eq_intervalIntegral_positiveRDerivative h k (lt_of_lt_of_le ha hx.1)).symm

/-- **A.e. derivative law from Theorem 2.2(ii).** On the positive half-line,
`R_k'(x) = 2 I_{k+1} x^(k-1/2) h(x) Q_k(x)` almost everywhere. -/
theorem R_ae_hasDerivAt
    (h : FullSupportMomentWeight) (k : ℕ) :
    ∀ᵐ x, 0 < x → HasDerivAt (R h k) (rDerivativeIntegrand h k x) x := by
  have hloc : LocallyIntegrable (positiveRDerivative h k) volume :=
    (positiveRDerivative_integrable h k).locallyIntegrable
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hloc] with x hx
  intro hxpos
  have hprim :
      HasDerivAt (fun y ↦ ∫ t in (0 : ℝ)..y, positiveRDerivative h k t)
        (positiveRDerivative h k x) x :=
    hx 0
  have heq :
      (R h k) =ᶠ[𝓝 x] (fun y ↦ ∫ t in (0 : ℝ)..y, positiveRDerivative h k t) := by
    filter_upwards [Ioi_mem_nhds hxpos] with y hy
    exact R_eq_intervalIntegral_positiveRDerivative h k hy
  have hR := hprim.congr_of_eventuallyEq heq
  rw [positiveRDerivative_eq h k hxpos] at hR
  exact hR

end CrossBoundaryMomentKernels
