import CrossBoundaryMomentKernels.TotalPositivityAdjacent

noncomputable section

open MeasureTheory Set Filter

namespace CrossBoundaryMomentKernels

/-- Iterating the adjacent ratio theorem: for every `d ≥ 0`, the ratio
`Z_{m+d+1}/Z_m` is strictly increasing on `(0,∞)`. -/
lemma Z_ratio_strict_add
    (h : FullSupportMomentWeight) {m d : ℕ} (hm : 1 ≤ m) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    Z h (m + d + 1) u / Z h m u < Z h (m + d + 1) v / Z h m v := by
  induction d with
  | zero =>
      simpa using adjacent_Z_ratio_strict h hm hu huv
  | succ d ih =>
      let p : ℕ := m + d + 1
      have hp : 1 ≤ p := by dsimp [p]; omega
      have hAdj :
          Z h (p + 1) u / Z h p u < Z h (p + 1) v / Z h p v :=
        adjacent_Z_ratio_strict h hp hu huv
      have hInd : Z h p u / Z h m u < Z h p v / Z h m v := by
        simpa [p, Nat.add_assoc] using ih
      have hZpU : 0 < Z h p u := Z_pos h hp hu
      have hZpV : 0 < Z h p v := Z_pos h hp (lt_trans hu huv)
      have hZmU : 0 < Z h m u := Z_pos h hm hu
      have hZmV : 0 < Z h m v := Z_pos h hm (lt_trans hu huv)
      have hZsuccV : 0 < Z h (p + 1) v := Z_pos h (by omega) (lt_trans hu huv)
      have hIndPosU : 0 < Z h p u / Z h m u := div_pos hZpU hZmU
      have hAdjPosV : 0 < Z h (p + 1) v / Z h p v := div_pos hZsuccV hZpV
      have hmul₁ := mul_lt_mul_of_pos_right hAdj hIndPosU
      have hmul₂ := mul_lt_mul_of_pos_left hInd hAdjPosV
      have hprod :
          (Z h (p + 1) u / Z h p u) * (Z h p u / Z h m u) <
            (Z h (p + 1) v / Z h p v) * (Z h p v / Z h m v) :=
        lt_trans hmul₁ hmul₂
      have hfacU :
          Z h (p + 1) u / Z h m u =
            (Z h (p + 1) u / Z h p u) * (Z h p u / Z h m u) := by
        field_simp [ne_of_gt hZpU, ne_of_gt hZmU]
      have hfacV :
          Z h (p + 1) v / Z h m v =
            (Z h (p + 1) v / Z h p v) * (Z h p v / Z h m v) := by
        field_simp [ne_of_gt hZpV, ne_of_gt hZmV]
      have hstep : Z h (p + 1) u / Z h m u < Z h (p + 1) v / Z h m v := by
        rw [hfacU, hfacV]
        exact hprod
      simpa [p, Nat.succ_eq_add_one, Nat.add_assoc] using hstep

/-- For arbitrary manuscript indices `1 ≤ m < n`, the ratio `Z_n/Z_m` is strictly increasing. -/
theorem Z_ratio_strict_indices
    (h : FullSupportMomentWeight) {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    Z h n u / Z h m u < Z h n v / Z h m v := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = m + d + 1 := by omega
  exact Z_ratio_strict_add h hm hu huv

/-- **Strict total positivity of order two.** This is the determinant form of manuscript
Theorem 2.2(iv), for arbitrary (not only adjacent) indices. -/
theorem strict_total_positivity_order_two
    (h : FullSupportMomentWeight) {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    0 < Z h m u * Z h n v - Z h n u * Z h m v := by
  have hratio := Z_ratio_strict_indices h hm hmn hu huv
  have hmu : 0 < Z h m u := Z_pos h hm hu
  have hmv : 0 < Z h m v := Z_pos h hm (lt_trans hu huv)
  have hcross := (div_lt_div_iff₀ hmu hmv).mp hratio
  nlinarith [hcross]

/-- **Manuscript Theorem 2.2(iv).** Adjacent normalized ratios are strictly increasing and the
whole hierarchy is strictly TP2 for every `1 ≤ m < n`. -/
theorem universal_strict_tp2
    (h : FullSupportMomentWeight) :
    (∀ ⦃k : ℕ⦄, 1 ≤ k → ∀ ⦃u v : ℝ⦄, 0 < u → u < v →
      Z h (k + 1) u / Z h k u < Z h (k + 1) v / Z h k v) ∧
    (∀ ⦃m n : ℕ⦄, 1 ≤ m → m < n → ∀ ⦃u v : ℝ⦄, 0 < u → u < v →
      0 < Z h m u * Z h n v - Z h n u * Z h m v) := by
  constructor
  · intro k hk u v hu huv
    exact adjacent_Z_ratio_strict h hk hu huv
  · intro m n hm hmn u v hu huv
    exact strict_total_positivity_order_two h hm hmn hu huv

end CrossBoundaryMomentKernels
