import OAI.Computability.BorderVNP.ParseBatchVerifierKeys
import OAI.Computability.BorderVNP.TeamSorting

/-!
# Near-linear resources of the batched histogram in Lemma 2.3

Once the number of copies dominates a fixed polynomial in the original circuit
size, all labels fit in that many distinct binary keys. The uses, key markers and
sorting padding occupy only linearly many rows. The raw guess bits, rank/count
bits, and weighted parameter occurrences have one logarithmic factor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchVerifier
open VPVNP ParseRecords ParseBatchCounts

/-- Numerical bounds on the actual label and histogram word layouts. -/
structure HistogramBudget (m g r : ℕ) (d : Fin m) : Prop where
  /-- The complete binary-label alphabet fits in the number of copies. -/
  keys : 2 ^ labelWidth m g m ≤ r
  /-- Every raw field fits the common size used for the logarithms. -/
  fieldRange : max m (max g m) + 1 ≤ 2 * m * r
  /-- Each use belongs to one of `r` trees with at most `2m` nodes. -/
  uses : r * (2 * d.val + 1) ≤ 2 * m * r
  /-- All use rows, key markers, and padding fit this many sorting lanes. -/
  lanes : 2 ^ histogramWidth m g r d ≤ 6 * m * r
  /-- The complete raw record has logarithmic width. -/
  labelBits : labelWidth m g m ≤ 6 * Nat.clog 2 (2 * m * r) + 2
  /-- The rank/count and sorting address words have logarithmic width. -/
  histogramBits : histogramWidth m g r d ≤ Nat.clog 2 (2 * m * r) + 2

/-- The absolute replication exponent 24 suffices for every smaller grammar and
all parse degrees below the matrix order. -/
theorem histogramBudget_of_replication {m g s r : ℕ} (d : Fin m)
    (hg : g ≤ 2 * m + s + 1) (hr : (m + s + 2) ^ 24 ≤ r) : HistogramBudget m g r d := by
  let z := m + s + 2
  let x := max m (max g m) + 1
  let a := labelWidth m g m
  let u := r * (2 * d.val + 1)
  have hm : 1 ≤ m := (Nat.zero_le d.val).trans_lt d.isLt
  have hx : 0 < x := Nat.succ_pos _
  have hz : 2 ≤ z := by dsimp [z]; omega
  have hxz : x ≤ 2 * z := by dsimp [x, z]; omega
  have hroot : 2 ^ Nat.clog 2 x ≤ 4 * z := (TeamSorting.padding_lt_twice hx).le.trans (by omega)
  have hkeys : 2 ^ a ≤ r := calc
    2 ^ a = 4 * (2 ^ Nat.clog 2 x) ^ 6 := by
      change 2 ^ (2 + 6 * Nat.clog 2 x) = _
      rw [pow_add, Nat.mul_comm 6 _, pow_mul]
      rfl
    _ ≤ 4 * (4 * z) ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hroot _)
    _ = 4 ^ 7 * z ^ 6 := by ring
    _ ≤ z ^ 18 * z ^ 6 := by
      apply Nat.mul_le_mul_right
      exact (by decide : 4 ^ 7 ≤ 2 ^ 18).trans (Nat.pow_le_pow_left hz 18)
    _ = z ^ 24 := (pow_add z 18 6).symm
    _ ≤ r := hr
  have hzr : z ≤ r := (Nat.le_self_pow (by decide : 24 ≠ 0) z).trans hr
  have hmr : r ≤ m * r := Nat.le_mul_of_pos_left r hm
  have hrange : x ≤ 2 * m * r := hxz.trans (by nlinarith only [hzr, hmr])
  have huses : u ≤ 2 * m * r := by
    have hd := d.isLt
    change r * (2 * d.val + 1) ≤ _
    exact (Nat.mul_le_mul_left r (show 2 * d.val + 1 ≤ 2 * m by omega)).trans_eq (mul_comm ..)
  have hpos : 0 < u + 2 ^ a := Nat.add_pos_right _ (Nat.two_pow_pos a)
  have hpad := (TeamSorting.padding_lt_twice hpos).le
  have hbits : Nat.clog 2 (u + 2 ^ a) ≤ Nat.clog 2 (2 * m * r) + 2 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add 2 (Nat.clog 2 (2 * m * r)) 2]
    have hcap := Nat.le_pow_clog (by decide : 1 < 2) (2 * m * r)
    change u + 2 ^ a ≤ 2 ^ Nat.clog 2 (2 * m * r) * 4
    nlinarith only [huses, hkeys, hmr, hcap]
  refine ⟨hkeys, hrange, huses, ?_, ?_, hbits⟩
  · change 2 ^ Nat.clog 2 (u + 2 ^ a) ≤ _
    exact hpad.trans (by nlinarith only [huses, hkeys, hmr])
  · change 2 + 6 * Nat.clog 2 x ≤ _
    have h := Nat.clog_mono_right 2 hrange
    omega

/-- The actual canonical grammar labels inject into the histogram keys, so the
number of unary-weight wires is bounded by the number of keys times the count width. -/
theorem grammarWeightCount_le {m g r : ℕ} (d : Fin m) :
    Fintype.card (GrammarLabel (Fin m × Bool) (Fin g) m) * Nat.clog 2 (r * (2 * d.val + 1) + 1)
      ≤ 2 ^ labelWidth m g m * histogramWidth m g r d := by
  have h := Fintype.card_le_of_injective (recordKey ∘ packBits :
    GrammarLabel (Fin m × Bool) (Fin g) m → Fin (2 ^ labelWidth m g m))
    ((recordKey_injective m g m).comp packBits_injective)
  rw [Fintype.card_fin] at h
  exact Nat.mul_le_mul h (countWidth_le m g r d)

/-- The histogram circuit, on the padded use/marker array with its actual widths,
costs at most a constant times `m*r` times the cube of the binary logarithm. -/
theorem HistogramBudget.gates {m g r : ℕ} {d : Fin m} (h : HistogramBudget m g r d) :
    (histogramFrame (histogramLayout m g r d)).size ≤
      1152000 * (m * r) * (Nat.clog 2 (2 * m * r) + 1) ^ 3 := by
  apply (histogramFrame_size_per_row _).trans
  have hw : histogramWidth m g r d + 2 ≤ 4 * (Nat.clog 2 (2 * m * r) + 1) := by
    have := h.histogramBits
    omega
  calc
    _ ≤ 3000 * (6 * m * r) * (4 * (Nat.clog 2 (2 * m * r) + 1)) ^ 3 := by gcongr; exact h.lanes
    _ = _ := by ring

/-- Total raw input, parse guess, auxiliary rank/count and unary-weight wire budget.
The first summand is the free query and the others are counted separately. -/
theorem HistogramBudget.wires {m g r : ℕ} {d : Fin m} (h : HistogramBudget m g r d) :
    m * r + r * (2 * d.val + 1) * labelWidth m g m +
      2 * 2 ^ labelWidth m g m * histogramWidth m g r d +
      Fintype.card (GrammarLabel (Fin m × Bool) (Fin g) m) * Nat.clog 2 (r * (2 * d.val + 1) + 1)
      ≤ 20 * (m * r) * (Nat.clog 2 (2 * m * r) + 1) := by
  let l := Nat.clog 2 (2 * m * r)
  have hmr : r ≤ m * r := Nat.le_mul_of_pos_left _ ((Nat.zero_le d.val).trans_lt d.isLt)
  have hk := h.keys.trans hmr
  have hraw := Nat.mul_le_mul h.uses h.labelBits
  have haux := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hk) h.histogramBits
  have hweights := (grammarWeightCount_le (g := g) (r := r) d).trans (Nat.mul_le_mul hk h.histogramBits)
  change _ ≤ 20 * (m * r) * (l + 1)
  change _ ≤ 2 * m * r * (6 * l + 2) at hraw
  change _ ≤ 2 * (m * r) * (l + 2) at haux
  change _ ≤ m * r * (l + 2) at hweights
  nlinarith only [hraw, haux, hweights, Nat.zero_le (m * r * l), Nat.zero_le (m * r)]

end ParseBatchVerifier

end BorderVNP
end Computability
end OAI
