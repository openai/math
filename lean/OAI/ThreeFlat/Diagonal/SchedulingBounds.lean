import OAI.ThreeFlat.Diagonal.DefectBudget
import OAI.ThreeFlat.Diagonal.Scheduling
import OAI.ThreeFlat.Diagonal.GroupCount
import OAI.ThreeFlat.Diagonal.SlotBudget

namespace OAI
/-! # Cell bounds at the scales of the diagonal construction

The distribution lemma bounds the work and the external pairs of a single cell by
`V^(3/5)`. Round its binary logarithm up to an integer. The resulting bound still
fits in both shares used to define the group score and in one team slot.
-/

namespace ThreeFlat.Diagonal

/-- The external register and work shares of one group both dominate the cell
bound. Here `e` is the saving exponent `A − c₁ − c₂` in the total work, and
`k` is the polynomial exponent of the tick template. -/
theorem cell_budget_bounds {w A d e k L : ℕ} (hw : d + e + k + 16 ≤ w)
    (hL : L ≤ w ^ d) :
    let V := 2 ^ (w ^ 10)
    let q := 2 ^ (w ^ 3)
    let T := 2 ^ (w ^ 6)
    let a := 2 ^ (w ^ 10 - w ^ 4)
    let B := 2 * (q * V * L / w ^ (A + 2))
    let W := q * V * T / w ^ e
    let J := 1024 * B / a
    let m := V / w ^ k
    let M := 2 ^ ((3 * w ^ 10 + 4) / 5)
    J * M ≤ B ∧ J * M ≤ W ∧ 16 * M ≤ m := by
  intro V q T a B W J m M
  have wp : 0 < w := by omega
  have h₄ : 16 ≤ w ^ 4 := (by omega : 16 ≤ w).trans (Nat.le_self_pow (by decide) w)
  have h₆ : 16 ≤ w ^ 6 := (by omega : 16 ≤ w).trans (Nat.le_self_pow (by decide) w)
  have h₂₄ : w ^ 2 ≤ w ^ 4 := Nat.pow_le_pow_right wp (by decide)
  have gap : 16 * w ^ 4 ≤ w ^ 10 := by
    calc
      16 * w ^ 4 ≤ w ^ 6 * w ^ 4 := Nat.mul_le_mul_right _ h₆
      _ = w ^ 10 := (Nat.pow_add w 6 4).symm
  have bin : 1024 * M ≤ a := by
    change 2 ^ 10 * 2 ^ ((3 * w ^ 10 + 4) / 5) ≤ 2 ^ (w ^ 10 - w ^ 4)
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have pairs_fit : J * M ≤ B := by
    apply Nat.le_of_mul_le_mul_left (c := 1024) _ (by decide)
    calc
      1024 * (J * M) = J * (1024 * M) := by ac_rfl
      _ ≤ J * a := Nat.mul_le_mul_left J bin
      _ ≤ 1024 * B := Nat.div_mul_le_self _ _
  have polynomial : 2 * (L * w ^ e) ≤ T := by
    have small := Nat.mul_le_mul_right (w ^ e) hL
    rw [← Nat.pow_add] at small
    have width := width_pow_le_two_pow_sq (w := w) (k := d + e) (by omega)
    have hy : 2 * w ^ 2 ≤ w ^ 6 := by
      calc
        2 * w ^ 2 ≤ w ^ 4 * w ^ 2 := Nat.mul_le_mul_right _ (by omega : 2 ≤ w ^ 4)
        _ = w ^ 6 := (Nat.pow_add w 4 2).symm
    calc
      2 * (L * w ^ e) ≤ 2 * 2 ^ (w ^ 2) := Nat.mul_le_mul_left _ (small.trans width)
      _ = 2 ^ (1 + w ^ 2) := (Nat.pow_add 2 1 _).symm
      _ ≤ T := Nat.pow_le_pow_right (by decide) (by
        have : 0 < w ^ 2 := Nat.pow_pos wp
        omega)
  have total : B ≤ W := by
    apply (Nat.le_div_iff_mul_le (Nat.pow_pos wp)).mpr
    calc
      B * w ^ e ≤ (2 * (q * V * L)) * w ^ e := Nat.mul_le_mul_right _ <|
        Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
      _ = (q * V) * (2 * (L * w ^ e)) := by ac_rfl
      _ ≤ q * V * T := Nat.mul_le_mul_left _ polynomial
  refine ⟨pairs_fit, pairs_fit.trans total, ?_⟩
  apply (Nat.le_div_iff_mul_le (Nat.pow_pos wp)).mpr
  calc
    (16 * M) * w ^ k ≤ (2 ^ 4 * M) * 2 ^ (w ^ 2) :=
      Nat.mul_le_mul_left _ (width_pow_le_two_pow_sq (by omega : k ≤ w))
    _ ≤ V := by
      dsimp only [M, V]
      rw [← Nat.pow_add, ← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Bounds for work and pairs imply the required score estimate, with all
denominators cleared as in the executable schedule. -/
theorem cellScore_le_of_cell_budget {α : Type*} {J W B M : ℕ} (work pairs : α → ℕ)
    (c : α) (hw : work c ≤ M) (hp : pairs c ≤ M) (hW : J * M ≤ W) (hB : J * M ≤ B) :
    cellScore J W B work pairs c ≤ 2 * (W * B) := by
  have work_le := Nat.mul_le_mul_left B ((Nat.mul_le_mul_left J hw).trans hW)
  have pairs_le := Nat.mul_le_mul_left W ((Nat.mul_le_mul_left J hp).trans hB)
  calc
    cellScore J W B work pairs c = B * (J * work c) + W * (J * pairs c) := by
      simp only [cellScore, Nat.mul_add]
      ac_rfl
    _ ≤ B * W + W * B := Nat.add_le_add work_le pairs_le
    _ = 2 * (W * B) := by rw [Nat.mul_comm B W, Nat.two_mul]

open LinearAlgebra.SpectralBooks.VNP

/-- The two levels of the greedy schedule cover the cells at the collapse scales.
Each group meets its external-pair bound, and the actual whole-cell handoffs
within that group cover it using its allocated number of team slots. -/
theorem schedule_at_collapse_scales {α : Type*} {w A d e k L : ℕ}
    (large : 512 ≤ w) (hw : d + e + k + 16 ≤ w) (saving : k + 1 ≤ e)
    (hmin : w ^ (A + 2) ≤ L) (hmax : L ≤ w ^ d)
    (work pairs : α → ℕ) (cells : List α) (pos : ∀ c ∈ cells, 0 < work c) :
    let V := 2 ^ (w ^ 10)
    let q := 2 ^ (w ^ 3)
    let T := 2 ^ (w ^ 6)
    let a := 2 ^ (w ^ 10 - w ^ 4)
    let B := 2 * (q * V * L / w ^ (A + 2))
    let W := q * V * T / w ^ e
    let J := 1024 * B / a
    let m := V / w ^ k
    let M := 2 ^ ((3 * w ^ 10 + 4) / 5)
    Team.ticks work cells ≤ W → Team.ticks pairs cells ≤ B →
    (∀ c ∈ cells, work c ≤ M ∧ pairs c ≤ M) →
    let groups := schedule J W B work pairs cells
    groups.length = J ∧ groups.flatten = cells ∧ ∀ g ∈ groups,
      J * Team.ticks pairs g ≤ 4 * B ∧
      (Team.handoff work (m / 4) (q * T / (4 * J)) g).1.flatten = g := by
  intro V q T a B W J m M totalWork totalPairs maxCell groups
  have wp : 0 < w := by omega
  have qp : 0 < q := Nat.two_pow_pos _
  have ap : 0 < a := Nat.two_pow_pos _
  have mp : 0 < M := Nat.two_pow_pos _
  have Ja : a ≤ 1024 * B := by
    have full : q * V ≤ q * V * L / w ^ (A + 2) :=
      (Nat.le_div_iff_mul_le (Nat.pow_pos wp)).mpr (Nat.mul_le_mul_left _ hmin)
    have av : a ≤ V := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    have vq : V ≤ q * V := Nat.le_mul_of_pos_left _ qp
    dsimp only [B]
    omega
  have jp : 0 < J := (Nat.le_div_iff_mul_le ap).mpr (by simpa using Ja)
  obtain ⟨budgetB, budgetW, maxTicks⟩ := cell_budget_bounds (A := A) hw hmax
  change J * M ≤ B at budgetB
  change J * M ≤ W at budgetW
  change 16 * M ≤ m at maxTicks
  obtain ⟨len, flat, caps⟩ := schedule_spec jp ((Nat.mul_pos jp mp).trans_le budgetW)
    ((Nat.mul_pos jp mp).trans_le budgetB) work pairs cells pos totalWork totalPairs
    (fun c hc => cellScore_le_of_cell_budget work pairs c
      (maxCell c hc).1 (maxCell c hc).2 budgetW budgetB)
  refine ⟨len, flat, ?_⟩
  intro g hg
  obtain ⟨workCap, pairsCap⟩ := caps g hg
  have count : 4 * J ≤ T := group_count_fits_transitions (by omega : 3 ≤ w)
    (group_count_budget (by omega : d + 16 ≤ w) hmax)
  have gain : 256 * W ≤ m * (q * T) := by
    have workBudget := diagonal_work_budget large (by omega : k ≤ w) saving
    simpa only [W, m, V, q, T, Nat.mul_right_comm (2 ^ (w ^ 3)) (2 ^ (w ^ 10))] using
      workBudget
  have room := group_slot_budget jp (count.trans (Nat.le_mul_of_pos_left _ qp))
    (by omega : 16 ≤ m) maxTicks workCap gain
  have covered := Team.handoff_covers work (m / 4) M (q * T / (4 * J)) g (fun c hc => by
    have inside := List.mem_flatten.mpr ⟨g, hg, hc⟩
    change c ∈ (schedule J W B work pairs cells).flatten at inside
    rw [flat] at inside
    exact ⟨pos c inside, (maxCell c inside).1.trans (Nat.le_succ _)⟩) room
  exact ⟨pairsCap, by
    simpa only [covered, List.append_nil] using
      Team.handoff_flatten work (m / 4) (q * T / (4 * J)) g⟩

end ThreeFlat.Diagonal

end OAI
