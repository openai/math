import OAI.LinearAlgebra.SpectralBooks.VNP.TeamBlockHandoff

namespace OAI
/-! # Packing the cells in the rank diagonal

A cell has a work bound and a number of external pairs. The greedy scheduling
score of each cell is the sum of its fractions of the two budgets. Multiplying
all scores and the stopping threshold by the same positive integer lets the
teams compute their common schedule using integer operations.
-/

namespace ThreeFlat.Diagonal

open LinearAlgebra.SpectralBooks.VNP

variable {α : Type*}

/-- Scale the paper's score by `groups * workBudget * pairBudget`. -/
def cellScore (groups workBudget pairBudget : ℕ) (work pairs : α → ℕ) (cell : α) : ℕ :=
  groups * (pairBudget * work cell + workBudget * pairs cell)

private theorem score_sum (J W B : ℕ) (work pairs : α → ℕ) (cells : List α) :
    Team.ticks (cellScore J W B work pairs) cells =
      J * (B * Team.ticks work cells + W * Team.ticks pairs cells) := by
  induction cells with
  | nil => simp
  | cons c cs ih =>
    simp only [Team.ticks_cons, ih, cellScore]
    simp only [Nat.mul_add]
    ac_rfl

private theorem group_cost_le {cost : α → ℕ} {capacity : ℕ} {groups : List (List α)}
    {cells rest : List α} (valid : Team.ValidHandoff cost capacity cells groups rest) :
    ∀ group ∈ groups, Team.ticks cost group ≤ capacity := by
  induction groups generalizing cells with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨next, _, h, hs⟩ := valid
    intro group hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact h.1
    · exact ih hs group hg

/-- The actual contiguous groups, padded with empty groups at the end. -/
def schedule (J W B : ℕ) (work pairs : α → ℕ) (cells : List α) : List (List α) :=
  (Team.handoff (cellScore J W B work pairs) (4 * (W * B)) J cells).1

/-- Every cell is assigned once and in order. Each group receives at most
`4 W / J` work and `4 B / J` pairs. The small-cell hypothesis is that a
single cell has score at most `2 / J`, with denominators cleared. -/
theorem schedule_spec {J W B : ℕ} (hJ : 0 < J) (hW : 0 < W) (hB : 0 < B)
    (work pairs : α → ℕ) (cells : List α)
    (work_pos : ∀ c ∈ cells, 0 < work c)
    (work_total : Team.ticks work cells ≤ W) (pair_total : Team.ticks pairs cells ≤ B)
    (small : ∀ c ∈ cells, cellScore J W B work pairs c ≤ 2 * (W * B)) :
    (schedule J W B work pairs cells).length = J ∧
      (schedule J W B work pairs cells).flatten = cells ∧
      ∀ g ∈ schedule J W B work pairs cells,
        J * Team.ticks work g ≤ 4 * W ∧ J * Team.ticks pairs g ≤ 4 * B := by
  let score := cellScore J W B work pairs
  have positive (c : α) (hc : c ∈ cells) : 0 < score c := by
    have hw := work_pos c hc
    dsimp [score, cellScore]
    exact Nat.mul_pos hJ (Nat.lt_of_lt_of_le (Nat.mul_pos hB hw) (Nat.le_add_right _ _))
  have budget : Team.ticks score cells ≤ J * (4 * (W * B) - 2 * (W * B)) := by
    dsimp only [score]
    rw [score_sum]
    apply Nat.mul_le_mul_left
    have hw := Nat.mul_le_mul_left B work_total
    have hb := Nat.mul_le_mul_left W pair_total
    rw [Nat.mul_comm B W] at hw
    omega
  have covered := Team.handoff_covers score (4 * (W * B)) (2 * (W * B)) J cells
    (fun c hc => ⟨positive c hc, Nat.le_trans (small c hc) (Nat.le_succ _)⟩) budget
  have flat := Team.handoff_flatten score (4 * (W * B)) J cells
  rw [covered, List.append_nil] at flat
  refine ⟨Team.handoff_length .., flat, ?_⟩
  intro group hgroup
  have bound := group_cost_le (Team.handoff_valid score (4 * (W * B)) J cells) group hgroup
  change Team.ticks (cellScore J W B work pairs) group ≤ _ at bound
  rw [score_sum, Nat.mul_add] at bound
  constructor
  · apply Nat.le_of_mul_le_mul_left (c := B) _ hB
    calc
      B * (J * Team.ticks work group) = J * (B * Team.ticks work group) := by ac_rfl
      _ ≤ 4 * (W * B) := Nat.le_trans (Nat.le_add_right _ _) bound
      _ = B * (4 * W) := by ac_rfl
  · apply Nat.le_of_mul_le_mul_left (c := W) _ hW
    calc
      W * (J * Team.ticks pairs group) = J * (W * Team.ticks pairs group) := by ac_rfl
      _ ≤ 4 * (W * B) := Nat.le_trans (Nat.le_add_left _ _) bound
      _ = W * (4 * B) := by ac_rfl

end ThreeFlat.Diagonal

end OAI
