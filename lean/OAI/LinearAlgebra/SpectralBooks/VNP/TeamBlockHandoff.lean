import Mathlib.Data.List.TakeDrop
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

namespace OAI
/-! # Greedy instruction handoff between team processors

An instruction or local-subroutine call is indivisible. Each processor executes
the maximal prefix fitting in its block and passes the first unexecuted
instruction and its state to its successor. Empty blocks propagate a halt.
-/

namespace LinearAlgebra.SpectralBooks.VNP.Team

variable {α : Type*}

/-- Total logical ticks charged to a list of instructions. -/
def ticks (cost : α → ℕ) (xs : List α) : ℕ := (xs.map cost).sum

@[simp] theorem ticks_nil (cost : α → ℕ) : ticks cost [] = 0 := rfl
@[simp] theorem ticks_cons (cost : α → ℕ) (a : α) (xs : List α) :
    ticks cost (a::xs) = cost a + ticks cost xs := rfl

@[simp] theorem ticks_append (cost : α → ℕ) (xs ys : List α) :
    ticks cost (xs ++ ys) = ticks cost xs + ticks cost ys := by simp [ticks]

/-- Split before the first instruction that exceeds the current tick budget. -/
def splitBlock (cost : α → ℕ) : ℕ → List α → List α × List α
  | _, [] => ([], [])
  | H, a::xs =>
    if cost a ≤ H then
      let b := splitBlock cost (H - cost a) xs
      (a :: b.1, b.2)
    else ([], a::xs)

/-- A maximal block uses at most `H` ticks. When a continuation exists,
adding its first instruction would exceed the budget. -/
def MaximalBlock (cost : α → ℕ) (H : ℕ) (block rest : List α) : Prop :=
  ticks cost block ≤ H ∧ ∀ a ys, rest = a::ys → H < ticks cost block + cost a

private theorem split_spec (cost : α → ℕ) (H : ℕ) (xs : List α) :
    let b := splitBlock cost H xs
    b.1 ++ b.2 = xs ∧ MaximalBlock cost H b.1 b.2 := by
  induction xs generalizing H with
  | nil => simp [splitBlock, MaximalBlock]
  | cons a xs ih =>
    by_cases ha : cost a ≤ H
    · obtain ⟨hap, hle, hmax⟩ := ih (H - cost a)
      simp only [splitBlock, ite_eq_left ha, List.cons_append, List.cons.injEq, true_and, ticks_cons,
        MaximalBlock] at *
      refine ⟨hap, by omega, fun c cs h => ?_⟩
      have := hmax c cs h
      omega
    · simp [splitBlock, ha, MaximalBlock]; omega

/-- Local maximality determines the exact split, even when the same instruction
occurs more than once. -/
theorem splitBlock_eq_of_maximal (cost : α → ℕ) (H : ℕ) (block rest : List α)
    (hm : MaximalBlock cost H block rest) : splitBlock cost H (block ++ rest) = (block, rest) := by
  induction block generalizing H with
  | nil =>
    cases rest with
    | nil => rfl
    | cons a xs =>
      have h := hm.2 a xs rfl
      simp [splitBlock, show ¬ cost a ≤ H by simpa using h]
  | cons a bs ih =>
    have ha : cost a ≤ H := (Nat.le_add_right _ _).trans hm.1
    have ht : MaximalBlock cost (H - cost a) bs rest := by
      constructor
      · have := hm.1; simp only [ticks_cons] at this; omega
      · intro c cs h
        have := hm.2 c cs h
        simp only [ticks_cons] at this
        omega
    simp [splitBlock, ha, ih _ ht]

/-- Allocate `r` processors, retaining the unexecuted suffix if the slots run out. -/
def handoff (cost : α → ℕ) (H : ℕ) : ℕ → List α → List (List α) × List α
  | 0, xs => ([], xs)
  | r+1, xs =>
    let here := splitBlock cost H xs
    let later := handoff cost H r here.2
    (here.1 :: later.1, later.2)

@[simp] theorem handoff_length (cost : α → ℕ) (H r : ℕ) (xs : List α) :
    (handoff cost H r xs).1.length = r := by
  induction r generalizing xs <;> simp [handoff, *]

theorem handoff_flatten (cost : α → ℕ) (H r : ℕ) (xs : List α) :
    (handoff cost H r xs).1.flatten ++ (handoff cost H r xs).2 = xs := by
  induction r generalizing xs with
  | zero => rfl
  | succ r ih =>
    simp only [handoff, List.flatten_cons, List.append_assoc, ih]
    exact (split_spec cost H xs).1

/-- All local handoff tests, including propagation of the empty execution after halt. -/
def ValidHandoff (cost : α → ℕ) (H : ℕ) : List α → List (List α) → List α → Prop
  | xs, [], rest => rest = xs
  | xs, b::bs, rest => ∃ next, b ++ next = xs ∧ MaximalBlock cost H b next ∧
    ValidHandoff cost H next bs rest

theorem handoff_valid (cost : α → ℕ) (H r : ℕ) (xs : List α) :
    ValidHandoff cost H xs (handoff cost H r xs).1 (handoff cost H r xs).2 := by
  induction r generalizing xs with
  | zero => rfl
  | succ r ih => exact ⟨_, (split_spec cost H xs).1, (split_spec cost H xs).2, ih _⟩

theorem handoff_eq_of_valid (cost : α → ℕ) (H : ℕ) (xs : List α) (bs : List (List α))
    (rest : List α) (h : ValidHandoff cost H xs bs rest) :
    handoff cost H bs.length xs = (bs, rest) := by
  induction bs generalizing xs with
  | nil => exact Prod.ext rfl h.symm
  | cons b bs ih =>
    obtain ⟨next, rfl, hmax, hvalid⟩ := h
    simp [handoff, splitBlock_eq_of_maximal cost H b next hmax, ih next hvalid]

/-- Every execution of cost at most `r (H-Q)` fits, provided individual
instructions take between one and `Q+1` ticks, inclusive. -/
theorem handoff_covers (cost : α → ℕ) (H Q r : ℕ) (xs : List α)
    (hc : ∀ a ∈ xs, 0 < cost a ∧ cost a ≤ Q+1)
    (hbudget : ticks cost xs ≤ r*(H-Q)) : (handoff cost H r xs).2 = [] := by
  induction r generalizing xs with
  | zero =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      have := (hc a List.mem_cons_self).1
      simp at hbudget
      omega
  | succ r ih =>
    generalize heq : splitBlock cost H xs = pair at *
    rcases pair with ⟨block, rest⟩
    have hs := split_spec cost H xs
    simp only [heq] at hs
    have hc' (a) (ha : a ∈ rest) := hc a (hs.1 ▸ List.mem_append_right _ ha)
    simp only [handoff, heq]
    apply ih _ hc'
    cases rest with
    | nil => simp
    | cons a ys =>
      have hm := hs.2.2 a ys rfl
      have hmax := (hc' a List.mem_cons_self).2
      rw [← hs.1, ticks_append, Nat.succ_mul] at hbudget
      omega

/-- The logical state after consecutive blocks is the state after their concatenation.
The state can include registers, program counter, tick counter, and accumulated weight. -/
theorem fold_blocks {S : Type*} (step : S → α → S) (state : S) (bs : List (List α)) :
    bs.foldl (fun s b => b.foldl step s) state = bs.flatten.foldl step state := by
  induction bs generalizing state with
  | nil => rfl
  | cons b bs ih => simp [List.foldl_append, ih]

/-- Processor `j` owns the consecutive instruction slice immediately after all
earlier slots, including when the trace halted before reaching this processor. -/
theorem handoff_slot (cost : α → ℕ) (H r : ℕ) (xs : List α) (j : Fin r) :
    let bs := (handoff cost H r xs).1
    let earlier := (bs.take j.val).flatten
    let here := bs[j.val]'(by simp [bs])
    let later := (bs.drop (j.val+1)).flatten ++ (handoff cost H r xs).2
    earlier ++ (here ++ later) = xs ∧ (xs.drop earlier.length).take here.length = here := by
  intro bs earlier here later
  have hj : j.val < bs.length := by simp [bs]
  have hg : bs.take j.val ++ (here :: bs.drop (j.val+1)) = bs := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have heq : earlier ++ (here ++ later) = xs := by
    have h := congrArg (fun l : List (List α) => l.flatten ++ (handoff cost H r xs).2) hg
    simpa [earlier, later, bs, List.flatten_append, List.append_assoc, handoff_flatten] using h
  refine ⟨heq, ?_⟩
  conv_lhs => rw [← heq]
  simp

/-- Consecutive processors make the same state transitions as the bounded trace. -/
theorem fold_handoff {S : Type*} (step : S → α → S) (state : S)
    (cost : α → ℕ) (H Q r : ℕ) (xs : List α)
    (hc : ∀ a ∈ xs, 0 < cost a ∧ cost a ≤ Q + 1)
    (hbudget : ticks cost xs ≤ r * (H - Q)) :
    (handoff cost H r xs).1.foldl (fun s b => b.foldl step s) state = xs.foldl step state := by
  have h := handoff_flatten cost H r xs
  rw [handoff_covers cost H Q r xs hc hbudget, List.append_nil] at h
  rw [fold_blocks, h]

end LinearAlgebra.SpectralBooks.VNP.Team

end OAI
