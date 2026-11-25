import OAI.ThreeFlat.Diagonal.TraceIssue
import OAI.ThreeFlat.Diagonal.TraceAdjacent

namespace OAI
/-! # Reading the fetched-instruction checks as adjacent row conditions -/

namespace ThreeFlat.Diagonal.TraceIssue

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM TraceBanks

variable {w p r k : ℕ} {C : Type*}

theorem follows_move_iff (a : CallAction w C) (e : Event w) (d : C) :
    Follows a (.move e d) ↔ TraceRows.next? a e = some d := by
  cases a with
  | localStep z | branch z | finish z | reject =>
    cases e <;> simp [Follows, TraceRows.next?, eq_comm]
  | read addr next =>
    cases e with
    | read b v =>
      by_cases h : addr = b <;> simp [Follows, TraceRows.next?, h, eq_comm]
    | tick | choice | write => simp [Follows, TraceRows.next?]
  | write addr v z =>
    cases e with
    | write b u =>
      by_cases h : addr = b ∧ v = u
      · obtain ⟨rfl,rfl⟩ := h
        simp [Follows, TraceRows.next?, eq_comm]
      · simp [Follows, TraceRows.next?, h, and_assoc]
        grind
    | tick | choice | read => simp [Follows, TraceRows.next?]

theorem follows_halt_iff (a : CallAction w C) (out : Option (Word w)) :
    Follows a (.halt out) ↔ a = .finish out := by
  cases a <;> simp [Follows, eq_comm]

/-- For two active rows the local circuit checks exactly the native transition
from the first row's registers to the second row's registers. -/
theorem circuit_move (M : Machine w p r k) (s t : Snapshot w p r) (e : Event (w+1)) :
    ((issueFrame M).circuit ()).eval (valuation M s (.move e t)) = true ↔
      TraceRows.next? ((exposed M).step s) e = some t := by
  rw [circuit_true, follows_move_iff]

/-- A terminal marker matches precisely the word returned by this instruction. -/
theorem circuit_halt (M : Machine w p r k) (s : Snapshot w p r) (out : Option (Word (w+1))) :
    ((issueFrame M).circuit ()).eval (valuation M s (.halt out)) = true ↔
      (exposed M).step s = .finish out := by
  rw [circuit_true, follows_halt_iff]

end ThreeFlat.Diagonal.TraceIssue

end OAI
