import OAI.Hierarchy.DescentTerminalAppendixNumbers
import OAI.Hierarchy.DescentTerminalChipBootPins
import OAI.Hierarchy.DescentTerminalDenseHeaderBoot
import OAI.Hierarchy.DescentExteriorAppendedWords

namespace OAI
/-! # One appended terminal header for proposal views and all shared static dictionaries -/
namespace Hierarchy.DescentTerminalBoot
open Computability.VPVNP.BurstRAM PrivateRAM DescentTerminalChipPins
open ThreeFlat.Diagonal
noncomputable section
variable {K W q piece : ℕ}

def back (z : Inputs K W q piece → Bool) (w codes : ℕ) : Memory w :=
  DescentExteriorShelf.Root.appended (DescentTerminalChipBootWords.total K W q piece codes)
    (DescentTerminalDenseHeaderBoot.extent q (W*piece))
    (DescentTerminalChipBootWords.back z w codes) (DescentTerminalDenseHeaderBoot.back w q (W*piece))

def pins (K W q piece w codes : ℕ) :
    Fin (total K W q piece codes) × Fin (w+1) → Inputs K W q piece ⊕ Bool :=
  DescentExteriorShelf.Root.appendPin (DescentTerminalChipBootWords.total K W q piece codes)
    (DescentTerminalDenseHeaderBoot.extent q (W*piece)) (DescentTerminalChipBootWords.backPin K W q piece w codes)
    (DescentTerminalDenseHeaderBoot.backPin w q (W*piece))

theorem pins_read (z : Inputs K W q piece → Bool) (w codes : ℕ) (room : q*(W*piece) ≤ w)
    (i : Fin (total K W q piece codes) × Fin (w+1)) :
    (pins K W q piece w codes i).elim z id = TraceWords.bits (TraceBanks.wide (back z w codes i.1.val)) i.2 :=
  DescentExteriorShelf.Root.appendPin_read _ _ z _ _ _ _
    (DescentTerminalChipBootWords.backPin_read z w codes room)
    (DescentTerminalDenseHeaderBoot.backPin_read z w q (W*piece)) i

theorem ten (z : Inputs K W q piece → Bool) (w codes : ℕ) {j : ℕ}
    (valid : j < DescentTerminalChipBootWords.total K W q piece codes) :
    back z w codes j = DescentTerminalChipBootWords.back z w codes j :=
  DescentExteriorShelf.Root.append_low _ _ _ _ valid

theorem header (z : Inputs K W q piece → Bool) (w codes : ℕ) {j : ℕ}
    (valid : j < DescentTerminalDenseHeaderBoot.extent q (W*piece)) :
    back z w codes (DescentTerminalChipBootWords.total K W q piece codes+j) =
      DescentTerminalDenseHeaderBoot.back w q (W*piece) j :=
  DescentExteriorShelf.Root.suffix_read _ _ _ _ ⟨j,valid⟩

/-- A single preserved input range supplies both native chip banks and both
cable/exterior lookups into the same four header tables. -/
theorem ranges (z : Inputs K W q piece → Bool) (w codes front : ℕ) (m : Memory w)
    (kept : ∀ j < total K W q piece codes, m (front+j) = back z w codes j) :
    (∀ j < DescentTerminalChipBootWords.total K W q piece codes,
      m (front+j) = DescentTerminalChipBootWords.back z w codes j) ∧
    (∀ j < DescentTerminalDenseHeaderBoot.extent q (W*piece),
      m (front+DescentTerminalChipBootWords.total K W q piece codes+j) =
        DescentTerminalDenseHeaderBoot.back w q (W*piece) j) := by
  constructor
  · intro j live
    exact (kept j (live.trans_le (Nat.le_add_right ..))).trans (ten z w codes live)
  · intro j live
    rw [Nat.add_assoc]
    exact (kept _ (Nat.add_lt_add_left live _)).trans (header z w codes live)

end
end Hierarchy.DescentTerminalBoot

end OAI
