import OAI.Hierarchy.DescentTerminalAppendixNumbers
import OAI.Hierarchy.DescentTerminalPaidBoot

namespace OAI
/-! # The immutable last column of the terminal input and its literal pins -/
namespace Hierarchy.DescentTerminalPublicIdentity
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.Diagonal
open DescentTerminalPaidBoot DescentTerminalPrimitiveArena
open scoped Fin.CommRing
noncomputable section
variable {K W q piece rows : ℕ}
local notation "B" => q*(W*piece)
local notation "Paid" => DescentTerminalPaidBoot.Input K W q piece rows

def bank (start publicRows : ℕ) : ProtocolRAM.Bank := ⟨start,Nat.clog 2 publicRows⟩

def back (z : Paid→Bool) (w codes publicRows : ℕ) : Memory w :=
  DescentExteriorShelf.Root.appended (DescentTerminalPaidBoot.total K W q piece codes rows) (pad publicRows)
    (DescentTerminalPaidBoot.back z w codes) (fun i=>(i:Word w))

def pins (K W q piece rows publicRows w codes : ℕ) :
    Fin (total K W q piece codes rows publicRows)×Fin (w+1)→DescentTerminalPaidBoot.Input K W q piece rows⊕Bool :=
  DescentExteriorShelf.Root.appendPin _ _ (DescentTerminalPaidBoot.pins K W q piece rows w codes)
    (fun i=>.inr (TraceWords.bits (TraceBanks.wide (i.1.val:Word w)) i.2))

theorem pins_read (z : Paid→Bool) (w codes publicRows : ℕ) (room : B ≤ w)
    (i : Fin (total K W q piece codes rows publicRows)×Fin (w+1)) :
    (pins K W q piece rows publicRows w codes i).elim z id=
      TraceWords.bits (TraceBanks.wide (back z w codes publicRows i.1.val)) i.2 := by
  apply DescentExteriorShelf.Root.appendPin_read
  · exact DescentTerminalPaidBoot.pins_read z w codes room
  · intro a; rfl

theorem total_le (K W q piece codes rows publicRows : ℕ) :
    total K W q piece codes rows publicRows ≤ DescentTerminalPaidBoot.total K W q piece codes rows+(2*publicRows+1) :=
  Nat.add_le_add_left (pad_le _) _

theorem ranges {w : ℕ} (z : Paid→Bool) (codes publicRows origin : ℕ) (m : Memory w)
    (kept : ∀i < total K W q piece codes rows publicRows,m (origin+i)=back z w codes publicRows i) :
    (∀i < DescentTerminalPaidBoot.total K W q piece codes rows,m (origin+i)=DescentTerminalPaidBoot.back z w codes i) ∧
    (∀i < pad publicRows,m (origin+DescentTerminalPaidBoot.total K W q piece codes rows+i)=(i:Word w)) := by
  constructor
  · intro i live
    exact (kept i (live.trans_le (Nat.le_add_right ..))).trans (DescentExteriorShelf.Root.append_low _ _ _ _ live)
  · intro i live
    rw [Nat.add_assoc]
    exact (kept _ (Nat.add_lt_add_left live _)).trans
      (DescentExteriorShelf.Root.suffix_read _ _ _ _ ⟨i,live⟩)

theorem reads {w : ℕ} {m : Memory w} (n addr : ℕ) (fits : pad n < 2^w)
    (held : ∀i < pad n,m (addr+i)=(i:Word w)) :
    (∀i : Fin n,(bank addr n).read m (i.val:Word w)=(i.val:Word w)) ∧
      ∀u : Word w,(⟨addr,0⟩:ProtocolRAM.Bank).read m u=0 := by
  constructor
  · intro i
    have hi : i.val < pad n := i.isLt.trans_le (covered n)
    change m (addr + (i.val : Word w).val % pad n) = (i.val : Word w)
    rw [Fin.val_cast_of_lt (hi.trans fits), Nat.mod_eq_of_lt hi]
    exact held i.val hi
  · intro u
    change m (addr + u.val % 1) = 0
    rw [Nat.mod_one]
    exact held 0 (Nat.two_pow_pos _)

end
end Hierarchy.DescentTerminalPublicIdentity

end OAI
