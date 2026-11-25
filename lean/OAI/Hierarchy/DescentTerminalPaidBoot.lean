import OAI.Hierarchy.DescentTerminalAppendixNumbers
import OAI.Hierarchy.DescentTerminalBoot
import OAI.Hierarchy.DescentTerminalDenseGraphRead
import OAI.Hierarchy.DescentTerminalPrimitiveSpace

namespace OAI
/-! # The paid raw payload beside the two shared chip proposals and public dictionaries -/
namespace Hierarchy.DescentTerminalPaidBoot
open DescentTerminalPorts DescentTerminalChipPins DescentTerminalDenseWindow DescentTerminalDenseGraphRead
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.Diagonal
open scoped Classical Fin.CommRing
noncomputable section
variable {K W q piece rows w : ℕ}
local notation "B" => q*(W*piece)

abbrev Input (K W q piece rows : ℕ) :=
  Inputs K W q piece ⊕ RowBit rows (q*(W*piece))

def candidate (K W q piece codes rows origin : ℕ) : ProtocolRAM.Bank :=
  ⟨origin+DescentTerminalBoot.total K W q piece codes,Nat.clog 2 rows⟩

theorem candidate_size (K W q piece codes rows origin : ℕ) :
    rows ≤ (candidate K W q piece codes rows origin).size :=
  DescentTerminalPrimitiveArena.covered rows

theorem candidate_end (K W q piece codes rows origin : ℕ) :
    (candidate K W q piece codes rows origin).base + (candidate K W q piece codes rows origin).size =
      origin + total K W q piece codes rows := by
  change (origin+_)+_ = origin+(_+_)
  exact Nat.add_assoc ..

theorem candidate_fits (K W q piece codes rows origin : ℕ) {start w : ℕ}
    (below : origin + total K W q piece codes rows ≤ start) (word : start < 2^w) :
    (candidate K W q piece codes rows origin).Fits w start := by
  have stop := (candidate_end K W q piece codes rows origin).le.trans below
  exact ⟨Nat.two_pow_pos _,by omega,stop⟩

theorem total_le (K W q piece codes rows : ℕ) :
    total K W q piece codes rows ≤ DescentTerminalBoot.total K W q piece codes + (2*rows+1) :=
  Nat.add_le_add_left (DescentTerminalPrimitiveArena.pad_le rows) _

def raw {n d : ℕ} (w : ℕ) (pay : RowBit n d → Bool) : Memory w :=
  fun i => ((dense d (stream pay) i).val : Word w)

def back (z : Input K W q piece rows → Bool) (w codes : ℕ) : Memory w :=
  DescentExteriorShelf.Root.appended (DescentTerminalBoot.total K W q piece codes) (DescentTerminalPrimitiveArena.pad rows)
    (DescentTerminalBoot.back (z ∘ Sum.inl) w codes) (raw w (z ∘ Sum.inr))

private def rawPin (K W q piece rows w : ℕ) (i : Fin (DescentTerminalPrimitiveArena.pad rows) × Fin (w+1)) :
    Input K W q piece rows ⊕ Bool :=
  if row : i.1.val < rows then
    if bit : i.2.val < q*(W*piece) then .inl (.inr (⟨i.1.val,row⟩,⟨i.2.val,bit⟩)) else .inr false
  else .inr false

private theorem rawPin_read (z : Input K W q piece rows → Bool) (w : ℕ) (room : B ≤ w)
    (i : Fin (DescentTerminalPrimitiveArena.pad rows) × Fin (w+1)) :
    (rawPin K W q piece rows w i).elim z id =
      TraceWords.bits (TraceBanks.wide (raw w (z ∘ Sum.inr) i.1.val)) i.2 := by
  let pay : RowBit rows B → Bool := z ∘ Sum.inr
  let v := dense B (stream pay) i.1.val
  have fit : v.val < 2^w := v.isLt.trans_le (Nat.pow_le_pow_right (by decide) room)
  change _ = (v.val : Word w).val.testBit i.2.val
  rw [Fin.val_cast_of_lt fit]
  by_cases row : i.1.val < rows
  · by_cases bit : i.2.val < B
    · simp only [rawPin,dite_eq_left row,dite_eq_left bit,Sum.elim_inl]
      exact (raw_at pay ⟨_,row⟩ ⟨_,bit⟩).symm.trans
        (Computability.VPVNP.LiveHeader.testBit_wordBits v ⟨_,bit⟩).symm
    · simp only [rawPin,dite_eq_left row,dite_eq_right bit,Sum.elim_inr,id_eq]
      exact (Nat.testBit_lt_two_pow (v.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt bit)))).symm
  · have blank : v = 0 := raw_sentinel pay i.1.val (Nat.le_of_not_gt row)
    simp [rawPin,row,blank]

private def priorPin (K W q piece rows w codes : ℕ)
    (i : Fin (DescentTerminalBoot.total K W q piece codes) × Fin (w+1)) : Input K W q piece rows ⊕ Bool :=
  (DescentTerminalBoot.pins K W q piece w codes i).map Sum.inl id

def pins (K W q piece rows w codes : ℕ) :
    Fin (total K W q piece codes rows) × Fin (w+1) → Input K W q piece rows ⊕ Bool :=
  DescentExteriorShelf.Root.appendPin _ _ (priorPin K W q piece rows w codes) (rawPin K W q piece rows w)

theorem pins_read (z : Input K W q piece rows → Bool) (w codes : ℕ) (room : B ≤ w)
    (i : Fin (total K W q piece codes rows) × Fin (w+1)) :
    (pins K W q piece rows w codes i).elim z id =
      TraceWords.bits (TraceBanks.wide (back z w codes i.1.val)) i.2 := by
  apply DescentExteriorShelf.Root.appendPin_read
  · intro j
    have h := DescentTerminalBoot.pins_read (z ∘ Sum.inl) w codes room j
    change ((DescentTerminalBoot.pins K W q piece w codes j).map Sum.inl id).elim z id = _
    cases eqn : DescentTerminalBoot.pins K W q piece w codes j <;> rw [eqn] at h <;> exact h
  · exact rawPin_read z w room

theorem ranges (z : Input K W q piece rows → Bool) (w codes origin : ℕ) (m : Memory w)
    (kept : ∀ j < total K W q piece codes rows, m (origin+j) = back z w codes j) :
    (∀ j < DescentTerminalBoot.total K W q piece codes,
      m (origin+j) = DescentTerminalBoot.back (z ∘ Sum.inl) w codes j) ∧
    (∀ j < DescentTerminalPrimitiveArena.pad rows,
      m ((candidate K W q piece codes rows origin).base+j) = raw w (z ∘ Sum.inr) j) := by
  constructor
  · intro j live
    exact (kept _ (live.trans_le (Nat.le_add_right ..))).trans (DescentExteriorShelf.Root.append_low _ _ _ _ live)
  · intro j live
    change m ((origin+DescentTerminalBoot.total K W q piece codes)+j) = _
    rw [Nat.add_assoc]
    exact (kept _ (Nat.add_lt_add_left live _)).trans
      (DescentExteriorShelf.Root.suffix_read _ _ _ _ ⟨j,live⟩)

theorem rawRead (z : Input K W q piece rows → Bool) (w codes origin : ℕ) (m : Memory w)
    (kept : ∀ j < total K W q piece codes rows, m (origin+j) = back z w codes j) (i : Fin rows) :
    m ((candidate K W q piece codes rows origin).base+i.val) =
      ((dense B (stream (z ∘ Sum.inr)) i.val).val : Word w) :=
  (ranges z w codes origin m kept).2 i.val (i.isLt.trans_le (DescentTerminalPrimitiveArena.covered rows))

end
end Hierarchy.DescentTerminalPaidBoot

end OAI
