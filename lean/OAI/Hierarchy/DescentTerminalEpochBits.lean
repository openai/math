import OAI.Hierarchy.DescentTerminalProfileCodes
import OAI.ThreeFlat.Diagonal.TraceWordTests

namespace OAI
/-! # Canonical raw Boolean bank for one dense matched profile deck -/

namespace Hierarchy.DescentTerminalEpochBits
open DescentTerminalEpochFlags DescentSixParty Computability.VPVNP.BurstRAM
open ThreeFlat.Diagonal
open scoped Classical Fin.CommRing
noncomputable section
variable {C seats count : ℕ} {I : Type*}

def width (C : ℕ) := Nat.clog 2 (alphabet C)
abbrev Pins (C seats : ℕ) := Fin seats × Fin (width C)

def wordBits (u : ℕ) : Word u ≃ (Fin u→Bool) :=
  Equiv.ofBijective TraceWords.bits ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨TraceWords.bits_injective, by simp [Word]⟩)

def raw (z : Pins C seats → Bool) (i : Fin seats) : ℕ :=
  ((wordBits (width C)).symm (fun b=>z (i,b))).val

def codeWord (number : I≃Fin count) (p : I→Profile C) (i : Fin seats) : ℕ :=
  if h : i.val < count then encode (p (number.symm ⟨i.val,h⟩)) else 0

def store (number : I≃Fin count) (p : I→Profile C) : Pins C seats → Bool :=
  fun a=>wordBits _ (codeWord number p a.1 : Word (width C)) a.2

theorem code_fits (number : I≃Fin count) (p : I→Profile C) (i : Fin seats) :
    codeWord number p i < 2^width C := by
  unfold codeWord
  split
  · exact ((finFunctionFinEquiv _).isLt : encode _ < alphabet C).trans_le (Nat.le_pow_clog (by decide) _)
  · exact Nat.two_pow_pos _

theorem raw_store (number : I≃Fin count) (p : I→Profile C) (i : Fin seats) :
    raw (store number p) i=codeWord number p i := by
  change ((wordBits _).symm ((wordBits _) (codeWord number p i : Word (width C)))).val=_
  rw [Equiv.symm_apply_apply,Fin.val_cast_of_lt (code_fits number p i)]

theorem raw_injective (C seats : ℕ) : Function.Injective (@raw C seats) := by
  intro z y h
  funext a
  rcases a with ⟨i,b⟩
  have e : (wordBits _).symm (fun b=>z (i,b))=(wordBits _).symm (fun b=>y (i,b)) := Fin.ext (congrFun h i)
  exact congrFun ((wordBits (width C)).symm.injective e) b

def Good (count : ℕ) (z : Pins C seats → Bool) := ∀i,SeatValid C count (raw z i) i.val

def read (number : I≃Fin count) (bound : count ≤ seats) (z : Pins C seats→Bool) : Option (I→Profile C) :=
  if ok : Good count z then some ((valid_unique number bound (raw z) ok).exists.choose) else none

theorem read_iff (number : I≃Fin count) (bound : count ≤ seats) (z : Pins C seats→Bool) (p : I→Profile C) :
    read number bound z = some p ↔ z=store number p := by
  constructor
  · intro hit
    unfold read at hit
    split at hit
    · rename_i ok
      cases Option.some.inj hit
      have selected := (valid_unique number bound (raw z) ok).exists.choose_spec
      apply raw_injective C seats
      funext i
      exact (selected i).trans (raw_store number _ i).symm
    · contradiction
  · rintro rfl
    have good : Good count (store (seats:=seats) number p) :=
      (valid_iff number bound _).mpr ⟨p,raw_store number p⟩
    have unique := valid_unique number bound (raw (store number p)) good
    have h := unique.unique unique.exists.choose_spec (raw_store number p)
    simp [read,good,h]

theorem survives (number : I≃Fin count) (bound : count ≤ seats) (z : Pins C seats→Bool) :
    Good count z ↔ ∃p,read number bound z=some p := by
  by_cases h : Good count z <;> simp [read,h]

/-- A source header carries the literal raw selector bits, even outside the profile range. -/
def header (w C seats : ℕ) (z : Pins C seats→Bool) (i : ℕ) : Word w :=
  if h : i < seats then (raw z ⟨i,h⟩ : Word w) else 0

theorem header_word (w : ℕ) (wide : width C ≤ w) (z : Pins C seats→Bool) (i : Fin seats) :
    (header w C seats z i.val).val=raw z i := by
  have hi : raw z i < 2^width C := ((wordBits _).symm _).isLt
  have enough : 2^width C ≤ 2^w := Nat.pow_le_pow_right (by decide) wide
  simp [header,i.isLt,Fin.val_cast_of_lt (hi.trans_le enough)]

end
end Hierarchy.DescentTerminalEpochBits

end OAI
