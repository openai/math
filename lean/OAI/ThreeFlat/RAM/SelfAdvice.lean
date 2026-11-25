import OAI.ThreeFlat.RAM.ProgramValue
import OAI.ThreeFlat.Diagonal.TraceBitInput

namespace OAI
/-! # One binary description carrying both executables and the common finite advice -/

namespace ThreeFlat.RAM.SelfAdvice

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TraceBitHeader
variable {w p r k p' r' k' q g : ℕ}

abbrev textSize (w p k : ℕ) := (1+6*p+k)*w

structure Fits (w p k p' k' g q : ℕ) : Prop where
  room : textSize w p k + textSize w p' k' + g ≤ q

variable (tick : Machine w p r k) (H : Machine w p' r' k')
variable (extra : Fin g → Bool)

def suffix (i : Fin q) : Bool :=
  if h : i.val < textSize w p k + textSize w p' k' ∧ textSize w p k ≤ i.val then
    programBits H ⟨i.val-textSize w p k,by change i.val-textSize w p k<textSize w p' k'; omega⟩
  else if h : i.val < textSize w p k + textSize w p' k' + g ∧
      textSize w p k + textSize w p' k' ≤ i.val then
    extra ⟨i.val-(textSize w p k+textSize w p' k'),by omega⟩
  else false

def description : Fin q → Bool :=
  installProgram tick (suffix (p:=p) (k:=k) H extra)

variable (room : Fits w p k p' k' g q)

theorem tick_bits (i : Fin (textSize w p k)) :
    description (q:=q) tick H extra ⟨i.val,by have := room.room; have := i.isLt; omega⟩ = programBits tick i := by
  unfold description installProgram
  rw [dite_eq_left i.isLt]

theorem h_bits (i : Fin (textSize w p' k')) :
    description (q:=q) tick H extra ⟨textSize w p k+i.val,by have := room.room; have := i.isLt; omega⟩ =
      programBits H i := by
  have hi := i.isLt
  rw [description,installProgram_after _ _ _ (Nat.le_add_right _ _)]
  unfold suffix
  rw [dite_eq_left (show textSize w p k+i.val<textSize w p k+textSize w p' k' ∧
    textSize w p k≤textSize w p k+i.val by omega)]
  apply congrArg (programBits H)
  apply Fin.ext
  change textSize w p k+i.val-textSize w p k=i.val
  omega

theorem extra_bits (i : Fin g) :
    description (q:=q) tick H extra ⟨textSize w p k+textSize w p' k'+i.val,by
      have := room.room; have := i.isLt; omega⟩ = extra i := by
  have hi := i.isLt
  rw [description,installProgram_after _ _ _ (by
    change textSize w p k≤textSize w p k+textSize w p' k'+i.val
    omega)]
  unfold suffix
  rw [dite_eq_right (show ¬(textSize w p k+textSize w p' k'+i.val<textSize w p k+textSize w p' k' ∧
    textSize w p k≤textSize w p k+textSize w p' k'+i.val) by omega)]
  rw [dite_eq_left (show textSize w p k+textSize w p' k'+i.val<textSize w p k+textSize w p' k'+g ∧
    textSize w p k+textSize w p' k'≤textSize w p k+textSize w p' k'+i.val by omega)]
  apply congrArg extra
  apply Fin.ext
  change textSize w p k+textSize w p' k'+i.val-(textSize w p k+textSize w p' k')=i.val
  omega

theorem decode_tick (fit : TextFits w p r k) :
    readAdvicePrefix w p r k (by have := room.room; omega : textSize w p k≤q)
      (description tick H extra) = some tick :=
  readAdvicePrefix_install tick fit _ _

def hText (D : Fin q → Bool) : Fin (textSize w p' k') → Bool :=
  fun i => D ⟨textSize w p k+i.val,by have := room.room; omega⟩

theorem decode_H (fit : TextFits w p' r' k') :
    readAdvicePrefix w p' r' k' (le_refl _) (hText room (description tick H extra)) = some H := by
  apply readAdvicePrefix_eq H fit
  intro i
  exact h_bits tick H extra room i

/-- The public code segment of the virtual H header can be read straight from the common
description. Other addresses access the ordinary raw H tape, which itself contains the same D. -/
theorem public_header {S : ℕ} (mount : ℕ) (raw : ℕ → Bool) :
    advicePins (S:=S) mount (hText room (description tick H extra)) raw =
    advicePins mount (fun i : Fin (textSize w p' k') => programBits H i) raw := by
  congr 1
  funext i
  exact h_bits tick H extra room i

end ThreeFlat.RAM.SelfAdvice

end OAI
