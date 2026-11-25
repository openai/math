import OAI.Computability.BorderVNP.GeometryAdviceStripe
import OAI.Computability.BorderVNP.GeometryOutput
import OAI.Computability.BorderVNP.TransmissionPinsInput

/-! # Installing the shared gate payload in the physical processor literals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryAdvice

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- A finite, canonical Boolean serialization of the descriptor words in low-bit-first
order, as expected by the ordinary physical word decoder. -/
def serialized {w : ℕ} (xs : List (Word w)) : List Bool := (xs.map wordBits).flatten

/-- Serialization has exactly the native word width times the payload word count. -/
theorem serialized_length {w : ℕ} (xs : List (Word w)) : (serialized xs).length = xs.length*w := by
  induction xs with
  | nil => simp [serialized]
  | cons x xs ih => simp [serialized,wordBits,List.length_cons,Nat.succ_mul] at ih ⊢; omega

/-- Fill the occupied part of a processor's literal stripe, retaining the original
literal outside that part. This permits the validator, public header, residue advice
and the private tail to be chosen independently. -/
def Stripe.literal (a : Stripe) (bits : List Bool) (p : ℕ) (old : List Bool) : List Bool :=
  List.ofFn fun j : Fin old.length =>
    let i := p*a.width+(j.val-a.offset)
    if h : a.offset ≤ j.val ∧ j.val < a.offset+a.width ∧ i < bits.length then bits[i]'h.2.2 else old[j.val]

/-- Updating the geometry stripe preserves every processor's fixed literal length. -/
theorem Stripe.literal_length (a : Stripe) (bits : List Bool) (p : ℕ) (old : List Bool) :
    (a.literal bits p old).length = old.length := List.length_ofFn

/-- Original bit reads outside the reserved stripe, including the residue advice
in the prefix and the bottom-bundle description in the literal suffix. -/
theorem Stripe.literal_outside (a : Stripe) (bits : List Bool) (p : ℕ) (old : List Bool)
    (j : Fin old.length) (out : j.val < a.offset ∨ a.offset+a.width ≤ j.val) :
    (a.literal bits p old)[j.val]? = old[j.val]? := by
  have h : ¬ (a.offset ≤ j.val ∧ j.val < a.offset+a.width ∧ p*a.width+(j.val-a.offset)<bits.length) := by omega
  simp [literal,j.isLt,h]

/-- The physical geometry payload installs a literal of the same size on every actual
processor, preserving the separate exterior and secondary pin fields. -/
def Stripe.install (a : Stripe) {L : Pins.Layout} (P : Pins.ProcessorFields L) (bits : List Bool) :
    Pins.ProcessorFields L :=
  { P with literal := fun p => a.literal bits p.val (P.literal p)
           literal_length := fun p => (a.literal_length ..).trans (P.literal_length p) }

/-- Each serialized bit can be read at its precise physical address in the RAM initialized
from the installed processor fields. The final processor may carry a partial stripe. -/
theorem Stripe.installed_bit {w : ℕ} (a : Stripe) {L : Pins.Layout} (P : Pins.ProcessorFields L)
    (bits : List Bool) (m : Memory w) (image : (a.install P bits).ContainsInput m)
    (widthPos : 0<a.width) (headRoom : a.offset+a.width ≤ L.literal)
    (capacity : bits.length ≤ L.processors*a.width) (i : Fin bits.length) :
    m (a.src L.stride i.val) = DiagonalResidueRAM.word w (bits[i.val].toNat) := by
  let p : Fin L.processors := ⟨i.val/a.width,(Nat.div_lt_iff_lt_mul widthPos).mpr (i.isLt.trans_le capacity)⟩
  have ht := Nat.mod_lt i.val widthPos
  let j : Fin L.literal := ⟨a.offset+i.val%a.width,by omega⟩
  have hp := image.literal p j
  rw [src,Nat.add_assoc]
  change m (p.val*L.stride+j.val) = _
  rw [hp]
  have hj : j.val < (P.literal p).length := (P.literal_length p).symm ▸ j.isLt
  have hindex : p.val*a.width+(j.val-a.offset) = i.val := by
    dsimp only [p,j]
    rw [Nat.add_sub_cancel_left,Nat.div_add_mod']
  have guard : a.offset ≤ j.val ∧ j.val < a.offset+a.width ∧ p.val*a.width+(j.val-a.offset)<bits.length :=
    ⟨Nat.le_add_right ..,Nat.add_lt_add_left ht _,hindex ▸ i.isLt⟩
  simp [TeamTapeInputEmit.headerWord,install,literal,hj,guard,hindex,i.isLt]
  rfl

/-- After the native deinterleaver, the contiguous bit words satisfy the exact
little-endian input relation of the physical payload decoder. -/
theorem Stripe.dense_words {w : ℕ} (a : Stripe) {L : Pins.Layout} (P : Pins.ProcessorFields L)
    (xs : List (Word w)) (m : Memory w) (installed : (a.install P (serialized xs)).ContainsInput m)
    (widthPos : 0<a.width) (headRoom : a.offset+a.width ≤ L.literal) (count : xs.length = a.words)
    (capacity : a.words*w ≤ L.processors*a.width) (hw : 0<w) :
    DiagonalTallyBits.WordsAt (a.image L.stride m (a.words*w)) a.dense (xs.map wordBits) := by
  apply GeometryOutput.wordsAt_of_get
  intro i
  have size : (serialized xs).length = a.words*w := (serialized_length xs).trans (congrArg (· *w) count)
  have hfit : i.val < a.words*w := size ▸ i.isLt
  rw [a.image_at m hfit]
  have hx := a.installed_bit P (serialized xs) m installed widthPos headRoom (size ▸ capacity) i
  rw [hx]
  apply DiagonalResidueRAM.word_val
  cases (serialized xs)[i.val] <;> simp [Nat.one_lt_two_pow hw.ne']

end GeometryAdvice

end BorderVNP
end Computability
end OAI
