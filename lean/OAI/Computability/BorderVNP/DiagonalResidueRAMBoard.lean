import OAI.Computability.BorderVNP.DiagonalResidueRAMPins
import OAI.Computability.BorderVNP.ResidueEntryInput
import OAI.Computability.BorderVNP.DiagonalEntry

/-!
# Wiring external pins and unshifted team tallies to the residue verifier

The physical pin fields and tally words are little-endian. The Laurent
preprocessor expects three high-bit-first offset words. The only arithmetic
in this wiring adds the advised box radius to each parameter multiplicity
using a bit adder at the full index width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM.Board

open Diagonal ResidueEntryInput ResidueEntryField ExactQuantumFactoring BooleanNetwork BitArithmetic
open ResiduePins ResidueBox VPVNP.RAMSerialization
open scoped Classical

/-- The row and column pin fields and the team's serialized parameter and gadget tallies. -/
abbrev Physical (h pin tally : ℕ) (J : Type*) :=
  (Bool × Fin ((h+2)*pin)) ⊕ ((Fin h ⊕ J) × Fin tally)

variable {h pin tally idx m D H : ℕ} {J G : Type*} [Fintype J] [Fintype G]

set_option maxHeartbeats 2000000

local notation "BoardTape" => Physical h pin tally J ⊕ G
local notation "Net" => BooleanNetwork (Fintype.card BoardTape)

/-- The actual public bits are packed pin fields and unsigned team tallies.
There is no tally for the distinguished time coordinate. -/
def physicalInput (row col : Fin ((h+2)*pin) → Bool) (μ : Fin h → ℕ) (δ : J → ℕ) :
    Physical h pin tally J → Bool :=
  Sum.elim (fun (side,j) => (if side then col else row) j)
    (fun (t,j) => (Sum.elim μ δ t).testBit j.val)

/-- Pin field zero holds the basis address, field one the time exponent. -/
def exponentField : Option (Fin h) → Fin (h+2)
  | none => 1
  | some j => j.succ.succ

/-- A physical packed pin selected from the joint input. -/
noncomputable def pinBits (side : Bool) : Net ((h+2)*pin) :=
  route (fun j => (.inl (.inl (side,j)) : BoardTape))

/-- A physical tally word selected from the joint input. -/
noncomputable def tallyBits (tag : Fin h ⊕ J) : Net tally :=
  route (fun j => (.inl (.inr (tag,j)) : BoardTape))

/-- The shifted unsigned multiplier at index width. Its time-coordinate power is zero. -/
noncomputable def offsetNet (idx H : ℕ) (i : Option (Fin h)) : Net idx :=
  match i with
  | none => literal _ idx H
  | some j => ((((tallyBits (.inl j)).comp (resizeWord tally idx)).pair (literal _ idx H)).comp (add idx))

/-- Select one bit of an already computed shared word. -/
def pick {n k : ℕ} (A : BooleanNetwork n k) (i : Fin k) : BooleanNetwork n 1 :=
  A.rewire (fun _ => i)

/-- A complete joint verifier input bit, routed from the physical packet.
Taking a bit after resizing zero-extends small fields and reverses the
exponent words to the preprocessor's high-bit-first convention. -/
noncomputable def queryBit (H : ℕ) : (Query (Fin h) idx D J m ⊕ G) → Net 1
  | .inl (.inl (tag,i,j)) =>
    if tag = 1 then pick (offsetNet idx H i) j.rev
    else pick (((pinBits (tag != 0)).comp (Pins.field (exponentField i))).comp
      (resizeWord pin idx)) j.rev
  | .inl (.inr (.inl (side,j))) =>
    pick (((pinBits side).comp (Pins.field 0)).comp (resizeWord pin (Nat.clog 2 D))) j
  | .inl (.inr (.inr (l,j))) => pick ((tallyBits (.inr l)).comp (resizeWord tally m)) j
  | .inr g => bit (Fintype.equivFin BoardTape (.inr g))

private theorem resizeBit {n a k : ℕ} (A : BooleanNetwork n a) (x : Basis n) (j : Fin k) :
    ((A.comp (resizeWord a k)).eval x j) = (value (A.eval x)).testBit j.val := by
  rw [eval_comp, ← bitsValue_bit ((resizeWord a k).eval (A.eval x)) j,resizeWord_value,BitVec.getLsbD_setWidth]
  simp [value,BitVec.getLsbD,j.isLt]

private theorem offset_value (H : ℕ) (i : Option (Fin h)) (row col : Fin ((h+2)*pin) → Bool)
    (μ : Fin h → ℕ) (δ : J → ℕ) (guess : G → Bool) (hm : ∀ j, μ j < 2^tally)
    (b : Fin idx) :
    (offsetNet idx H i).eval (number (Sum.elim (physicalInput (tally := tally) row col μ δ) guess)) b =
      ((i.elim 0 μ) + H).testBit b.val := by
  cases i with
  | none =>
    rw [offsetNet,literal,← bitsValue_bit ((wordConstant _).eval _) b,wordConstant_eval]
    simp only [BitVec.getLsbD_ofNat, b.isLt, decide_true, Bool.true_and, Option.elim_none, zero_add]
  | some j =>
    let x := number (Sum.elim (physicalInput (tally := tally) row col μ δ) guess)
    have hv : value ((tallyBits (.inl j)).eval x) = μ j := by
      change value ((route _).eval (number _)) = _
      rw [route_eval]
      exact bitsValue_ofFn ⟨μ j,hm j⟩
    rw [offsetNet,eval_comp,eval_pair,add_correct,leftWord_append,rightWord_append,eval_comp,resizeWord_value,
      literal,wordConstant_eval,BitVec.getLsbD,BitVec.toNat_add,
      BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    change (((value ((tallyBits (.inl j)).eval x)) % 2^idx + H % 2^idx) % 2^idx).testBit b.val = _
    rw [hv, ← Nat.add_mod, Nat.testBit_mod_two_pow]
    simp

private theorem pin_field_val (hβ : D ≤ 2^pin) (hH : 2*H < 2^pin)
    (i : Index (Fin D) (Fin h) H) (f : Fin (h+2)) :
    value ((Pins.field f).eval ((boxPinCodec h hβ hH).encode i)) = (pinWords hβ hH i f).val := by
  rw [Pins.field_value]
  exact congrArg (fun z : Fin (h+2) → VPVNP.BurstRAM.Word pin => (z f).val)
    ((arrayBits (h+2) pin).symm_apply_apply _)

/-- On actual pin words and unsigned tally bits, each selected wire has the
exact value used in the residue coefficient formula. -/
theorem queryBit_value (hβ : D ≤ 2^pin) (hH : 2*H < 2^pin)
    (i j : Index (Fin D) (Fin h) H) (μ : Fin h →₀ ℕ) (δ : J → ℕ)
    (hm : ∀ l, μ l < 2^tally) (hd : ∀ l, δ l < 2^tally) (guess : G → Bool)
    (t : Query (Fin h) idx D J m ⊕ G) :
    let raw := physicalInput (tally := tally) ((boxPinCodec h hβ hH).encode i) ((boxPinCodec h hβ hH).encode j) μ δ
    (queryBit H t).eval (number (Sum.elim raw guess)) 0 =
      Sum.elim (encodeQuery idx H m i.2.val (parameterShift μ) j.2.val i.1 j.1 δ) guess t := by
  intro raw
  rcases t with (⟨tag,l,b⟩ | (⟨side,b⟩ | ⟨k,b⟩)) | g
  · by_cases one : tag = 1
    · rw [queryBit, ite_eq_left one]
      change (offsetNet idx H l).eval (number (Sum.elim raw guess)) b.rev = _
      rw [offset_value H l _ _ _ _ guess hm b.rev]
      cases l <;> simp [ResidueIndex.encode,encodeQuery,one,parameterShift,Fin.rev,Nat.sub_sub,Nat.add_comm]
      congr 1; omega
    · rw [queryBit, ite_eq_right one]
      change ((_ : Net pin).comp (resizeWord pin idx)).eval _ b.rev = _
      rw [resizeBit,eval_comp,pinBits,route_eval]
      by_cases zero : tag = 0
      · have bits : (Sum.elim raw guess ∘ fun k => Sum.inl (Sum.inl (tag != 0,k))) =
            (boxPinCodec h hβ hH).encode i := by funext k; simp [raw,physicalInput,zero]
        rw [bits,pin_field_val hβ hH i]
        cases l <;> simp [encodeQuery,ResidueIndex.encode,zero,pinWords,exponentField,Fin.rev,Nat.sub_sub,Nat.add_comm]
      · have bits : (Sum.elim raw guess ∘ fun k => Sum.inl (Sum.inl (tag != 0,k))) =
            (boxPinCodec h hβ hH).encode j := by funext k; simp [raw,physicalInput,zero]
        rw [bits,pin_field_val hβ hH j]
        cases l <;> simp [encodeQuery,ResidueIndex.encode,zero,one,pinWords,exponentField,Fin.rev,Nat.sub_sub,Nat.add_comm]
  · change ((_ : Net pin).comp (resizeWord pin (Nat.clog 2 D))).eval _ b = _
    rw [resizeBit,eval_comp,pinBits,route_eval]
    cases side <;> simp [raw,physicalInput,Function.comp_def,pin_field_val hβ hH,encodeQuery,
      addressWord, pinWords, -BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
  · change ((_ : Net tally).comp (resizeWord tally m)).eval _ b = _
    rw [resizeBit,tallyBits,route_eval]
    have hv := bitsValue_ofFn (⟨δ k,hd k⟩ : Fin (2^tally))
    rw [show value (Sum.elim raw guess ∘ fun z => Sum.inl (Sum.inr (Sum.inr k,z))) = δ k from hv]
    rfl
  · simp [queryBit,number]

end DiagonalResidueRAM.Board

end BorderVNP
end Computability
end OAI
