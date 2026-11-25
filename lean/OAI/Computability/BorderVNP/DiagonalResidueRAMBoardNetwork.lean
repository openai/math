import OAI.Computability.BorderVNP.DiagonalResidueRAMBoard

/-!
# The complete padded-pin query preprocessor

One advised Boolean network takes the actual two pin fields and the unsigned
team subtotals. Invalid pins produce zero. Valid pins select the exact joint
input of the field verifier, including a multiword addition of the advised
box radius.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM.Board

open Diagonal ResidueEntryInput ResidueEntryField ResiduePins ExactQuantumFactoring BooleanNetwork BitArithmetic
open scoped Classical

variable {h pin tally idx m D H : ℕ} {J G : Type*} [Fintype J] [Fintype G]

local notation "Source" => Physical h pin tally J ⊕ G
local notation "Target" => Query (Fin h) idx D J m ⊕ G

/-- All joint input pins, numbered exactly as in the chart verifier. -/
noncomputable def inputNet (H : ℕ) : BooleanNetwork (Fintype.card Source) (Fintype.card Target) :=
  vector (fun i => queryBit H ((Fintype.equivFin Target).symm i))

/-- Reject each invalid padded pin, and otherwise run the field verifier on
the prepared input. -/
noncomputable def guarded (H : ℕ) (N : BooleanNetwork (Fintype.card Target) 1) :
    BooleanNetwork (Fintype.card Source) 1 :=
  (((pinBits false).comp (Pins.guard h pin D H)).band ((pinBits true).comp (Pins.guard h pin D H))).band
    ((inputNet H).comp N)

/-- All preprocessed input bits, including the private guesses, agree with the
joint verifier input on a valid pin pair. -/
theorem inputNet_value (hβ : D ≤ 2^pin) (hH : 2*H < 2^pin)
    (i j : Index (Fin D) (Fin h) H) (μ : Fin h →₀ ℕ) (δ : J → ℕ)
    (hm : ∀ l, μ l < 2^tally) (hd : ∀ l, δ l < 2^tally) (guess : G → Bool) :
    let raw := physicalInput (tally := tally) ((boxPinCodec h hβ hH).encode i) ((boxPinCodec h hβ hH).encode j) μ δ
    (inputNet (idx := idx) (m := m) H).eval (number (Sum.elim raw guess)) =
      number (Sum.elim (encodeQuery idx H m i.2.val (parameterShift μ) j.2.val i.1 j.1 δ) guess) := by
  intro raw
  funext t
  rw [inputNet,eval_vector]
  exact queryBit_value hβ hH i j μ δ hm hd guess _

private theorem sideBits (side : Bool) (row col : Fin ((h+2)*pin) → Bool)
    (μ : Fin h → ℕ) (δ : J → ℕ) (guess : G → Bool) :
    (pinBits side).eval (number (Sum.elim (physicalInput (tally := tally) row col μ δ) guess)) =
      if side then col else row := by
  rw [pinBits,route_eval]
  cases side <;> rfl

/-- Full semantics on every pair of raw external pins, including out-of-box
words. The offsets and basis addresses come from the actual decoded indices. -/
theorem guarded_eval (hβ : D ≤ 2^pin) (hH : 2*H < 2^pin) (N : BooleanNetwork (Fintype.card Target) 1)
    (row col : Fin ((h+2)*pin) → Bool) (μ : Fin h →₀ ℕ) (δ : J → ℕ)
    (hm : ∀ l, μ l < 2^tally) (hd : ∀ l, δ l < 2^tally) (guess : G → Bool) :
    let codec := boxPinCodec h hβ hH
    let raw := physicalInput (tally := tally) row col μ δ
    (guarded H N).eval (number (Sum.elim raw guess)) 0 =
      (codec.decode row).elim false fun i => (codec.decode col).elim false fun j =>
        N.eval (number (Sum.elim (encodeQuery idx H m i.2.val (parameterShift μ) j.2.val i.1 j.1 δ) guess)) 0 := by
  intro codec raw
  simp only [guarded, eval_band, eval_comp]
  rw [show (pinBits false).eval (number (Sum.elim raw guess)) = row from sideBits false row col μ δ guess,
      show (pinBits true).eval (number (Sum.elim raw guess)) = col from sideBits true row col μ δ guess]
  have check (b : Fin ((h+2)*pin) → Bool) : (Pins.guard h pin D H).eval b 0 = (codec.decode b).isSome :=
    Bool.eq_iff_iff.mpr (Pins.guard_correct hβ hH b)
  rw [check,check]
  cases hr : codec.decode row with
  | none => rfl
  | some i =>
    cases hc : codec.decode col with
    | none => rfl
    | some j =>
      obtain rfl := (codec.decode_eq_some row i).mp hr
      obtain rfl := (codec.decode_eq_some col j).mp hc
      rw [inputNet_value hβ hH i j μ δ hm hd guess]
      rfl

/-- A single output pin needs at most one width-indexed addition and two width
conversions. Constant zero, source selection and endianness use no extra gates. -/
theorem queryBit_count (H : ℕ) (t : Target) :
    ((queryBit H t : BooleanNetwork (Fintype.card Source) 1).net.count) ≤
      100*(idx+m+Nat.clog 2 D+1) := by
  have off (i : Option (Fin h)) :
      ((offsetNet idx H i : BooleanNetwork (Fintype.card Source) idx).net.count) ≤ 88*idx+6 := by
    cases i with
    | none => simp [offsetNet,literal,wordConstant_count]; omega
    | some j =>
      have hw := resizeWord_count tally idx
      have hAdd := add_count idx
      simp only [offsetNet,count_comp,count_pair,tallyBits,route_count,literal,wordConstant_count]
      omega
  rcases t with (⟨tag,i,j⟩ | (⟨side,j⟩ | ⟨l,j⟩)) | g
  · by_cases one : tag = 1
    · rw [queryBit,ite_eq_left one]
      simp only [pick,count_rewire]
      exact (off i).trans (by omega)
    · rw [queryBit,ite_eq_right one]
      simp only [pick,count_rewire, count_comp, pinBits,route_count, Pins.field,count_select]
      have := resizeWord_count pin idx
      omega
  · simp only [queryBit,pick,count_rewire,count_comp,pinBits,route_count,Pins.field,count_select]
    have := resizeWord_count pin (Nat.clog 2 D)
    omega
  · simp only [queryBit,pick,count_rewire,count_comp,tallyBits,route_count]
    have := resizeWord_count tally m
    omega
  · simp [queryBit]

/-- The physical-board preprocessing and both range guards have an explicit
polynomial budget, with one occurrence of the shared chart verifier. -/
theorem guarded_count (H : ℕ) (N : BooleanNetwork (Fintype.card Target) 1) :
    ((guarded H N : BooleanNetwork (Fintype.card Source) 1).net.count) ≤
      N.net.count + Fintype.card Target*(100*(idx+m+Nat.clog 2 D+1)) +
        2*((h+3)*(100*pin+25)) + 2 := by
  have hin := count_vector_le
    (fun t => (queryBit H ((Fintype.equivFin Target).symm t) : BooleanNetwork (Fintype.card Source) 1))
    (fun t => queryBit_count H ((Fintype.equivFin Target).symm t))
  have hguard := Pins.guard_count h pin D H
  simp only [guarded,inputNet,count_band,count_comp,pinBits,route_count]
  omega

end DiagonalResidueRAM.Board

end BorderVNP
end Computability
end OAI
