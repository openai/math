import OAI.Computability.BorderVNP.RoutingISACompactDecode
import OAI.Computability.BorderVNP.TeamPrivateCall
import OAI.Computability.QuantumFactoring.BitEncoding

/-! # Word packing for the compact private cell input

The outer team stores the generator descriptor as little-endian machine words.
A presence bit precedes each payload digit. A zero terminator ends the descriptor,
and the last word is padded with zeros up to the machine width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactFrame

open VPVNP.BurstRAM ExactQuantumFactoring

private theorem frame_length (bs : List Bool) :
    (frameBits bs).length = 2 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [frameBits, CellMacro.FieldDecoder.frame] at ih ⊢; omega

/-- Number of physical words occupied by the terminated, padded input descriptor. -/
def wordCount (w : ℕ) (payload : List Bool) := (2*payload.length+1+w-1)/w

/-- Unused bits in the final word of the packed descriptor. -/
def padding (w : ℕ) (payload : List Bool) := wordCount w payload * w - (2*payload.length+1)

private theorem room {w : ℕ} (hw : 0 < w) (payload : List Bool) :
    2*payload.length+1 ≤ wordCount w payload * w ∧
      wordCount w payload * w < 2*payload.length+1+w := by
  let l := 2*payload.length+1
  have h := Nat.div_add_mod (l+w-1) w
  rw [Nat.mul_comm] at h
  have hmod := Nat.mod_lt (l+w-1) hw
  change l ≤ (l+w-1)/w*w ∧ (l+w-1)/w*w < l+w
  omega

/-- The canonical packing uses fewer than one word of zero padding. -/
theorem padding_lt {w : ℕ} (hw : 0 < w) (payload : List Bool) : padding w payload < w := by
  have h := room hw payload
  unfold padding
  omega

private def firstWord (w : ℕ) (bs : List Bool) : Word w :=
  (bitsValue (fun j : Fin w => bs[j.val]?.getD false)).toFin

private def blocks (w : ℕ) : ℕ → List Bool → List (Word w)
  | 0, _ => []
  | n+1, bs => firstWord w bs :: blocks w n (bs.drop w)

private theorem length_blocks (w n : ℕ) (bs : List Bool) : (blocks w n bs).length = n := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => simp [blocks,ih]

private theorem firstWord_bits (w : ℕ) (bs : List Bool) (hw : w ≤ bs.length) :
    List.ofFn (fun j : Fin w => (firstWord w bs).val.testBit j.val) = bs.take w := by
  have val (j : Fin w) : (firstWord w bs).val.testBit j.val = bs[j.val]?.getD false := bitsValue_bit _ j
  apply List.ext_getElem
  · simp [Nat.min_eq_left hw]
  · intro j h₁ _
    have hj : j < w := by simpa using h₁
    simp [val, List.getElem?_eq_getElem (hj.trans_le hw)]

private theorem unpack_blocks (w n : ℕ) (bs : List Bool) (fit : bs.length = n*w) :
    TeamPrivateCall.inputBits (blocks w n bs) = bs := by
  induction n generalizing bs with
  | zero =>
    have h : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using fit)
    subst bs
    rfl
  | succ n ih =>
    rw [Nat.succ_mul] at fit
    change List.ofFn (fun j : Fin w => (firstWord w bs).val.testBit j.val) ++
      TeamPrivateCall.inputBits (blocks w n (bs.drop w)) = bs
    rw [firstWord_bits w bs (by omega), ih _ (by simp [fit]), List.take_append_drop]

/-- Store the framed payload in consecutive words with the least significant bit first. -/
def pack (w : ℕ) (payload : List Bool) : List (Word w) :=
  blocks w (wordCount w payload) (frameBits payload ++ List.replicate (padding w payload) false)

/-- The physical read interval uses exactly the ceiling of the framed bit length divided by width. -/
theorem length_pack (w : ℕ) (payload : List Bool) :
    (pack w payload).length = (2*payload.length+1+w-1)/w := length_blocks ..

/-- The genuine private input operation recovers every prefix marker, digit and padding bit. -/
theorem inputBits_pack {w : ℕ} (hw : 0 < w) (payload : List Bool) :
    TeamPrivateCall.inputBits (pack w payload) =
      frameBits payload ++ List.replicate (padding w payload) false := by
  apply unpack_blocks
  simp only [List.length_append, List.length_replicate, frame_length, padding]
  have h := (room hw payload).1
  omega

/-- On the actual word burst the fixed parser consumes the input, leaves the ordered
payload in the destination, and takes at most three steps per input bit. -/
theorem decode_packed {K : Type} [DecidableEq K] {src dst : K} (different : src ≠ dst)
    {w : ℕ} (hw : 0 < w) (payload : List Bool) (s : VPVNP.RAMTape.Stacks K)
    (input : s src = TeamPrivateCall.inputBits (pack w payload)) (empty : s dst = []) :
    ∃ t ≤ 3*((pack w payload).length*w), (decode src dst).Runs t s
      (Function.update (Function.update s src []) dst payload) := by
  refine ⟨_,?_,decode_run different payload (padding w payload) s (input.trans (inputBits_pack hw payload)) empty⟩
  have n := TeamPrivateCall.inputBits_length (pack w payload)
  rw [inputBits_pack hw, List.length_append, frame_length, List.length_replicate] at n
  omega

end RoutingISA.CompactFrame

end BorderVNP
end Computability
end OAI
