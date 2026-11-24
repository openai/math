import OAI.Computability.VPVNP.RAMSerialization
import Mathlib.Data.List.OfFn

/-!
# Reading one RAM word from a bit stream

The private choices for a reported RAM call contain fixed-width read answers.
They use the same least-significant-bit-first encoding as the shared messages.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ}

/-- The `w` consecutive bits of a word, in increasing order of significance. -/
def wordBits (a : Word w) : List Bool := List.ofFn (RAMSerialization.wordBits w a)

@[simp] theorem length_wordBits (a : Word w) : (wordBits a).length = w :=
  List.length_ofFn

private def pushLow (b : Bool) (hi : Word w) : Word (w + 1) :=
  ⟨(finTwoEquiv.symm b).val + 2 * hi.val, by
    have hb := (finTwoEquiv.symm b).isLt
    have hh := hi.isLt
    rw [pow_succ]
    omega⟩

private theorem decode_digits (d : Fin w → Bool) :
    ((RAMSerialization.wordBits w).symm d).val = ∑ i, (finTwoEquiv.symm (d i)).val * 2 ^ i.val :=
  finFunctionFinEquiv_apply _

private theorem decode_cons (b : Bool) (d : Fin w → Bool) :
    (RAMSerialization.wordBits (w + 1)).symm (Fin.cons b d) =
      pushLow b ((RAMSerialization.wordBits w).symm d) := by
  apply Fin.ext
  rw [decode_digits, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.val_zero, pow_zero, mul_one, Fin.cons_succ, Fin.val_succ, pow_succ,
    ← Nat.mul_assoc, ← Finset.sum_mul]
  simp [pushLow, decode_digits, Nat.mul_comm]

private theorem wordBits_pushLow (b : Bool) (hi : Word w) :
    wordBits (pushLow b hi) = b :: wordBits hi := by
  have he := decode_cons b (RAMSerialization.wordBits w hi)
  rw [Equiv.symm_apply_apply] at he
  simp [wordBits, ← he, List.ofFn_succ]

/-- Consume one bit per iteration. Each return computes the word by a single
left shift and the addition of its low bit, without inspecting the suffix. -/
def takeWord : (w : ℕ) → List Bool → Option (Word w × List Bool)
  | 0, xs => some (0, xs)
  | _ + 1, [] => none
  | k + 1, b :: xs => (takeWord k xs).map (fun (a, tail) => (pushLow b a, tail))

private theorem takeWord_sound (xs : List Bool) (a : Word w) (tail : List Bool)
    (h : takeWord w xs = some (a, tail)) : xs = wordBits a ++ tail := by
  induction w generalizing xs with
  | zero =>
    have he : ((0 : Word 0), xs) = (a, tail) := Option.some.inj h
    obtain ⟨_, rfl⟩ := Prod.mk.inj he
    simp [wordBits]
  | succ w ih =>
    cases xs with
    | nil => simp [takeWord] at h
    | cons b xs =>
      simp only [takeWord, Option.map_eq_some_iff] at h
      obtain ⟨⟨hi, ts⟩, hh, he⟩ := h
      cases he
      rw [wordBits_pushLow, List.cons_append, ih _ _ hh]

private theorem takeWord_wordBits (a : Word w) (tail : List Bool) :
    takeWord w (wordBits a ++ tail) = some (a, tail) := by
  induction w with
  | zero =>
    have ha : a = 0 := by
      apply Fin.ext
      have h := a.isLt
      simp at h
      omega
    simp [wordBits, takeWord, ha]
  | succ w ih =>
    let d := RAMSerialization.wordBits (w + 1) a
    have he := decode_cons (d 0) (Fin.tail d)
    rw [Fin.cons_self_tail, Equiv.symm_apply_apply] at he
    rw [he, wordBits_pushLow, List.cons_append, takeWord, ih]
    rfl

theorem takeWord_eq_some_iff (xs : List Bool) (a : Word w) (tail : List Bool) :
    takeWord w xs = some (a, tail) ↔ xs = wordBits a ++ tail :=
  ⟨takeWord_sound xs a tail, fun he => he ▸ takeWord_wordBits a tail⟩

/-- Meter the width test, list dispatch, low-bit conversion, shift and addition.
On a short stream, including when the first missing bit is the last requested
bit, the parser returns within the same bound as on a complete word. -/
def meteredTakeWord : (w : ℕ) → List Bool → Option (Word w × List Bool) × ℕ
  | 0, xs => (some (0, xs), 1)
  | _ + 1, [] => (none, 2)
  | k + 1, b :: xs =>
    let (out, work) := meteredTakeWord k xs
    (out.map (fun (a, tail) => (pushLow b a, tail)), 5 + work)

/-- The metered stream parser realizes the decoder used by local calls. -/
theorem meteredTakeWord_spec (w : ℕ) (xs : List Bool) :
    (meteredTakeWord w xs).1 = takeWord w xs ∧ (meteredTakeWord w xs).2 ≤ 5 * w + 1 := by
  induction w generalizing xs with
  | zero => simp [meteredTakeWord, takeWord]
  | succ k ih =>
    cases xs with
    | nil => simp [meteredTakeWord, takeWord]; omega
    | cons b xs =>
      obtain ⟨ho, hw⟩ := ih xs
      simp only [meteredTakeWord, takeWord, ho, true_and]
      omega

end BurstRAM

end VPVNP
end Computability
end OAI
