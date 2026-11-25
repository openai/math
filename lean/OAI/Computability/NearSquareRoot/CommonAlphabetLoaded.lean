import OAI.Computability.NearSquareRoot.CommonAlphabetLayout

/-! # Whole-tape semantics of fixed-width symbol blocks

Absolute integer coordinates split into a source address and a physical
offset. A blank-preserving code agrees on both infinite blank tails of a
loaded tape as well as on the finite interval containing its data.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Code

open IntegerMultiplication

variable {A : Type} (c : Code A)

/-- Offset of a physical cell within its block, including for negative coordinates. -/
def offset (z : ℤ) : Fin c.width :=
  let wpos : 0 < (c.width : ℤ) := by exact_mod_cast c.pos
  ⟨(z % (c.width : ℤ)).toNat, (Int.toNat_lt (Int.emod_nonneg _ wpos.ne')).mpr (Int.emod_lt_of_pos _ wpos)⟩

theorem block_coordinate (z : ℤ) :
    z / (c.width : ℤ) * c.width + ((c.offset z).val : ℤ) = z := by
  have hw : 0 < (c.width : ℤ) := by exact_mod_cast c.pos
  rw [offset, Int.toNat_of_nonneg (Int.emod_nonneg _ hw.ne'), Int.ediv_mul_add_emod]

private theorem absolute_loaded_nat {B : Type} (blank : B) (xs : List B) (n : ℕ) :
    (TM.Tape.loaded blank xs).absolute (n : ℤ) = xs[n]?.getD blank := by
  simp [TM.Tape.loaded, TM.Tape.absolute]

private theorem absolute_loaded_neg {B : Type} (blank : B) (xs : List B) (z : ℤ) (hz : z < 0) :
    (TM.Tape.loaded blank xs).absolute z = blank := by
  cases z with
  | ofNat n => exact False.elim ((Int.not_lt.mpr (Int.natCast_nonneg n)) hz)
  | negSucc => rfl

/-- One cell of a loaded physical tape represents the corresponding block
digit of the loaded source tape, even outside the input interval. -/
theorem loaded_absolute_block (blank : A) (hb : c.enc blank = fun _ => none)
    (xs : List A) (q : ℤ) (j : Fin c.width) :
    (TM.Tape.loaded none (c.encodeList xs)).absolute (q * c.width + j.val) =
      c.enc ((TM.Tape.loaded blank xs).absolute q) j := by
  cases q with
  | ofNat n =>
    change (TM.Tape.loaded _ _).absolute ((n : ℤ) * (c.width : ℤ) + j.val) =
      c.enc ((TM.Tape.loaded blank xs).absolute (n : ℤ)) j
    rw [← Nat.cast_mul, ← Nat.cast_add, absolute_loaded_nat, absolute_loaded_nat]
    by_cases hn : n < xs.length
    · rw [c.getElem?_encodeList xs n hn, List.getElem?_eq_getElem hn]
      rfl
    · have hge : xs.length ≤ n := Nat.le_of_not_gt hn
      have hl : (c.encodeList xs).length ≤ n * c.width + j.val := by
        rw [c.length_encodeList]
        exact (Nat.mul_le_mul_right _ hge).trans (Nat.le_add_right ..)
      rw [List.getElem?_eq_none hl, List.getElem?_eq_none hge]
      exact (congrFun hb j).symm
  | negSucc n =>
    have hq : Int.negSucc n ≤ -1 := by omega
    have hw : 0 ≤ (c.width : ℤ) := by positivity
    have hj : (j.val : ℤ) < c.width := by exact_mod_cast j.isLt
    have hz : Int.negSucc n * c.width + j.val < 0 := by
      have hm := mul_le_mul_of_nonneg_right hq hw
      linarith
    rw [absolute_loaded_neg _ _ _ hz, absolute_loaded_neg _ _ _ (Int.negSucc_lt_zero n), hb]

/-- Equivalent absolute-coordinate form of the block representation. -/
theorem loaded_absolute (blank : A) (hb : c.enc blank = fun _ => none)
    (xs : List A) (z : ℤ) :
    (TM.Tape.loaded none (c.encodeList xs)).absolute z =
      c.enc ((TM.Tape.loaded blank xs).absolute (z / (c.width : ℤ))) (c.offset z) := by
  simpa only [c.block_coordinate z] using
    c.loaded_absolute_block blank hb xs (z / (c.width : ℤ)) (c.offset z)

/-- The aligned heads and the contents of the two fully loaded tapes agree. -/
theorem represents_loaded (blank : A) (hb : c.enc blank = fun _ => none) (xs : List A) :
    Represents c (TM.Tape.loaded none (c.encodeList xs)) (TM.Tape.loaded blank xs) :=
  ⟨by simp [TM.Tape.loaded], c.loaded_absolute_block blank hb xs⟩

/-- Exact output including all the physical blanks follows from the virtual
whole-output property and the representation of the destination tape. -/
theorem whole_of_represents (blank : A) (hb : c.enc blank = fun _ => none)
    {xs : List A} {T : TM.Tape A} {S : TM.Tape (Option Bool)}
    (ht : TM.whole blank xs T) (hs : Represents c S T) :
    TM.whole none (c.encodeList xs) S := by
  funext z
  have h := hs.2 (z / c.width) (c.offset z)
  rw [c.block_coordinate, congrFun ht] at h
  exact h.trans (c.loaded_absolute blank hb xs z).symm

end CommonAlphabet.Code

end NearSquareRoot
end Computability
end OAI
