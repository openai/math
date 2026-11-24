import OAI.Computability.VPVNP.LiveExponentSweep

/-!
# The exponent stage on the paper's serialized cut buffers

The addresses are three disjoint flat arrays. The input and output buffers
contain the little-endian serialization of their exponent words. Processing
a label clears that label's counter word and leaves every other label's
initial increment available for its own row of calls.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveExponent

open BurstRAM RAMSerialization
open scoped Classical Fin.CommRing

variable {w t Z : ℕ}

/-- Address of the increment word for a label. -/
def counterAddr (pub : Fin 5 → Word w) (a : Fin t) : Word w := pub 2 + Fin.ofNat _ a.val

/-- Encode the flattened address offset of a given label and exponent digit. -/
def posWord (a : Fin t) (j : Fin Z) : Word w := Fin.ofNat _ (a.val * Z + j.val)

/-- Data and address contract of the stage after the header and pair phases. -/
structure BufferLayout (pub : Fin 5 → Word w) (t Z : ℕ) : Prop where
  width : (pub 3).val = Z
  size : (pub 4).val = t*Z
  incoming_disjoint : ∀ (a b : Fin t) (j : Fin Z), incomingAddress pub (posWord a j) ≠ counterAddr pub b
  outgoing_disjoint : ∀ (a b : Fin t) (j : Fin Z), outgoingAddress pub (posWord a j) ≠ counterAddr pub b

/-- The actual little-endian word arrays produced by the header scan. -/
structure BufferValues (pub : Fin 5 → Word w) (x y : Fin t → Word Z) (m : Memory w) : Prop where
  incoming : ∀ a j, (m (incomingAddress pub (posWord a j)).val).val = (wordBits Z (x a) j).toNat
  outgoing : ∀ a j, (m (outgoingAddress pub (posWord a j)).val).val = (wordBits Z (y a) j).toNat

/-- Clearing a completed carry preserves both read-only arrays. -/
theorem BufferValues.write_counter {pub : Fin 5 → Word w} (L : BufferLayout pub t Z)
    {x y : Fin t → Word Z} {m : Memory w} (v : BufferValues pub x y m) (b : Fin t) (c : Word w) :
    BufferValues pub x y (writeMemory m (counterAddr pub b) c) := by
  constructor <;> intro a j
  · rw [writeMemory, ite_eq_right (fun e => L.incoming_disjoint a b j (Fin.ext e))]
    exact v.incoming a j
  · rw [writeMemory, ite_eq_right (fun e => L.outgoing_disjoint a b j (Fin.ext e))]
    exact v.outgoing a j

private theorem pos_lt (a : Fin t) (j : Fin Z) : a.val*Z+j.val < t*Z := by
  calc
    a.val*Z+j.val < a.val*Z+Z := Nat.add_lt_add_left j.isLt _
    _ = (a.val+1)*Z := (Nat.succ_mul ..).symm
    _ ≤ t*Z := Nat.mul_le_mul_right _ a.isLt

theorem counterAddr_injective {pub : Fin 5 → Word w} (L : BufferLayout pub t Z) (hZ : 0 < Z) :
    Function.Injective (counterAddr (t := t) pub) := by
  intro a b he
  have hab : (Fin.ofNat (2^w) a.val : Word w) = Fin.ofNat (2^w) b.val :=
    add_left_cancel (show pub 2 + _ = pub 2 + _ from he)
  have ht : t ≤ t*Z := Nat.le_mul_of_pos_right t hZ
  have hcap : t*Z < 2^w := L.size ▸ (pub 4).isLt
  apply Fin.ext
  exact (Nat.mod_eq_of_lt ((a.isLt.trans_le ht).trans hcap)).symm.trans
    ((congrArg Fin.val hab).trans (Nat.mod_eq_of_lt ((b.isLt.trans_le ht).trans hcap)))

/-- One row of the digit scan in its physical order. -/
def wordRow (x y : Word Z) : List (Bool × Bool) := List.ofFn fun j => (wordBits Z x j, wordBits Z y j)

@[simp] theorem wordRow_length (x y : Word Z) : (wordRow x y).length = Z := List.length_ofFn

theorem wordRow_checks (x y : Word Z) (c : ℕ) :
    Checks c ((wordRow x y).map Prod.fst) ((wordRow x y).map Prod.snd) ↔ y.val = x.val+c := by
  simpa [wordRow, List.map_ofFn, BurstRAM.wordBits, Function.comp_def] using checks_words c x y

theorem BufferValues.rowCells {pub : Fin 5 → Word w} (L : BufferLayout pub t Z) (hZ : 0 < Z)
    {x y : Fin t → Word Z} {m : Memory w} (v : BufferValues pub x y m) (a : Fin t) :
    RowCells pub (counterAddr pub a) (a.val*Z) (wordRow (x a) (y a)) m := by
  constructor
  · rw [wordRow_length, ← Nat.succ_mul, L.size]
    exact Nat.mul_le_mul_right _ a.isLt
  · intro j hj
    have hjZ : j < Z := by simpa using hj
    let k : Fin Z := ⟨j,hjZ⟩
    have hpos : (posWord (w := w) a k).val = a.val*Z+j :=
      Nat.mod_eq_of_lt ((pos_lt a k).trans (L.size ▸ (pub 4).isLt))
    have hcarry : carryAddress pub (posWord a k) = counterAddr pub a := by
      unfold carryAddress counterAddr
      congr 1
      change Fin.ofNat _ ((posWord (w := w) a k).val / (pub 3).val) = _
      rw [hpos, L.width, Nat.mul_comm a.val Z, Nat.mul_add_div hZ, Nat.div_eq_of_lt hjZ, Nat.add_zero]
    refine ⟨hcarry,L.incoming_disjoint a a k,L.outgoing_disjoint a a k,?_,?_,?_⟩
    · simpa [wordRow, k, posWord, atPos] using v.incoming a k
    · simpa [wordRow, k, posWord, atPos] using v.outgoing a k
    · simp [L.width, Nat.mul_comm a.val Z, Nat.mod_eq_of_lt hjZ]

/-- Full native row specification on the actual serialized buffers. -/
theorem run_wordRow {pub : Fin 5 → Word w} (L : BufferLayout pub t Z) (hZ : 0 < Z) (hw : 2 ≤ w)
    {x y : Fin t → Word Z} {m : Memory w} (v : BufferValues pub x y m) (a : Fin t)
    (hc : (m (counterAddr pub a).val).val + 1 < 2^w)
    (bits : List (List Bool)) (hlen : bits.length = Z) (tail : List (List Bool)) (f : ℕ) :
    let P := (digitTemplate.instantiate w pub).program
    runSegment P (f+31) (some (Fin.ofNat _ (a.val*Z))) m (bits ++ tail) =
      if (y a).val = (x a).val + (m (counterAddr pub a).val).val ∧ bits = List.replicate Z [] then
        (runSegment P (f+31) (some (Fin.ofNat _ ((a.val+1)*Z))) (writeMemory m (counterAddr pub a) 0)
          tail).map (rowReports pub Z (a.val*Z) m ++ ·)
      else none := by
  have hn : wordRow (x a) (y a) ≠ [] := by
    intro hn
    have he := congrArg List.length hn
    simp at he
    omega
  have he := run_row hw (L.width ▸ hZ) (v.rowCells L hZ a) hc hn bits (by simpa using hlen) tail f
  rw [wordRow_checks, wordRow_length, ← Nat.succ_mul] at he
  by_cases hgood : (y a).val = (x a).val + (m (counterAddr pub a).val).val ∧ bits = List.replicate Z []
  · simpa only [hgood, ite_true, atPos, Nat.succ_eq_add_one] using he
  · simpa only [hgood, ite_false, atPos, Nat.succ_eq_add_one] using he

end LiveExponent

end VPVNP
end Computability
end OAI
