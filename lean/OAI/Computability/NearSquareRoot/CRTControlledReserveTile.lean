import OAI.Computability.NearSquareRoot.CRTControlledReserveMiddle
import OAI.Computability.NearSquareRoot.CRTPositionChunkView

/-! # Realizing a middle-address permutation between two fixed fields -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveTile
open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Strip

variable {k lo hi : ℕ} (fit : lo + hi ≤ k)

/-- The high and low fields remain in physical order around the middle word. -/
def view :
    Adopt ((line 2 hi).cart ((line 2 (k - lo - hi)).cart (line 2 lo))) (line 2 k) :=
  ((Adopt.same _).split (prefixView (p := k - lo - hi) (n := lo) rfl)).thenDo
    (prefixView (by omega))

/-- The middle address permutation lifted through the physical packing. -/
def lift (e : Equiv.Perm (Block 2 (k - lo - hi))) : Equiv.Perm (Block 2 k) :=
  (view fit).cast.symm.trans
    (((Equiv.refl _).prodCongr (e.prodCongr (Equiv.refl _))).trans (view fit).cast)

theorem lift_view (e : Equiv.Perm (Block 2 (k - lo - hi))) (a : Block 2 hi)
    (b : Block 2 (k - lo - hi)) (c : Block 2 lo) :
    lift fit e ((view fit).cast (a, b, c)) = (view fit).cast (a, e b, c) := by
  simp [lift]

/-- The physical address of a bit in the low field. -/
abbrev lowPort (j : Fin lo) : Fin k := ⟨j.val, by have := j.isLt; omega⟩

/-- The physical address of a bit in the high field. -/
abbrev highPort (j : Fin hi) : Fin k := ⟨(k - lo - hi + lo) + j.val,
  by have := j.isLt; omega⟩

variable (a : Block 2 hi) (b : Block 2 (k - lo - hi)) (c : Block 2 lo)

theorem low_bit (j : Fin lo) :
    prefixBit ((view fit).cast (a, b, c)) (lowPort fit j) = prefixBit c j := by
  let v := prefixView (p := k - lo - hi) (n := lo) rfl
  have size : hi + (k - lo - hi + lo) = k := by omega
  exact (lowPrefixBit size a (v.cast (b, c)) ⟨j.val, by have := j.isLt; omega⟩).trans
    (lowPrefixBit rfl b c j)

theorem middle_bit (j : Fin (k - lo - hi)) :
    prefixBit ((view fit).cast (a, b, c)) (ReserveMiddle.embed k lo hi j) = prefixBit b j := by
  let v := prefixView (p := k - lo - hi) (n := lo) rfl
  have size : hi + (k - lo - hi + lo) = k := by omega
  exact (lowPrefixBit size a (v.cast (b, c)) ⟨lo + j.val, by have := j.isLt; omega⟩).trans
    (highPrefixBit rfl b c j)

theorem high_bit (j : Fin hi) :
    prefixBit ((view fit).cast (a, b, c)) (highPort fit j) = prefixBit a j := by
  have size : hi + (k - lo - hi + lo) = k := by omega
  exact highPrefixBit size a ((prefixView (p := k - lo - hi) (n := lo) rfl).cast (b, c)) j

/-- A little-endian position in the middle reads through its local map. Every
reserved high and low position reads its own original bit. -/
theorem lift_prefixBit (e : Equiv.Perm (Block 2 (k - lo - hi)))
    (m : Equiv.Perm (Fin (k - lo - hi)))
    (h : ∀ y j, prefixBit (e y) j = prefixBit y (m j)) (y : Block 2 k) (j : Fin k) :
    prefixBit (lift fit e y) j = prefixBit y (ReserveMiddle.extend lo hi m j) := by
  obtain ⟨⟨a, b, c⟩, rfl⟩ := (view fit).cast.surjective y
  rw [lift_view]
  unfold ReserveMiddle.extend
  split_ifs with inside
  · let t : Fin (k - lo - hi) := ⟨j.val - lo, by omega⟩
    have hj : j = ReserveMiddle.embed k lo hi t := by
      apply Fin.ext
      change j.val = lo + (j.val - lo)
      omega
    change _ = prefixBit _ (ReserveMiddle.embed k lo hi (m t))
    rw [middle_bit, hj, middle_bit, h]
  · by_cases low : j.val < lo
    · let t : Fin lo := ⟨j.val, low⟩
      have hj : j = lowPort fit t := rfl
      rw [hj, low_bit, low_bit]
    · let t : Fin hi := ⟨j.val - (k - hi), by have := j.isLt; omega⟩
      have hj : j = highPort fit t := by
        apply Fin.ext
        change j.val = (k - lo - hi + lo) + (j.val - (k - hi))
        omega
      rw [hj, high_bit, high_bit]

end Controlled.ReserveTile

end NearSquareRoot
end Computability
end OAI
