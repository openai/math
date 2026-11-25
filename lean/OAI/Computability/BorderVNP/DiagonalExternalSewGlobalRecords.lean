import OAI.Computability.BorderVNP.DiagonalExternalSewPhysicalVolume

/-! # Total number of live exterior cable descriptors

The half-open address ranges of all processors fit inside the initial site
blocks. Counting the records in each block counts every occupied interval
twice, once at each of its ordered ends.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Finset
open scoped Classical

variable {R r : ℕ} (literal stride link g : ℕ)

/-- The site block of each stored end exists inside the public array of sites. -/
theorem fieldBlock_lt (V : ℕ) (hg : 0 < g) (fit : literal + R*link ≤ stride) (room : r*stride ≤ V*g)
    (c : Pieces (fieldStart (R := R) (r := r) literal stride link) g link) (a : Bool) :
    (fieldBlock literal stride link g c a).2 < V := by
  let j : Fin (pieceWidth _ _ c) := ⟨0,pieceWidth_pos _ _ c⟩
  rw [fieldBlock_bit literal stride link g c a j]
  apply (Nat.div_lt_iff_lt_mul hg).mpr
  have h₁ := Nat.mul_le_mul_right link (Nat.succ_le_of_lt (fieldRank c.1.1 a).isLt)
  have h₂ := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt c.1.2.isLt)
  have h₃ := (pieceOffset _ _ c j).isLt
  rw [Nat.succ_mul] at h₁ h₂
  omega

/-- The true number of occupied cable intervals is at most twice the total
number of initial sites across the teams. -/
theorem physical_pieces_le (V : ℕ) (hg : 0 < g) (small : g ≤ link) (fit : literal + R*link ≤ stride)
    (room : r*stride ≤ V*g) :
    Fintype.card (Pieces (fieldStart (R := R) (r := r) literal stride link) g link) ≤ 2*((R+1)*V) := by
  let C := Pieces (fieldStart (R := R) (r := r) literal stride link) g link
  let addr (x : Bool × C) := fieldBlock literal stride link g x.2 x.1
  let loc (x : Bool × C) : Fin (R+1) × Fin V :=
    ((addr x).1,⟨(addr x).2,fieldBlock_lt _ _ _ _ V hg fit room x.2 x.1⟩)
  have iff (x : Bool × C) (y : Fin (R+1) × Fin V) : loc x = y ↔ addr x = (y.1,y.2.val) := by
    constructor
    · rintro rfl; rfl
    · intro h
      have ht := congrArg Prod.fst h
      have hs := congrArg Prod.snd h
      exact Prod.ext ht (Fin.ext hs)
  have hs (y : Fin (R+1) × Fin V) : (univ.filter fun x => loc x = y).card ≤ 4 := by
    simp only [iff]
    exact physical_ends_per_block (r := r) literal stride link g (by omega) hg small y.1 y.2.val
  have h : (∑ y : Fin (R+1) × Fin V, (univ.filter fun x => loc x = y).card) = 2*Fintype.card C := by
    simpa using sum_card_fiberwise_eq_card_filter (univ : Finset (Bool × C)) univ loc
  have hz := sum_le_sum fun y (_ : y ∈ univ) => hs y
  rw [h] at hz
  simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hz
  change Fintype.card C ≤ _
  omega

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
