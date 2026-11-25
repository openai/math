import OAI.Hierarchy.DescentThinPacks
import OAI.Hierarchy.DescentPackingColors

namespace OAI
/-! # Walsh slabs for the actual ordered stream of old vertex occurrences -/

namespace Hierarchy.DescentPacking
open scoped BigOperators Classical
open DescentWalshTables
noncomputable section
variable {k : ℕ} {U : Type*}

/-- Aggregate precisely the incidences emitted by this block in the old list. -/
def slab (weight : U → ℕ) (address : U → Bits k) (xs : List U) (i : Bits k) : ℕ :=
  amount weight (xs.filter fun x => address x=i)

/-- Filtering keeps all vertices of a block together, even if the ordered
occurrence stream contains several records with the same block address. -/
def side (address : U → Bits k) (a : Bits k) (b : ZMod 2) (zeroSide : Bool) (xs : List U) :=
  xs.filter fun x => decide (binaryRow a (address x)+b=0) == zeroSide

theorem color_slab (weight : U → ℕ) (address : U → Bits k) (a : Bits k) (b : ZMod 2)
    (t : Bool) (xs : List U) :
    amount weight (side address a b t xs)=
      ∑ i : Bits k, if (decide (binaryRow a i+b=0) == t) then slab weight address xs i else 0 := by
  induction xs with
  | nil => simp [side,slab,amount]
  | cons x xs ih =>
    have each (i : Bits k) : slab weight address (x::xs) i=
        (if i=address x then weight x else 0)+slab weight address xs i := by
      by_cases hit : i=address x
      · subst i
        simp [slab,amount]
      · simp [slab,amount,hit,Ne.symm hit]
    let keep (i : Bits k) := decide (binaryRow a i+b=0) == t
    change amount weight (side address a b t (x::xs))=∑ i,if keep i then _ else 0
    have splitAt (i : Bits k) :
        (if keep i then slab weight address (x::xs) i else 0)=
        (if i=address x then (if keep (address x) then weight x else 0) else 0)+
        (if keep i then slab weight address xs i else 0) := by
      by_cases here : i=address x
      · subst i; cases h : keep (address x) <;> simp [each]
      · cases h : keep i <;> simp [each,here]
    simp_rw [splitAt]
    rw [Finset.sum_add_distrib,Fintype.sum_ite_eq']
    change amount weight (side address a b t xs)=∑ i,if keep i then slab weight address xs i else 0 at ih
    rw [←ih]
    cases h : keep (address x) <;>
      simp [side,amount,keep] at h ⊢ <;> simp_all

theorem slab_total (weight : U → ℕ) (address : U → Bits k) (xs : List U) :
    (∑ i : Bits k,slab weight address xs i)=amount weight xs := by
  induction xs with
  | nil => simp [slab,amount]
  | cons x xs ih =>
    have each (i : Bits k) : slab weight address (x::xs) i=
        (if i=address x then weight x else 0)+slab weight address xs i := by
      by_cases hit : i=address x
      · subst i
        simp [slab,amount]
      · simp [slab,amount,hit,Ne.symm hit]
    simp only [each,Finset.sum_add_distrib,Fintype.sum_ite_eq',ih]
    rfl

end
end Hierarchy.DescentPacking

end OAI
