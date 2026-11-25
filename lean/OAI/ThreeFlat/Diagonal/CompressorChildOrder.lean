import OAI.ThreeFlat.Diagonal.CompressorOwnerRows
import OAI.ThreeFlat.Diagonal.CompressorBundleCounts
import OAI.ThreeFlat.Diagonal.CompressorWordEncoding
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Equal-size child lists in chronological old-site order

The ordinal indexes a polarity, a port, and the remaining color bits.
The color of the old base fixes the erased bit in each such block.
-/
namespace ThreeFlat.Diagonal.CompressorPacking.Owner
open Computability.VPVNP.Compression
variable {V H Tag L : Type*} {c d : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d (c+1)) (lay : Bool) (v : Site V Tag L)

abbrev freeWords (thin : Bool) (i : Fin d) := {u : BitWord (c+1) // valid P lay v (thin,i,u)}
def chosenColor (thin : Bool) (i : Fin d) := P.color (child P lay v (thin,i,0)).1.1

omit [AddCommGroup H] in
theorem valid_bit (thin : Bool) (i : Fin d) (u : BitWord (c+1)) :
    valid P lay v (thin,i,u) ↔ u (chosenColor P lay v thin i) = (if thin then 0 else 1) := by
  cases thin with
  | false => rfl
  | true =>
    change (u (chosenColor P lay v true i) ≠ 1) ↔ u (chosenColor P lay v true i) = 0
    exact (by decide : ∀ x : Fin 2, x ≠ 1 ↔ x = 0) _

/-- Delete the constrained color, keeping the remaining bits in increasing order. -/
def freeOrdinal (thin : Bool) (i : Fin d) : freeWords P lay v thin i ≃ Fin (2^c) :=
  let p := chosenColor P lay v thin i
  let eqv : freeWords P lay v thin i ≃ {u : BitWord (c+1) // u p = (if thin then 0 else 1)} :=
    Equiv.subtypeEquivRight (valid_bit P lay v thin i)
  eqv.trans ((eraseColor p _).trans (((finSuccAboveEquiv p).symm.arrowCongr (Equiv.refl _)).trans
    (Native.tagOrdinal c)))

def groupedIndex : {a : Index d (c+1) // valid P lay v a} ≃
    (Σ b : Bool × Fin d, freeWords P lay v b.1 b.2) where
  toFun a := ⟨(a.val.1,a.val.2.1),a.val.2.2,a.property⟩
  invFun a := ⟨(a.1.1,a.1.2,a.2.val),a.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def indexOrder : {a : Index d (c+1) // valid P lay v a} ≃ Fin (d*2^(c+1)) :=
  (groupedIndex P lay v).trans ((Equiv.sigmaEquivProdOfEquiv (fun b => freeOrdinal P lay v b.1 b.2)).trans
    (((((finTwoEquiv.symm.prodCongr (Equiv.refl (Fin d))).trans finProdFinEquiv).prodCongr
      (Equiv.refl (Fin (2^c)))).trans finProdFinEquiv).trans (finCongr (by rw [pow_succ]; ring))))

def childOrder : Fin (d*2^(c+1)) ≃ {x // P.placement lay x = v} :=
  (indexOrder P lay v).symm.trans (children P lay v)

end ThreeFlat.Diagonal.CompressorPacking.Owner

end OAI
