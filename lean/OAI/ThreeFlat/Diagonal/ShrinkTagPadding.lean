import OAI.ThreeFlat.Diagonal.ShrinkGraph
import OAI.ThreeFlat.Diagonal.CompressorWordEncoding

namespace OAI
/-! # Binary form of the adjacent-tag padding permutation -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native

open Computability.VPVNP.Compression
variable {V L : Type} [AddCommGroup L] {n t : ℕ}

def adjacentMask (ht : 1 < 2^t) : BitWord t := (tagOrdinal t).symm ⟨1,ht⟩

theorem adjacent_ne (ht : 1<2^t) : adjacentMask ht ≠ 0 := by
  intro h
  have hx := tagOrdinal_add (0 : BitWord t) 0
  simp only [add_zero,Nat.xor_self] at hx
  have he := congrArg (fun a => (tagOrdinal t a).val) h
  simp only [adjacentMask,Equiv.apply_symm_apply,hx] at he
  omega

def adjacentPadding (ht : 1<2^t) (n : ℕ) : LiftedSlots (V × BitWord t) n L :=
  tagPadding (adjacentMask ht) (adjacent_ne ht) n

theorem padding_tag (ht : 1<2^t) (v : V) (g : BitWord t) (s : Fin n) (x : L) :
    let p := (adjacentPadding (V:=V) (L:=L) ht n).actualTarget (((v,g),s),x)
    p.1.1.1 = v ∧ (tagOrdinal t p.1.1.2).val = (tagOrdinal t g).val ^^^ 1 ∧ p.1.2 = s ∧ p.2=x := by
  dsimp only
  refine ⟨rfl,?_,rfl,add_zero x⟩
  change (tagOrdinal t (g+adjacentMask ht)).val = _
  rw [tagOrdinal_add]
  simp [adjacentMask]

end ThreeFlat.Diagonal.CompressorPacking.Native

end OAI
