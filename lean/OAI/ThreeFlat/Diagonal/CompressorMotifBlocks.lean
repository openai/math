import OAI.ThreeFlat.Diagonal.CompressorDemandOrdinal
import OAI.ThreeFlat.Diagonal.CompressorPackingCounts
import OAI.ThreeFlat.Diagonal.CompressorOrderIndex

namespace OAI
/-! # Dense global source-major motif indices from a bounded low-word scan

With every digit except the color word fixed, exactly a quarter of the
old wires are TT. Thus every contiguous physical block contains the
same number of CD records. Only the last block needs scanning.
-/

namespace ThreeFlat.Diagonal.CompressorPacking
open Computability.VPVNP.Compression
open scoped Classical BigOperators
variable {B H Tag L : Type*} {c d : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData B H Tag L d c)

def oldBlock (p : Site B Tag L × Fin d) (h : H) : Finset (Fin (2^c)) :=
  Finset.univ.filter fun u =>
    let a : Arc B H Tag L d c := (p,(Native.tagOrdinal c).symm u,h)
    ¬(P.thick (sourcePosition a) ∧ P.thick (sourcePosition (P.actual a)))

theorem oldBlock_card (p : Site B Tag L × Fin d) (h : H) (hc : 2 ≤ c) :
    (oldBlock P p h).card = 3*2^(c-2) := by
  let z := P.color p.1.1
  let v := P.color (P.slots.target (p.1.1,p.2)).1
  let k := P.bitShift (p.1.1,p.2) v
  let q := fun u : BitWord c => u z = 1 ∧ u v = 1-k
  have he : ↥(oldBlock P p h) ≃ {u : BitWord c // ¬q u} :=
    Equiv.subtypeEquiv (Native.tagOrdinal c).symm fun u => by
      simp only [oldBlock,Finset.mem_filter,Finset.mem_univ,true_and,q,z,v,k,
        both_thick,Pi.add_apply,eq_sub_iff_add_eq]
  have neq : z≠v := P.proper (p.1.1,p.2)
  have eq : 2^c = 2^(c-2)*4 := by
    conv_lhs => rw [show c=c-2+2 by omega,Nat.pow_add]
  rw [← Fintype.card_coe,Fintype.card_congr he,Fintype.card_subtype_compl]
  change Fintype.card (BitWord c) - Fintype.card {u : BitWord c // u z=1 ∧ u v=1-k} = _
  rw [fixed_bit_count _ _ neq]
  simp only [BitWord,Fintype.card_fun,Fintype.card_fin,ZMod.card,eq]
  omega

def blockIndex (p : Site B Tag L × Fin d) (h : H) (u : Fin (2^c)) : ℕ :=
  ((oldBlock P p h).filter fun x => x<u).card

theorem blockIndex_listed (p : Site B Tag L × Fin d) (h : H) (u : oldBlock P p h) (hc : 2 ≤ c) :
    blockIndex P p h u.val =
      (((oldBlock P p h).orderIsoOfFin (oldBlock_card P p h hc)).symm u).val := by
  let e := (oldBlock P p h).orderIsoOfFin (oldBlock_card P p h hc)
  have eq := sorted_index _ (oldBlock_card P p h hc) (e.symm u)
  change ((oldBlock P p h).filter fun x=>x<(e (e.symm u)).val).card=(e.symm u).val at eq
  rw [e.apply_symm_apply] at eq
  exact eq

end ThreeFlat.Diagonal.CompressorPacking

end OAI
