import OAI.ThreeFlat.Diagonal.ShrinkGraph
import Mathlib.Algebra.BigOperators.Fin
import OAI.ThreeFlat.Diagonal.CompressorRadixKey

namespace OAI
/-! # Mixed-radix canonical ordinals for actual retained edge occurrences

The remaining lane is zero in a rooted motif. Its label therefore needs
only the old base, tag, outgoing port, color bits, and old slot-label bits.
Two final digits record the surviving supply type and the parallel piece.
-/

namespace ThreeFlat.Diagonal.CompressorPacking
open Computability.VPVNP.Compression
variable {V H Tag L : Type*} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable {d c t : ℕ} (P : PackingData V H Tag L d c)

variable (baseId : V ↪ ℕ) (tagId : Tag ↪ Fin t)

def rootKey (r : Rooted P) : ℕ :=
  let a := r.val.val
  appendKey (appendKey (appendKey (appendKey (baseId a.1.1.1) (tagId a.1.1.2.1)) a.1.2)
    (finFunctionFinEquiv (m:=2) a.2.1)) (P.slotLabel a.2.2)

theorem rootKey_inj : Function.Injective (rootKey P baseId tagId) := by
  intro r s h
  obtain ⟨h,hlabel⟩ := appendKey_inj h
  obtain ⟨h,hbits⟩ := appendKey_inj h
  obtain ⟨h,hslot⟩ := appendKey_inj h
  obtain ⟨hbase,htag⟩ := appendKey_inj h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact Prod.ext (Prod.ext (baseId.injective hbase) (Prod.ext (tagId.injective htag)
      (r.property.trans s.property.symm))) hslot
  · exact Prod.ext (finFunctionFinEquiv.injective hbits) (P.slotLabel.injective hlabel)

variable (count : Fin 4 → ℕ) (pieces : ℕ) (bound : ∀ t, count t ≤ pieces)

def edgeKey (e : ShrinkEdge P count) : ℕ :=
  appendKey (appendKey (rootKey P baseId tagId e.2.1) e.1) (e.2.2.castLE (bound e.1))

def edgeOrder : ShrinkEdge P count ↪ ℕ where
  toFun := edgeKey P baseId tagId count pieces bound
  inj' := by
    rintro ⟨a,m,i⟩ ⟨b,n,j⟩ eq
    obtain ⟨h,hcopy⟩ := appendKey_inj eq
    obtain ⟨h,hrole⟩ := appendKey_inj h
    change a=b at hrole
    subst b
    have same : m=n := rootKey_inj P baseId tagId h
    have copy : i=j := Fin.ext (congrArg (fun x : Fin pieces=>x.val) hcopy)
    cases same
    cases copy
    rfl

end ThreeFlat.Diagonal.CompressorPacking

end OAI
