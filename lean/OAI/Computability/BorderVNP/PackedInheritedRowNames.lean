import Mathlib.Data.List.FinRange
import OAI.Computability.BorderVNP.PackedInheritedCovers

/-! # Stable public names of inherited incidence rows

Each old cable reserves two endpoint rows per band. A loop uses only its source
row. Ports use their unique attached site. A site's ordered history block is
obtained by restricting this single rectangular public order to that site.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Layer

open Crossing Shortening Shortening.SeedIntervals Shortening.CombiningStep
open scoped Classical

/-- Sparse slots reserved for the clipped endpoint rows and the attached port rows. -/
abbrev Row (old D np : ℕ) := ((Fin old × Band D) × Bool) ⊕ Fin np

variable {D m old np : ℕ} {K : Type*} {P : Type*} {bits : P → ℕ} (p : Pack D P bits K)
variable (edgeID : p.layout.Edge ↪ Fin old) (portID : P ↪ Fin np) (v : p.layout.Site)

/-- Name one site's intervals in the public rectangle; loops select the source column. -/
noncomputable def name : LayerRow p v ↪ Row old D np where
  toFun
    | .inl (z,b) => .inl ((edgeID z.val,b),decide (p.layout.src z.val = v))
    | .inr u => .inr (portID u.val)
  inj' := by
    rintro (⟨z,b⟩|u) (⟨z',b'⟩|u') h
    · simp only [Sum.inl.injEq,Prod.mk.injEq] at h
      obtain ⟨⟨h₁,rfl⟩,_⟩ := h
      obtain rfl := Subtype.ext (edgeID.injective h₁)
      rfl
    · contradiction
    · contradiction
    · exact congrArg Sum.inr (Subtype.ext (portID.injective (Sum.inr.inj h)))

/-- Integer indexing of the entire fixed rectangle, independent of all labels and widths. -/
noncomputable def order : Row old D np ≃ Fin (Fintype.card (Row old D np)) := Fintype.equivFin _

variable [Fintype P]

/-- Increasing order of this site's actual sparse source names. -/
noncomputable def index : Fin (Fintype.card (LayerRow p v)) ≃ LayerRow p v :=
  let r := (name p edgeID portID v).trans order.toEmbedding
  letI := LinearOrder.lift' r r.injective
  (Fintype.orderIsoFinOfCardEq _ rfl).toEquiv

/-- Comparing local indices is precisely comparing their public rectangle names. -/
theorem index_lt (i j : Fin (Fintype.card (LayerRow p v))) :
    order (name p edgeID portID v (index p edgeID portID v i)) <
      order (name p edgeID portID v (index p edgeID portID v j)) ↔ i < j := by
  let r := (name p edgeID portID v).trans order.toEmbedding
  let _ := LinearOrder.lift' r r.injective
  exact (Fintype.orderIsoFinOfCardEq (LayerRow p v) rfl).lt_iff_lt

variable [NeZero D] [Field K] (e : PaidIdentity K D m) {S : Type} [Fintype S]
variable (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S) (binName : S → ℕ)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
variable {next : ℕ} (nextID : (output e p bin perm positive first q).layout.Edge ↪ Fin next)

local notation3 "sl" => layerSlice e p bin perm binName positive first q v edgeID nextID portID

/-- Actual emitted list of clipped rows for a retained site's history block. -/
noncomputable def orderedCuts : List Slice := List.ofFn (sl ∘ index p edgeID portID v)

/-- Sorting the rows of a site by public names preserves their exact multiplicities. -/
theorem ordered_perm : (orderedCuts p edgeID portID v e bin perm binName positive first q nextID).Perm
    (layerCuts e p bin perm binName positive first q v edgeID nextID portID) := by
  let a := Fintype.equivFin (LayerRow p v)
  let σ := (index p edgeID portID v).trans a
  have h := Equiv.Perm.ofFn_comp_perm σ (sl ∘ a.symm)
  simpa [orderedCuts,layerCuts,σ,a,Function.comp_def] using h

/-- Coverage of the old incidence words is independent of the order of the sparse ties. -/
theorem covers_perm {n m : ℕ} {read : Fin n → Fin m} {a b : List Slice}
    (p : a.Perm b) (h : Covers n m b read) : Covers n m a read where
  oldFit r hr := h.oldFit r (p.mem_iff.mp hr)
  newFit r hr := h.newFit r (p.mem_iff.mp hr)
  agrees r hr i := h.agrees r (p.mem_iff.mp hr) i
  covers k := by
    obtain ⟨r,hr,i,hi⟩ := h.covers k
    exact ⟨r,p.mem_iff.mpr hr,i,hi⟩

/-- Stable public execution realizes the same physical lane reconstruction as the geometric cut. -/
theorem ordered_covers : Covers (incoming p.layout v) (incoming (output e p bin perm positive first q).layout (.inl v))
    (orderedCuts p edgeID portID v e bin perm binName positive first q nextID)
    (layerRead e p bin perm positive first q v edgeID nextID portID) :=
  covers_perm (ordered_perm p edgeID portID v e bin perm binName positive first q nextID)
    (layer_covers e p bin perm binName positive first q v edgeID nextID portID)

end Packing.Inherited.Layer

end BorderVNP
end Computability
end OAI
