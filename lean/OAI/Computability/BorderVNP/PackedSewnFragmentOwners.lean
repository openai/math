import OAI.Computability.BorderVNP.PackedSewnWireRoster
import OAI.Computability.BorderVNP.PackedSewnFragmentJoin

/-! # Real owners of the joined exterior fragment passes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open VPVNP.VerifierNetwork (Frame)

/-- Every enabled descriptor in the published array is the parse of an occupied slot. -/
theorem exists_slot_of_mem {n w : ℕ} {x : Pin n w → Bool} {p : Parsed} (hp : p ∈ list x) :
    ∃ i, active x i = true ∧ parse x i = p := by
  obtain ⟨i,_,eq⟩ := List.mem_filterMap.mp hp
  cases live : active x i <;> simp [live] at eq
  exact ⟨i,live,eq⟩

/-- The two physical operand arrays share the same named site keys. -/
theorem joinFrame_owners {σ V : Type} [Fintype σ] {n m w : ℕ} (left : Frame σ (Pin n w))
    (right : Frame σ (Pin m w)) (x : σ → Bool) (key : V → ℕ)
    (h₁ : ∀ p ∈ list (left.eval x), ∃ v, p.site=key v) (h₂ : ∀ p ∈ list (right.eval x), ∃ v, p.site=key v) :
    ∀ p ∈ list ((joinFrame left right).eval x), ∃ v, p.site=key v := by
  rw [joinFrame_list]
  intro p hp
  exact (List.mem_append.mp hp).elim (h₁ p) (h₂ p)

end Packing.SewnField.Fragment

namespace Packing.SewnField.WireFragments

open Crossing CellAddressCircuit CellAddressPhysical ParseBatchSort Inherited
open scoped Classical

variable {D s m n M N C k w : ℕ} {A σ τ : Type} [Fintype A] [Fintype σ] [Fintype τ]
    {bits : A → ℕ} (L : Network D A bits) (siteID : L.Site ↪ Fin s) (edgeID : L.Edge ↪ Fin m) (portID : A ↪ Fin n)
variable (F : Fields s m n C w k w σ) (B : Fields s M N C w k w τ) (old : σ → τ)
    (present : Fin m → σ) (retained : Fin m → Fin M) (x : τ → Bool)

omit [Fintype A] in
/-- An enabled wire fragment's owner is the true old source or destination site; a
self-loop supplies just its source-end occurrence. This uses only the old incidence scan. -/
theorem owners (beforeOK : Views.EndpointData L F siteID edgeID portID (x ∘ old))
    (occupied : ∀ i, x (old (present i)) = true ↔ i ∈ Set.range edgeID) :
    ∀ a ∈ Fragment.list ((frame F B old present retained).eval x), ∃ v, a.site = (F.sites (siteID v)).val := by
  intro a ha
  obtain ⟨i,live,rfl⟩ := Fragment.exists_slot_of_mem ha
  obtain ⟨⟨v,⟨e,_⟩⟩,rfl⟩ := (active_range L edgeID F B old present retained siteID portID x beforeOK occupied i).mp live
  refine ⟨v,?_⟩
  rw [index,frame_parse]
  by_cases src : L.src e.val=v
  · simpa only [src,decide_true,Layer.edgeEnd,ite_true,Function.comp_def] using
      (beforeOK.src e.val).trans (congrArg (fun u => (F.sites (siteID u)).val) src)
  · simpa only [decide_eq_false src,Layer.edgeEnd,Bool.false_eq_true,ite_false,Function.comp_def] using
      (beforeOK.dst e.val).trans (congrArg (fun u => (F.sites (siteID u)).val) (e.property.resolve_left src))

end Packing.SewnField.WireFragments

end BorderVNP
end Computability
end OAI
