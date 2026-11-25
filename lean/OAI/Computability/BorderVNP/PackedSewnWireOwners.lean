import OAI.Computability.BorderVNP.PackedSewnWireImage

/-! # Every live retained-cable fragment has a genuine terminal site owner -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.WireFragments

open Crossing Inherited CellAddressCircuit CellAddressPhysical ParseBatchSort
open Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport
open scoped Classical

variable {D s m n C k w : ℕ} {A P : Type} {bits : A → ℕ} (L : Network D A bits)
variable (siteID : L.Site ↪ Fin s) (edgeID : L.Edge ↪ Fin m)
variable {σ : Type} [Fintype σ] (F : Fields s m n C w k w σ) (p : Params) (name : ℕ → ℕ → ℕ)
variable (present : Fin m → σ) (hp : p.Valid) (lane : P ↪ Σ a, Fin (bits a))
variable {physical : PublicPort p.R p.processors p.literal p.link ≃ P} (hosts : BlockHosts (FineView.layout L lane) physical p.g)
variable (x : σ ⊕ Bool → Bool)
variable (post : Views.EndpointData (finalLayout p hosts) (FieldExport.fields F p name)
    siteID (mergedEdges p hp edgeID) finProdFinEquiv.toEmbedding x)

include post in
/-- The already represented sewn geometry identifies the site of every active old-wire
fragment. Unused rectangular slots cannot emit a fragment, since their width is zero. -/
theorem owners_of_sewn (a : Fragment.Parsed)
    (member : a ∈ Fragment.list ((sewnFrame F p name present).eval x)) :
    ∃ v, a.site = (F.sites (siteID v)).val := by
  let B := FieldExport.fields F p name
  let y := (sewnFrame F p name present).eval x
  change a ∈ (List.finRange (2*m)).filterMap (fun i => if Fragment.active y i then some (Fragment.parse y i) else none) at member
  obtain ⟨i,_,hm⟩ := List.mem_filterMap.mp member
  obtain ⟨⟨row,side⟩,rfl⟩ := ordinal.surjective i
  split at hm
  next enabled =>
    obtain rfl := Option.some.inj hm
    have live := (frame_active F B Sum.inl present (retainedRow m p.slots) x row side).mp enabled
    have occupied : row ∈ Set.range edgeID := by
      by_contra h
      have empty : retainedRow m p.slots row ∉ Set.range (mergedEdges p hp edgeID) := by
        rintro ⟨e,eq⟩
        cases e with
        | inl e => exact h ⟨e,Sum.inl.inj (finSumFinEquiv.injective eq)⟩
        | inr c =>
          have impossible : (Sum.inr (p.ordinal hp c) : Fin m ⊕ Fin p.slots) = .inl row := finSumFinEquiv.injective eq
          cases impossible
      have width := post.edgeHole _ empty
      simp only [fields,retainedRow,Equiv.symm_apply_apply,Sum.elim_inl,Function.comp_def] at width
      exact (Nat.ne_of_gt live.2.1) width
    obtain ⟨e,rfl⟩ := occupied
    have actual := frame_parse F B Sum.inl present (retainedRow m p.slots) x (edgeID e) side
    change ∃ v, (Fragment.parse y _).site = (F.sites (siteID v)).val
    have label : (Fragment.parse y (ordinal (edgeID e,side))).site = value (x ∘ Sum.inl ∘ F.ptr (Layer.edgeEnd (edgeID e) side)) :=
      congrArg Fragment.Parsed.site actual
    rw [label]
    cases side with
    | false =>
      refine ⟨L.dst e,?_⟩
      have ptr := post.dst (.inl e)
      change value (x ∘ B.ptr (.inl (.inr (finSumFinEquiv (Sum.inl (edgeID e) : Fin m ⊕ Fin p.slots))))) =
        (F.sites (siteID (L.dst e))).val at ptr
      simpa only [Layer.edgeEnd, Bool.false_eq_true, ite_false, B, fields, Equiv.symm_apply_apply,
        Sum.elim_inl,Function.comp_def] using ptr
    | true =>
      refine ⟨L.src e,?_⟩
      have ptr := post.src (.inl e)
      change value (x ∘ B.ptr (.inl (.inl (finSumFinEquiv (Sum.inl (edgeID e) : Fin m ⊕ Fin p.slots))))) =
        (F.sites (siteID (L.src e))).val at ptr
      simpa only [Layer.edgeEnd, ite_true, B, fields, Equiv.symm_apply_apply,Sum.elim_inl,Function.comp_def] using ptr
  next => cases hm

end Packing.SewnField.WireFragments

end BorderVNP
end Computability
end OAI
