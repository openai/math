import OAI.Computability.BorderVNP.PackedInheritedEndpointViews
import OAI.Computability.BorderVNP.PackedHistoryDenseReady

/-! # Recovering the pre-save endpoints from the real node output

The stable sparse cable name travels with each cable through the second
dense sort. The saved pointer and width words therefore describe the
original combining step as well as its stored presentation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddressCircuit

/-- Select the endpoint and metadata pins of a physical field table from a
common source that also exposes the old operands and histogram. -/
def Fields.mapPins {s e p c d k w : ℕ} {σ τ : Type*} (F : Fields s e p c d k w σ) (select : σ → τ) :
    Fields s e p c d k w τ where
  sites := F.sites
  cells := F.cells
  owner i := select ∘ F.owner i
  ptr i := select ∘ F.ptr i
  edgeWidth i := select ∘ F.edgeWidth i
  auxWidth i := select ∘ F.auxWidth i
  portWidth i := select ∘ F.portWidth i

/-- Change only the types of the scheduled site and cable rectangles. -/
def Fields.castRect {V E np C d k w V' E' : ℕ} {σ : Type*}
    (f : Fields V E np C d k w σ) (hv : V = V') (he : E = E') : Fields V' E' np C d k w σ := by
  subst V'; subst E'
  exact f

/-- Scheduled rectangle transport preserves the numeric site key at every
row, including the unused site rows. -/
theorem Fields.castRect_site {V E np C d k w V' E' : ℕ} {σ : Type*}
    (f : Fields V E np C d k w σ) (hv : V = V') (he : E = E') (i : Fin V') :
    ((f.castRect hv he).sites i).val = (f.sites (Fin.cast hv.symm i)).val := by
  subst V'; subst E'; rfl

end Packing.CellAddressCircuit

namespace Packing.Inherited.Views

open Crossing Shortening Shortening.PublicEndpoints Cover Epoch PackedHistoryCircuit.Normalized CellAddressCircuit ParseBatchSort
open scoped Classical BorderVNP.Epoch.Cube

variable {D V E np C d k w lev : ℕ} {P K σ : Type} {bits : P → ℕ}
variable (p saved : PlacedPack D P bits K (Cube D) lev) (dir : Directory p V E) (names : Directory saved V E)
variable (F : Fields V E np C d k w σ) (port : P ↪ Fin np)

/-- Reading the selected public operands in a combined frame gives the same
endpoint receipt on the combined input assignment. -/
theorem EndpointData.mapPins {N : Network D P bits} {v : N.Site ↪ Fin V} {a : N.Edge ↪ Fin E}
    {τ : Type*} {x : σ → Bool} (select : σ → τ) (y : τ → Bool) (same : y ∘ select = x)
    (h : EndpointData N F v a port x) : EndpointData N (F.mapPins select) v a port y := by
  subst x
  exact ⟨h.src,h.dst,h.attach,h.edge,h.port,h.edgeHole,h.portHole⟩

/-- Undo the actual dense save, preserving every cable's sparse name,
endpoints and width, all attached ports, and every unoccupied row. -/
theorem EndpointData.of_named_save {x : σ → Bool} (stored : saved = p.dense dir.cables) (hs : HEq names dir.dense)
    (h : EndpointData saved.pack.layout F names.sites names.cables port x) :
    EndpointData p.pack.layout F dir.sites dir.cables port x := by
  subst saved
  cases eq_of_heq hs
  let N := p.pack.layout
  let old (z : N.Edge) := Names.denseSlot N dir.cables z
  have same (z : N.Edge) : dir.dense.cables (old z) = dir.cables z := dir.dense_cable z
  constructor
  · intro z
    have src : (p.dense dir.cables).pack.layout.src (old z) = N.src z := Names.src_slot N _ _ z
    exact (congrArg (fun a => value (x ∘ F.ptr (.inl (.inl a)))) (same z).symm).trans
      ((h.src (old z)).trans (congrArg (fun a => (F.sites (dir.sites a)).val) src))
  · intro z
    have dst : (p.dense dir.cables).pack.layout.dst (old z) = N.dst z := Names.dst_slot N _ _ z
    exact (congrArg (fun a => value (x ∘ F.ptr (.inl (.inr a)))) (same z).symm).trans
      ((h.dst (old z)).trans (congrArg (fun a => (F.sites (dir.sites a)).val) dst))
  · exact h.attach
  · intro z
    have width : (p.dense dir.cables).pack.layout.width (old z) = N.width z := Names.width_slot N _ _ z
    exact (congrArg (fun a => value (x ∘ F.edgeWidth a)) (same z).symm).trans ((h.edge (old z)).trans width)
  · exact h.port
  · intro i hi
    apply h.edgeHole i
    rintro ⟨a,rfl⟩
    obtain ⟨z,rfl⟩ := (Names.denseSlot N dir.cables).surjective a
    exact hi ⟨z,(same z).symm⟩
  · exact h.portHole

/-- Numeric agreement of the two row assignments transports every physical
endpoint to the original emitter's static rectangles. -/
theorem EndpointData.castRect {N : Network D P bits} {V' E' : ℕ} {v : N.Site ↪ Fin V} {a : N.Edge ↪ Fin E}
    {v' : N.Site ↪ Fin V'} {a' : N.Edge ↪ Fin E'} {x : σ → Bool} (hv : V = V') (he : E = E')
    (hnv : ∀ i, (v i).val = (v' i).val) (hne : ∀ i, (a i).val = (a' i).val)
    (h : EndpointData N F v a port x) : EndpointData N (F.castRect hv he) v' a' port x := by
  subst V'; subst E'
  have eqv : v = v' := DFunLike.ext _ _ fun i => Fin.ext (hnv i)
  have eqa : a = a' := DFunLike.ext _ _ fun i => Fin.ext (hne i)
  subst v'; subst a'; exact h

end Packing.Inherited.Views

end BorderVNP
end Computability
end OAI
