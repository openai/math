import OAI.Computability.BorderVNP.DiagonalSiteTagRead
import OAI.Computability.BorderVNP.PackedHistoryPrivateSites
import OAI.Computability.BorderVNP.PackedInheritedParallelValue
import OAI.Computability.BorderVNP.PackedInheritedDenseValue

/-! # Pointwise reads of original private site programs on parallel and sorted tables -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Lineage

open Crossing Shortening PublicParallel Parallel DirectoryCircuit Diagonal.CellEntries
open scoped Classical

variable {D M np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {Param Gadget : Type*}

/-- A local tagged table and the original private checker at this site
agree at each physically ordered input, with its independent original
choices fixed. Later retention adds forced words to the current bank. -/
def TagModel (N : Network D P bits) (rows : N.Edge ↪ Fin M) (ports : P ↪ Fin np) (v : N.Site)
    (p : Site.Lineage (Inherited.incoming N v)) (compatible : (Fin p.birth.work → Bool) → Prop)
    (tags : N.Tables (Entry Param Gadget)) (number : Gadget ↪ ℕ) : Prop :=
  ∀ z x, Nonempty (TagRead p.birth (p.retention.readInput (inputWords N rows ports v z x ∘ Fin.cast p.size))
    compatible (tags v z x) number)

/-- Reading the physically retained work yields the same tags and
occurrences as the birth program, including its forced staging suffixes. -/
theorem TagModel.current {N : Network D P bits} {rows : N.Edge ↪ Fin M} {ports : P ↪ Fin np} {v : N.Site}
    {p : Site.Lineage (Inherited.incoming N v)} {compatible : (Fin p.birth.work → Bool) → Prop}
    {tags : N.Tables (Entry Param Gadget)} {number : Gadget ↪ ℕ}
    (model : TagModel N rows ports v p compatible tags number) (loc : p.birth.Local) (z x) :
    Nonempty (TagRead p.program (inputWords N rows ports v z x ∘ Fin.cast p.size)
      (fun g => compatible (p.retention.original g)) (tags v z x) number) := by
  obtain ⟨h⟩ := model z x
  exact ⟨h.retained p.retention loc _⟩

/-- A child site's private input vector and its true tag agree on each
copy of a disjoint parallel input. The old row and port orders are reused. -/
theorem TagModel.parallel {copies : ℕ} (p : Fin copies → Pack D P bits (Entry Param Gadget))
    (rows : ∀ i, (p i).layout.Edge ↪ Fin M) (ports : P ↪ Fin np) (i : Fin copies) (v : (p i).layout.Site)
    (s : Site.Lineage (Inherited.incoming (p i).layout v)) (compatible : (Fin s.birth.work → Bool) → Prop)
    (number : Gadget ↪ ℕ) (h : TagModel (p i).layout (rows i) ports v s compatible (p i).table number) :
    let L := Packing.parallelPacks p
    TagModel L.layout (parallelName rows) (portRows copies ports) ⟨i,v⟩
      (s.castWidth (incoming_eq (fun j => (p j).layout) i v).symm) compatible L.table number := by
  intro L z x
  have atWord (k : Fin s.program.incoming) := parallel_inputWords (fun j => (p j).layout) rows ports i v z x
    (Fin.cast s.size k)
  exact (congrArg (fun word => Nonempty (TagRead s.birth (s.retention.readInput word) compatible
    (L.table ⟨i,v⟩ z x) number)) (funext atWord)).mpr (h _ _)

/-- Sorting the edge directory preserves the physical incoming words and
the original checker, with its full pointwise fiber. -/
theorem TagModel.dense (p : Pack D P bits (Entry Param Gadget)) (rows : p.layout.Edge ↪ Fin M)
    (ports : P ↪ Fin np) (v : p.layout.Site) (s : Site.Lineage (Inherited.incoming p.layout v))
    (compatible : (Fin s.birth.work → Bool) → Prop) (number : Gadget ↪ ℕ)
    (h : TagModel p.layout rows ports v s compatible p.table number) :
    let L := densePack p rows
    TagModel L.layout (CutCircuit.denseRows p.layout rows) ports v (s.castWidth (dense_incoming p.layout rows v).symm)
      compatible L.table number := by
  intro L z x
  have atWord (k : Fin s.program.incoming) := dense_inputWords p.layout rows ports v z x (Fin.cast s.size k)
  exact (congrArg (fun word => Nonempty (TagRead s.birth (s.retention.readInput word) compatible
    (L.table v z x) number)) (funext atWord)).mpr (h _ _)

end Packing.Inherited.Site.Lineage

end BorderVNP
end Computability
end OAI
