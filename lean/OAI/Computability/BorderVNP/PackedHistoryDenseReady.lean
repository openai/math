import OAI.Computability.BorderVNP.ShortenCubeEnumeration
import OAI.Computability.BorderVNP.PackedHistoryDenseStep
import OAI.Computability.BorderVNP.ShortenPublicParallelStage

/-! # Reading the complete saved cable directory at a normalized physical node

The physical table carries both the segment fields and a separate presence
column. Dense saving preserves the sparse public queries at their exact row
numbers, including the queries for zero-width occupied cables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Cover Crossing Packing Shortening Epoch Catalog StaticRows PublicRelative PublicSegments
open scoped Classical BorderVNP.Epoch.Cube

variable {D lev V E w : ℕ} {K : Type*} {P Data : Type} {bits : P → ℕ}

/-- The public site and cable addresses and the site reserved for each virtual row. -/
structure Directory (p : PlacedPack D P bits K (Cube D) lev) (V E : ℕ) where
  /-- Injective site names in the prepared rectangle. -/
  sites : p.pack.layout.Site ↪ Fin V
  /-- Injective cable names in the prepared rectangle. -/
  cables : p.pack.layout.Edge ↪ Fin E
  /-- Site used by the dummy loop at each vacant cable slot. -/
  dummy : Fin E → p.pack.layout.Site

namespace Directory

variable {p : PlacedPack D P bits K (Cube D) lev} (a : Directory p V E)
    (S : Finset (HyperbolicHost (Cube D)))
    (field : PublicSegments.FieldBit (↥S) (Cube D) (lev+1) → Data)

/-- The charged geometry and the independently readable presence column of a stored pack. -/
structure Reads (x : Fin E ⊕ Raw Data V E w w → Bool) : Prop where
  /-- Catalog membership, exact site payload, pointers, widths and charge for the next classifier. -/
  geometry : SegmentReady S p.pack.layout a.sites a.cables a.dummy p.site field p.charged (x ∘ Sum.inr)
  /-- Presence is read independently of charge and width. -/
  present : ∀ j, x (.inl j) = true ↔ j ∈ Set.range a.cables

/-- The same physical rows after saving the pack in dense cable order. -/
noncomputable def dense : Directory (p.dense a.cables) V E :=
  ⟨a.sites,PublicEndpoints.densePublicRows p.pack.layout a.cables,a.dummy⟩

/-- Saving the cable order preserves every actual site name. -/
theorem dense_sites : a.dense.sites = a.sites := rfl

/-- The densely saved cable retains precisely its original stable sparse row. -/
theorem dense_cable (z : p.pack.layout.Edge) :
    a.dense.cables (Names.denseSlot p.pack.layout a.cables z) = a.cables z :=
  PublicEndpoints.densePublicRows_slot p.pack.layout a.cables z

/-- On every assignment the ready table continues to describe the densely stored successor. -/
theorem reads_dense {x : Fin E ⊕ Raw Data V E w w → Bool} (h : a.Reads S field x) :
    a.dense.Reads S field x := by
  refine ⟨PublicParallel.dense_ready h.geometry,?_⟩
  intro j
  exact (h.present j).trans (by
    change j ∈ Set.range a.cables ↔ j ∈ Set.range (PublicEndpoints.densePublicRows p.pack.layout a.cables)
    rw [PublicEndpoints.densePublicRows_range])

end Directory

private noncomputable def sewnRows {D m nEdges nSeeds : ℕ} [NeZero D] {K : Type*} [Field K]
    {P A : Type} [Fintype A] {bits : P → ℕ} (e : PaidIdentity K D m) (N : Pack D P bits K)
    (label : N.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (orient : N.layout.Edge → Bool)
    (hist : CombiningStep.Counts e N label perm) (old : N.layout.Edge ↪ Fin nEdges) (seed : A ↪ Fin nSeeds) :
    (CombiningStep.output e N label perm orient (0,false) hist).layout.Edge ↪ Fin (edgeCapacity e nEdges nSeeds) :=
  outputRows e N label perm orient (0,false) hist old seed

namespace Stage

variable {m copies d d' nSeeds nSites : ℕ} [NeZero D] [Field K] {B : Type} [Fintype B]
    {child : Fin copies → PlacedPack D P bits K (Cube D) d} (s : Stage m B d' child)
    (e : PaidIdentity K D m)

set_option maxHeartbeats 1600000 in
/-- Exact saved directory at a histogram of the densely sorted physical stage.
Its cable rows are the actual old-band, hook, residual and bank candidates of
the successor serializer. -/
noncomputable def directory (old : (raw child).layout.Site ↪ Fin nSites)
    (seed : ((Cube D → Deck (d'+1)) × B) ↪ Fin nSeeds)
    (dummy : Fin (edgeCapacity e s.rowCount nSeeds) →
      SiteShape e s.input ((Cube D → Deck (d'+1)) × B))
    (hist : s.Index e) :
    Directory (s.result e hist) (siteCapacity e nSites nSeeds) (edgeCapacity e s.rowCount nSeeds) :=
  by
    let N := s.input
    let out := CombiningStep.output e N s.label s.perm s.orient (0,false) hist
    let cols : N.layout.Edge ↪ Fin s.rowCount := CutCircuit.denseRows (raw child).layout s.slot
    refine ⟨?_,?_,?_⟩
    · change SiteShape e N _ ↪ Fin _
      exact siteRows e N old seed
    · change out.layout.Edge ↪ Fin _
      exact sewnRows e N s.label s.perm s.orient hist cols seed
    · exact dummy

/-- The old vertices and new bank sites are stored at exactly the row numbers
computed by the public site directory. These names are unaffected by the
subsequent dense cable save. -/
theorem directory_sites (old : (raw child).layout.Site ↪ Fin nSites)
    (seed : ((Cube D → Deck (d'+1)) × B) ↪ Fin nSeeds)
    (dummy : Fin (edgeCapacity e s.rowCount nSeeds) → SiteShape e s.input ((Cube D → Deck (d'+1)) × B))
    (hist : s.Index e) : (s.directory e old seed dummy hist).sites = siteRows e s.input old seed := rfl

/-- Stable numeric cable row, with the actual sorted old cable, cut band,
or seed-template cable used by the native serializer. -/
noncomputable def cableNumber (seed : ((Cube D → Deck (d'+1)) × B) ↪ Fin nSeeds)
    (hist : s.Index e) (z : (s.result e hist).pack.layout.Edge) : ℕ :=
  (outputRows e s.input s.label s.perm s.orient (0,false) hist
    (CutCircuit.denseRows (raw child).layout s.slot) seed z).val

/-- The actual saved directory uses the serializer's numeric cable rows. -/
theorem directory_cableNumber (old : (raw child).layout.Site ↪ Fin nSites)
    (seed : ((Cube D → Deck (d'+1)) × B) ↪ Fin nSeeds)
    (dummy : Fin (edgeCapacity e s.rowCount nSeeds) → SiteShape e s.input ((Cube D → Deck (d'+1)) × B))
    (hist : s.Index e) (z : (s.result e hist).pack.layout.Edge) :
    ((s.directory e old seed dummy hist).cables z).val = s.cableNumber e seed hist z := rfl

end Stage
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
