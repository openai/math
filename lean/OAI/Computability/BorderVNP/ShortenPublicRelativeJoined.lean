import OAI.Computability.BorderVNP.ShortenPublicRelativeSerializer

/-!
# Physical meaning of the sparse endpoint join on the successor table

The emitted geometry fields name the actual sewn quotient sites. Consequently
the single sparse join retrieves a canonical pair for each occupied cable and
two copies of the reserved site for each hole. The charge bit remains a
separate input, since the two endpoint lookups do not depend on it.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative

open Epoch Catalog Crossing CombiningStep Cover Cover.AddressCircuit StaticRows PublicEndpoints
open PublicEndpoints.Successor PublicSegments
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D lev V E w : ℕ} {P : Type*} {bits : P → ℕ} {B : Type*} [Fintype B]

/-- Correspondence to the sparse type reader's exact site payload, padded
cable directory and occupancy bit on every stable row. -/
structure GeometryTable (S : Finset (HyperbolicHost (Cube D))) (N : Network D P bits)
    (sites : N.Site ↪ Fin V) (rows : N.Edge ↪ Fin E) (dummy : Fin E → N.Site)
    (pos : N.Site → SurfaceHost (Cube D) (lev+1)) (field : FieldBit (↥S) (Cube D) (lev+1) → B)
    (y : Next B V E w → Bool) : Prop where
  /-- Every quotient site is in the fixed successor catalog. -/
  valid : ∀ v, relative lev (pos v) ∈ S
  /-- Addresses and widths of all rows, occupied and padded. -/
  names : PublicEndpoints.Represents N sites rows dummy (y ∘ Sum.inl)
  /-- Cable row occupancy is independent of its width or charge. -/
  occupied : ∀ r, y (.inr r) = true ↔ r ∈ Set.range rows
  /-- Actual site fields in the next-stage reader's wire order. -/
  payload : ∀ v j, y (.inl (.inl (sites v,field j))) = siteBits (pos v) (valid v) j

/-- Physical occupied and padded endpoint pairs read by the sparse join.
The same joined payload works for any choice of downstream charge wires. -/
theorem GeometryTable.join_rows {S : Finset (HyperbolicHost (Cube D))} {N : Network D P bits}
    {sites : N.Site ↪ Fin V} {rows : N.Edge ↪ Fin E} {dummy : Fin E → N.Site}
    {pos : N.Site → SurfaceHost (Cube D) (lev+1)} {field : FieldBit (↥S) (Cube D) (lev+1) → B}
    {y : Next B V E w → Bool} (g : GeometryTable S N sites rows dummy pos field y)
    (charge : Fin E → Bool) (fit : V ≤ 2^w) :
    let input : Raw B V E w w → Bool := Sum.elim charge (y ∘ Sum.inl)
    let output := (expand B w fit).eval input
    (∀ e, output ∘ pairAt field (rows e) =
      endpointBits (pos (N.src e)) (pos (N.dst e)) (g.valid _) (g.valid _)) ∧
    ∀ i, i ∉ Set.range rows → let v := dummy (Packing.Names.rowSlot i)
      output ∘ pairAt field i = endpointBits (pos v) (pos v) (g.valid v) (g.valid v) := by
  intro input out
  exact ⟨expanded_occupied N sites rows dummy pos g.valid field input fit g.names g.payload,
    expanded_unused N sites rows dummy pos g.valid field input fit g.names g.payload⟩

variable {q m : ℕ} [NeZero D] {K : Type*} [Field K] {A : Type} [Fintype A]
variable (N : Pack D P bits K) (bin : N.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)

/-- The source circuit and serializer give exactly the representation consumed
by the sparse geometric join in the next round, for every histogram branch. -/
theorem placement_geometry_of_reads (enum : Fin q ≃ Cube D) (pat : Pattern (Cube D) D)
    (e : PaidIdentity K D m) (S : Finset (HyperbolicHost (Cube D))) {d copies sites edges seeds w : ℕ}
    (home : Fin sites → Fin copies) {sf : Frame (BatchPorts q pat S d copies sites seeds)
      (Fin (siteCapacity e sites seeds) × (ProductSlots q (d+2*pat.depth) ⊕ ↥(pat.nextSites e S)))}
    (batch : BatchRows enum pat e S d home sf) (lev : ℕ) (hl : lev+1=d+2*pat.depth)
    (g : Placement (m := m) N bin perm (Cube D) (SurfaceHost (Cube D) (lev+1)))
    (a : PublicPlacement pat S N bin perm lev g) (old : N.layout.Site ↪ Fin sites)
    (rows : N.layout.Edge ↪ Fin edges) (seed : A ≃ Fin seeds)
    (dummy : Fin (edgeCapacity e edges seeds) → SiteShape e N A)
    (geo : BatchPorts q pat S d copies sites seeds → Bool)
    (reads : PlacementReads N bin perm enum pat S home g a old seed.toEmbedding geo)
    (positive : N.layout.Edge → Bool) (first : Fin D × Bool) (counts : Counts e N bin perm)
    (c : CableFields e A edges w → Bool)
    (y : Next (ProductSlots q (d+2*pat.depth) ⊕ ↥(pat.nextSites e S)) (siteCapacity e sites seeds)
      (edgeCapacity e edges seeds) w → Bool)
    (result : Result e N bin perm positive old rows seed dummy first counts
      (Sum.elim (sf.eval geo) c) y) :
    GeometryTable (pat.nextSites e S) (output e N bin perm positive first counts).layout
      (siteRows e N old seed.toEmbedding) (outputRows e N bin perm positive first counts rows seed.toEmbedding)
      dummy (g.postSites N bin perm e positive counts) (segmentField enum (pat.nextSites e S) hl) y := by
  have valid := actual_sites e N bin perm positive lev pat S g counts a.copyMotion a.oldLift a.oldDeck
    a.oldType a.moved a.code a.chartEq a.deck a.projects
  refine ⟨valid,result.rows,result.occupied,?_⟩
  intro v j
  let field := segmentField enum (pat.nextSites e S) hl
  have h := batch.placement_rows_of_reads N bin perm enum pat e S home lev hl g a old seed.toEmbedding geo reads
    positive counts v (field j)
  exact (result.sites (_,field j)).trans (h.trans (congrFun
    (quotientRow_siteBits enum (pat.nextSites e S) hl _ (valid v)) j))

/-- The source circuit and serializer give exactly the representation consumed
by the sparse geometric join in the next round, for every histogram branch. -/
theorem placement_geometry (enum : Fin q ≃ Cube D) (pat : Pattern (Cube D) D)
    (e : PaidIdentity K D m) (S : Finset (HyperbolicHost (Cube D))) {d copies sites edges seeds w : ℕ}
    (home : Fin sites → Fin copies) {sf : Frame (BatchPorts q pat S d copies sites seeds)
      (Fin (siteCapacity e sites seeds) × (ProductSlots q (d+2*pat.depth) ⊕ ↥(pat.nextSites e S)))}
    (batch : BatchRows enum pat e S d home sf) (lev : ℕ) (hl : lev+1=d+2*pat.depth)
    (g : Placement (m := m) N bin perm (Cube D) (SurfaceHost (Cube D) (lev+1)))
    (a : PublicPlacement pat S N bin perm lev g) (old : N.layout.Site ↪ Fin sites)
    (rows : N.layout.Edge ↪ Fin edges) (seed : A ≃ Fin seeds)
    (dummy : Fin (edgeCapacity e edges seeds) → SiteShape e N A)
    (pick : Fin copies → Fin pat.moves) (shift : Fin copies → Cube D → gamma 1)
    (hp : ∀ v, pick (home (old v)) = a.copyMotion v) (hs : ∀ v, shift (home (old v)) = a.oldDeck v)
    (positive : N.layout.Edge → Bool) (first : Fin D × Bool) (counts : Counts e N bin perm)
    (c : CableFields e A edges w → Bool)
    (y : Next (ProductSlots q (d+2*pat.depth) ⊕ ↥(pat.nextSites e S)) (siteCapacity e sites seeds)
      (edgeCapacity e edges seeds) w → Bool)
    (result : Result e N bin perm positive old rows seed dummy first counts
      (Sum.elim (sf.eval (placementInput N bin perm enum pat S d lev g a old seed.toEmbedding pick shift)) c) y) :
    GeometryTable (pat.nextSites e S) (output e N bin perm positive first counts).layout
      (siteRows e N old seed.toEmbedding) (outputRows e N bin perm positive first counts rows seed.toEmbedding)
      dummy (g.postSites N bin perm e positive counts) (segmentField enum (pat.nextSites e S) hl) y := by
  exact placement_geometry_of_reads N bin perm enum pat e S home batch lev hl g a old rows seed dummy _
    (placementInput_reads N bin perm enum pat S d lev g a old seed.toEmbedding pick shift home hp hs)
    positive first counts c y result

end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
