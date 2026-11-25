import OAI.Computability.BorderVNP.ShortenPublicRelativeJoined
import OAI.Computability.BorderVNP.ShortenPublicDirectoryOccupancy

/-! # The physical site, pointer and charge banks on the next classifier's input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative

open Epoch Catalog Crossing CombiningStep Cover Cover.AddressCircuit StaticRows PublicEndpoints
open PublicEndpoints.Successor PublicSegments
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D m q lev V E w : ℕ} {P : Type*} {bits : P → ℕ} {B : Type*} [Fintype B]

/-- Exact row contract for the next geometric classifier. Holes have false
charge, width zero, and a duplicate endpoint pointing at their reserved site. -/
structure SegmentReady (S : Finset (HyperbolicHost (Cube D))) (N : Network D P bits)
    (sites : N.Site ↪ Fin V) (rows : N.Edge ↪ Fin E) (dummy : Fin E → N.Site)
    (pos : N.Site → SurfaceHost (Cube D) (lev+1)) (field : FieldBit (↥S) (Cube D) (lev+1) → B)
    (mask : N.Edge → Bool) (x : Raw B V E w w → Bool) : Prop where
  /-- Every site belongs to the successor catalog. -/
  valid : ∀ v, relative lev (pos v) ∈ S
  /-- The real stable pointer and width fields, including padding. -/
  names : PublicEndpoints.Represents N sites rows dummy (x ∘ Sum.inr)
  /-- The queried site payload is in the classifier's exact factor order. -/
  payload : ∀ v j, x (.inr (.inl (sites v,field j))) = siteBits (pos v) (valid v) j
  /-- The real post-mask is forwarded on every occupied cable. -/
  charge : ∀ z, x (.inl (rows z)) = mask z
  /-- Empty reserved cable numbers have a false charge. -/
  hole : ∀ i, i ∉ Set.range rows → x (.inl i) = false

/-- The actual charge-bearing frame yields both physical endpoints for a
live cable and the same reserved endpoint twice for a hole. -/
theorem SegmentReady.join_rows {S : Finset (HyperbolicHost (Cube D))} {N : Network D P bits}
    {sites : N.Site ↪ Fin V} {rows : N.Edge ↪ Fin E} {dummy : Fin E → N.Site}
    {pos : N.Site → SurfaceHost (Cube D) (lev+1)} {field : FieldBit (↥S) (Cube D) (lev+1) → B}
    {mask : N.Edge → Bool} {x : Raw B V E w w → Bool}
    (g : SegmentReady S N sites rows dummy pos field mask x) (fit : V ≤ 2^w) :
    let joined := (expand B w fit).eval x
    (∀ e, joined ∘ pairAt field (rows e) =
      endpointBits (pos (N.src e)) (pos (N.dst e)) (g.valid _) (g.valid _)) ∧
    ∀ i, i ∉ Set.range rows → let v := dummy (Packing.Names.rowSlot i)
      joined ∘ pairAt field i = endpointBits (pos v) (pos v) (g.valid v) (g.valid v) := by
  intro out
  exact ⟨expanded_occupied N sites rows dummy pos g.valid field x fit g.names g.payload,
    expanded_unused N sites rows dummy pos g.valid field x fit g.names g.payload⟩

variable {K : Type*} [Field K] [NeZero D] {A : Type} [Fintype A]

set_option maxHeartbeats 1600000 in
/-- Uniform compiled transition from the copy, old-site, seed, interval and
histogram wires to the complete next-classifier input. The geometric batch is
charged once, the serializer once, and three additional gates per cable suffice. -/
theorem uniformOccupiedGeometry_frames (enum : Fin q ≃ Cube D) (pat : Pattern (Cube D) D)
    (e : PaidIdentity K D m) (S : Finset (HyperbolicHost (Cube D))) :
    ∃ C k : ℕ, ∀ {A : Type} [Fintype A] {P : Type*} {bits : P → ℕ} (d : ℕ), 1 ≤ d → ∀ (copies sites edges seeds w : ℕ)
      (home : Fin sites → Fin copies) (seed : A ≃ Fin seeds),
      siteCapacity e sites seeds ≤ 2^w → edgeCapacity e edges seeds ≤ 2^w →
      let B := ProductSlots q (d+2*pat.depth) ⊕ ↥(pat.nextSites e S)
      ∃ (sf : Frame (BatchPorts q pat S d copies sites seeds) (Fin (siteCapacity e sites seeds) × B))
        (f : Frame (BatchPorts q pat S d copies sites seeds ⊕ CableFields e A edges w)
          (Fin (edgeCapacity e edges seeds) ⊕ Raw B (siteCapacity e sites seeds) (edgeCapacity e edges seeds) w w)),
        BatchRows enum pat e S d home sf ∧ f.size ≤ (1+siteCapacity e sites seeds)*C*(d+1)^k +
          (cost e edges seeds w + 3*edgeCapacity e edges seeds) ∧
        ∀ (N : Pack D P bits K) (bin : N.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
          (lev : ℕ) (hl : lev+1=d+2*pat.depth) (g : Placement (m := m) N bin perm (Cube D) (SurfaceHost (Cube D) (lev+1)))
          (a : PublicPlacement pat S N bin perm lev g) (old : N.layout.Site ↪ Fin sites) (rows : N.layout.Edge ↪ Fin edges)
          (dummy : Fin (edgeCapacity e edges seeds) → SiteShape e N A)
          (geo : BatchPorts q pat S d copies sites seeds → Bool),
          PlacementReads N bin perm enum pat S home g a old seed.toEmbedding geo →
          ∀ (positive : N.layout.Edge → Bool) (first : Fin D × Bool) (hist : Counts e N bin perm)
            (c : CableFields e A edges w → Bool),
            SourceData e N bin perm positive old rows seed dummy first hist (Sum.elim (sf.eval geo) c) →
            SegmentReady (pat.nextSites e S) (output e N bin perm positive first hist).layout
              (siteRows e N old seed.toEmbedding) (outputRows e N bin perm positive first hist rows seed.toEmbedding)
              dummy (g.postSites N bin perm e positive hist) (segmentField enum (pat.nextSites e S) hl)
              (postMask N bin perm e positive hist) ((f.eval (Sum.elim geo c)) ∘ Sum.inr) ∧
            ∀ i, f.eval (Sum.elim geo c) (.inl i) = true ↔
              i ∈ Set.range (outputRows e N bin perm positive first hist rows seed.toEmbedding) := by
  obtain ⟨C,k,frames⟩ := batchRow_frames enum pat e S
  refine ⟨C,k,?_⟩
  intro A instA P bits d hd copies sites edges seeds w home seed hs he B
  obtain ⟨sf,hbatch,hsize⟩ := frames d hd copies sites seeds home
  obtain ⟨wire,hw,hout⟩ := Successor.exists_frame e B sites edges w seed hs he
  let read := occupiedSegmentInput e B sites edges w seed wire
  let f := read.subst (preparedSource e sf)
  refine ⟨sf,f,hbatch,?_,?_⟩
  · rw [show f.size = sf.size + read.size by simp [f,preparedSource_size]]
    rw [show read.size = (segmentInput e B sites edges w seed wire).size from occupiedSegmentInput_size ..]
    exact Nat.add_le_add hsize ((segmentInput_size e B sites edges w seed wire).trans (Nat.add_le_add_right hw _))
  intro N bin perm lev hl g a old rows dummy geo reads positive first hist c src
  let z := Sum.elim (sf.eval geo) c
  have result := hout N bin perm positive old rows dummy first hist z src
  have geom := placement_geometry_of_reads N bin perm enum pat e S home hbatch lev hl g a old rows seed dummy geo reads
    positive first hist c (wire.eval z) result
  have heval : f.eval (Sum.elim geo c) = read.eval z := by
    funext j
    simp only [f,Frame.subst_eval,preparedSource_eval,z]
  rw [heval]
  refine ⟨?_,occupiedSegmentInput_occupied e B sites edges w seed wire z N bin perm positive old rows dummy first hist result⟩
  rw [show read.eval z ∘ Sum.inr = (segmentInput e B sites edges w seed wire).eval z from occupiedSegmentInput_raw ..]
  refine ⟨geom.valid,segmentInput_rows e B sites edges w seed wire z N bin perm positive old rows dummy first hist result,
    ?_,segmentInput_charge e B sites edges w seed wire z N bin perm positive old rows dummy first hist src result,
    segmentInput_hole e B sites edges w seed wire z N bin perm positive old rows dummy first hist result⟩
  intro v j
  exact (segmentInput_table e B sites edges w seed wire z _).trans (geom.payload v j)

set_option maxHeartbeats 1600000 in
/-- Uniform compiled transition from the copy, old-site, seed, interval and
histogram wires to the complete next-classifier input. The geometric batch is
charged once, the serializer once, and three additional gates per cable suffice. -/
theorem occupiedGeometry_frames_of_reads (enum : Fin q ≃ Cube D) (pat : Pattern (Cube D) D)
    (e : PaidIdentity K D m) (S : Finset (HyperbolicHost (Cube D))) :
    ∃ C k : ℕ, ∀ (d : ℕ), 1 ≤ d → ∀ (copies sites edges seeds w : ℕ)
      (home : Fin sites → Fin copies) (seed : A ≃ Fin seeds),
      siteCapacity e sites seeds ≤ 2^w → edgeCapacity e edges seeds ≤ 2^w →
      let B := ProductSlots q (d+2*pat.depth) ⊕ ↥(pat.nextSites e S)
      ∃ (sf : Frame (BatchPorts q pat S d copies sites seeds) (Fin (siteCapacity e sites seeds) × B))
        (f : Frame (BatchPorts q pat S d copies sites seeds ⊕ CableFields e A edges w)
          (Fin (edgeCapacity e edges seeds) ⊕ Raw B (siteCapacity e sites seeds) (edgeCapacity e edges seeds) w w)),
        BatchRows enum pat e S d home sf ∧ f.size ≤ (1+siteCapacity e sites seeds)*C*(d+1)^k +
          (cost e edges seeds w + 3*edgeCapacity e edges seeds) ∧
        ∀ (N : Pack D P bits K) (bin : N.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
          (lev : ℕ) (hl : lev+1=d+2*pat.depth) (g : Placement (m := m) N bin perm (Cube D) (SurfaceHost (Cube D) (lev+1)))
          (a : PublicPlacement pat S N bin perm lev g) (old : N.layout.Site ↪ Fin sites) (rows : N.layout.Edge ↪ Fin edges)
          (dummy : Fin (edgeCapacity e edges seeds) → SiteShape e N A)
          (geo : BatchPorts q pat S d copies sites seeds → Bool),
          PlacementReads N bin perm enum pat S home g a old seed.toEmbedding geo →
          ∀ (positive : N.layout.Edge → Bool) (first : Fin D × Bool) (hist : Counts e N bin perm)
            (c : CableFields e A edges w → Bool),
            SourceData e N bin perm positive old rows seed dummy first hist (Sum.elim (sf.eval geo) c) →
            SegmentReady (pat.nextSites e S) (output e N bin perm positive first hist).layout
              (siteRows e N old seed.toEmbedding) (outputRows e N bin perm positive first hist rows seed.toEmbedding)
              dummy (g.postSites N bin perm e positive hist) (segmentField enum (pat.nextSites e S) hl)
              (postMask N bin perm e positive hist) ((f.eval (Sum.elim geo c)) ∘ Sum.inr) ∧
            ∀ i, f.eval (Sum.elim geo c) (.inl i) = true ↔
              i ∈ Set.range (outputRows e N bin perm positive first hist rows seed.toEmbedding) := by
  obtain ⟨C,k,make⟩ := uniformOccupiedGeometry_frames enum pat e S
  exact ⟨C,k,make (A := A) (P := P) (bits := bits)⟩

set_option maxHeartbeats 1600000 in
/-- Uniform compiled transition from the copy, old-site, seed, interval and
histogram wires to the complete next-classifier input. The geometric batch is
charged once, the serializer once, and three additional gates per cable suffice. -/
theorem chargedGeometry_frames_of_reads (enum : Fin q ≃ Cube D) (pat : Pattern (Cube D) D)
    (e : PaidIdentity K D m) (S : Finset (HyperbolicHost (Cube D))) :
    ∃ C k : ℕ, ∀ (d : ℕ), 1 ≤ d → ∀ (copies sites edges seeds w : ℕ)
      (home : Fin sites → Fin copies) (seed : A ≃ Fin seeds),
      siteCapacity e sites seeds ≤ 2^w → edgeCapacity e edges seeds ≤ 2^w →
      let B := ProductSlots q (d+2*pat.depth) ⊕ ↥(pat.nextSites e S)
      ∃ (sf : Frame (BatchPorts q pat S d copies sites seeds) (Fin (siteCapacity e sites seeds) × B))
        (f : Frame (BatchPorts q pat S d copies sites seeds ⊕ CableFields e A edges w)
          (Raw B (siteCapacity e sites seeds) (edgeCapacity e edges seeds) w w)),
        BatchRows enum pat e S d home sf ∧ f.size ≤ (1+siteCapacity e sites seeds)*C*(d+1)^k +
          (cost e edges seeds w + 3*edgeCapacity e edges seeds) ∧
        ∀ (N : Pack D P bits K) (bin : N.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
          (lev : ℕ) (hl : lev+1=d+2*pat.depth) (g : Placement (m := m) N bin perm (Cube D) (SurfaceHost (Cube D) (lev+1)))
          (a : PublicPlacement pat S N bin perm lev g) (old : N.layout.Site ↪ Fin sites) (rows : N.layout.Edge ↪ Fin edges)
          (dummy : Fin (edgeCapacity e edges seeds) → SiteShape e N A)
          (geo : BatchPorts q pat S d copies sites seeds → Bool),
          PlacementReads N bin perm enum pat S home g a old seed.toEmbedding geo →
          ∀ (positive : N.layout.Edge → Bool) (first : Fin D × Bool) (hist : Counts e N bin perm)
            (c : CableFields e A edges w → Bool),
            SourceData e N bin perm positive old rows seed dummy first hist (Sum.elim (sf.eval geo) c) →
            SegmentReady (pat.nextSites e S) (output e N bin perm positive first hist).layout
              (siteRows e N old seed.toEmbedding) (outputRows e N bin perm positive first hist rows seed.toEmbedding)
              dummy (g.postSites N bin perm e positive hist) (segmentField enum (pat.nextSites e S) hl)
              (postMask N bin perm e positive hist) (f.eval (Sum.elim geo c)) := by
  obtain ⟨C,k,frames⟩ := occupiedGeometry_frames_of_reads (P := P) (bits := bits) (A := A) enum pat e S
  refine ⟨C,k,?_⟩
  intro d hd copies sites edges seeds w home seed hs he B
  obtain ⟨sf,f,hbatch,hsize,hr⟩ := frames d hd copies sites edges seeds w home seed hs he
  refine ⟨sf,f.select Sum.inr,hbatch,hsize,?_⟩
  intro N bin perm lev hl g a old rows dummy geo reads positive first hist c src
  have out := (hr N bin perm lev hl g a old rows dummy geo reads positive first hist c src).1
  have eq : (f.select Sum.inr).eval (Sum.elim geo c) = f.eval (Sum.elim geo c) ∘ Sum.inr :=
    funext fun _ => Frame.select_eval ..
  rwa [eq]

set_option maxHeartbeats 1600000 in
/-- Uniform compiled transition from the copy, old-site, seed, interval and
histogram wires to the complete next-classifier input. The geometric batch is
charged once, the serializer once, and three additional gates per cable suffice. -/
theorem chargedGeometry_frames (enum : Fin q ≃ Cube D) (pat : Pattern (Cube D) D)
    (e : PaidIdentity K D m) (S : Finset (HyperbolicHost (Cube D))) :
    ∃ C k : ℕ, ∀ (d : ℕ), 1 ≤ d → ∀ (copies sites edges seeds w : ℕ)
      (home : Fin sites → Fin copies) (seed : A ≃ Fin seeds),
      siteCapacity e sites seeds ≤ 2^w → edgeCapacity e edges seeds ≤ 2^w →
      let B := ProductSlots q (d+2*pat.depth) ⊕ ↥(pat.nextSites e S)
      ∃ (sf : Frame (BatchPorts q pat S d copies sites seeds) (Fin (siteCapacity e sites seeds) × B))
        (f : Frame (BatchPorts q pat S d copies sites seeds ⊕ CableFields e A edges w)
          (Raw B (siteCapacity e sites seeds) (edgeCapacity e edges seeds) w w)),
        BatchRows enum pat e S d home sf ∧ f.size ≤ (1+siteCapacity e sites seeds)*C*(d+1)^k +
          (cost e edges seeds w + 3*edgeCapacity e edges seeds) ∧
        ∀ (N : Pack D P bits K) (bin : N.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
          (lev : ℕ) (hl : lev+1=d+2*pat.depth) (g : Placement (m := m) N bin perm (Cube D) (SurfaceHost (Cube D) (lev+1)))
          (a : PublicPlacement pat S N bin perm lev g) (old : N.layout.Site ↪ Fin sites) (rows : N.layout.Edge ↪ Fin edges)
          (dummy : Fin (edgeCapacity e edges seeds) → SiteShape e N A)
          (pick : Fin copies → Fin pat.moves) (shift : Fin copies → Cube D → gamma 1),
          (∀ v, pick (home (old v)) = a.copyMotion v) → (∀ v, shift (home (old v)) = a.oldDeck v) →
          ∀ (positive : N.layout.Edge → Bool) (first : Fin D × Bool) (hist : Counts e N bin perm)
            (c : CableFields e A edges w → Bool),
            let geo := placementInput N bin perm enum pat S d lev g a old seed.toEmbedding pick shift
            SourceData e N bin perm positive old rows seed dummy first hist (Sum.elim (sf.eval geo) c) →
            SegmentReady (pat.nextSites e S) (output e N bin perm positive first hist).layout
              (siteRows e N old seed.toEmbedding) (outputRows e N bin perm positive first hist rows seed.toEmbedding)
              dummy (g.postSites N bin perm e positive hist) (segmentField enum (pat.nextSites e S) hl)
              (postMask N bin perm e positive hist) (f.eval (Sum.elim geo c)) := by
  obtain ⟨C,k,frames⟩ := chargedGeometry_frames_of_reads (P := P) (bits := bits) (A := A) enum pat e S
  refine ⟨C,k,?_⟩
  intro d hd copies sites edges seeds w home seed hs he B
  obtain ⟨sf,f,hbatch,hsize,hr⟩ := frames d hd copies sites edges seeds w home seed hs he
  refine ⟨sf,f,hbatch,hsize,?_⟩
  intro N bin perm lev hl g a old rows dummy pick shift hp hshift positive first hist c geo src
  exact hr N bin perm lev hl g a old rows dummy geo
    (placementInput_reads N bin perm enum pat S d lev g a old seed.toEmbedding pick shift home hp hshift)
    positive first hist c src

end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
