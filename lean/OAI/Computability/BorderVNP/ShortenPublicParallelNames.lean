import OAI.Computability.BorderVNP.ShortenPublicParallelFrame
import OAI.Computability.BorderVNP.PackedDenseNames

/-!
# Stable geometry and cable names across the disjoint union of packs

The public rectangles use the product ordering of copy and row. A hole in
the union belongs to exactly one child's rectangle and points at the very
same child dummy site. This remains true when the allocator internally
permutes its padded slots.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicParallel

open Cover PublicSegments PublicEndpoints PublicRelative Crossing Packing Packing.Names Epoch Catalog ParseBatchSort
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {copies V E w D lev : ℕ} {B : Type*} [Fintype B] {P : Type} {bits : P → ℕ} {R : Type*}

/-- Stable names for a sigma family of site or cable records. -/
def parallelName {X : Fin copies → Type*} (names : ∀ i, X i ↪ Fin V) :
    (Σ i, X i) ↪ Fin (copies*V) where
  toFun z := flat z.1 (names z.1 z.2)
  inj' := by
    rintro ⟨i,x⟩ ⟨j,y⟩ eq
    have h := finProdFinEquiv.injective eq
    obtain rfl : i=j := congrArg Prod.fst h
    obtain rfl : x=y := (names i).injective (congrArg Prod.snd h)
    rfl

/-- Occupancy of a global rectangle entry is exactly occupancy of the local row. -/
theorem parallelName_mem {X : Fin copies → Type*} (names : ∀ i, X i ↪ Fin V)
    (i : Fin copies) (r : Fin V) :
    flat i r ∈ Set.range (parallelName names) ↔ r ∈ Set.range (names i) := by
  constructor
  · rintro ⟨⟨j,v⟩,h⟩
    have hh := finProdFinEquiv.injective h
    obtain rfl : j=i := congrArg Prod.fst hh
    exact ⟨v,congrArg Prod.snd hh⟩
  · rintro ⟨v,rfl⟩
    exact ⟨⟨i,v⟩,rfl⟩

private noncomputable def slotNumber (n : ℕ) : Fin n ≃ Fin n :=
  (Fintype.equivFin (Fin n)).trans (finCongr (Fintype.card_fin n))

/-- Reserved site of the global padded slot. Undo the global slot permutation
before reading the child, then apply the local slot permutation. -/
noncomputable def parallelDummy {X : Fin copies → Type*} (dummy : ∀ i, Fin E → X i)
    (r : Fin (copies*E)) : Σ i, X i :=
  let z := finProdFinEquiv.symm (slotNumber _ r)
  ⟨z.1,dummy z.1 (rowSlot z.2)⟩

/-- The site behind a global hole is precisely the reserved site in its child. -/
theorem parallelDummy_slot {X : Fin copies → Type*} (dummy : ∀ i, Fin E → X i)
    (i : Fin copies) (r : Fin E) :
    parallelDummy dummy (rowSlot (flat i r)) = ⟨i,dummy i (rowSlot r)⟩ := by
  have h : slotNumber _ (rowSlot (flat i r)) = flat i r := (slotNumber _).apply_symm_apply _
  exact congrArg (fun z : Fin copies × Fin E => (⟨z.1,dummy z.1 (rowSlot z.2)⟩ : Σ i, X i))
    ((congrArg finProdFinEquiv.symm h).trans (unflat_flat i r))

variable (input : Fin copies → Pack D P bits R)
variable (sites : ∀ i, (input i).layout.Site ↪ Fin V) (rows : ∀ i, (input i).layout.Edge ↪ Fin E)
variable (dummy : ∀ i, Fin E → (input i).layout.Site)

private theorem stored_occupied {P' : Type*} {b' : P' → ℕ} (N : Network D P' b')
    (s : N.Site ↪ Fin V) (r : N.Edge ↪ Fin E) (pad : Fin E → N.Site)
    (e : N.Edge) (side : Bool) : storedSite N s r pad (r e) side = s (if side then N.src e else N.dst e) := by
  cases side
  · exact congrArg s (dst_slot N r pad e)
  · exact congrArg s (src_slot N r pad e)

private theorem stored_unused {P' : Type*} {b' : P' → ℕ} (N : Network D P' b')
    (s : N.Site ↪ Fin V) (r : N.Edge ↪ Fin E) (pad : Fin E → N.Site)
    (i : Fin E) (hi : i ∉ Set.range r) (side : Bool) : storedSite N s r pad i side = s (pad (rowSlot i)) := by
  cases side
  · exact congrArg s (unused_row N r pad i hi).2.1
  · exact congrArg s (unused_row N r pad i hi).1

/-- The parallel padded source or destination site is the child padded site at the exact global offset. -/
theorem storedSite_parallel (i : Fin copies) (r : Fin E) (side : Bool) :
    storedSite (parallelPacks input).layout (parallelName sites) (parallelName rows) (parallelDummy dummy) (flat i r) side =
      flat i (storedSite (input i).layout (sites i) (rows i) (dummy i) r side) := by
  by_cases h : r ∈ Set.range (rows i)
  · obtain ⟨u,rfl⟩ := h
    change storedSite _ _ _ _ (parallelName rows ⟨i,u⟩) side = _
    refine (stored_occupied (parallelPacks input).layout (parallelName sites) (parallelName rows) (parallelDummy dummy) ⟨i,u⟩ side).trans ?_
    refine Eq.trans ?_ (congrArg (flat i) (stored_occupied (input i).layout (sites i) (rows i) (dummy i) u side)).symm
    cases side <;> rfl
  · rw [stored_unused (parallelPacks input).layout (parallelName sites) (parallelName rows) (parallelDummy dummy)
      (flat i r) (fun hh => h ((parallelName_mem rows i r).mp hh)) side,
      stored_unused (input i).layout (sites i) (rows i) (dummy i) r h side,
      parallelDummy_slot]
    rfl

/-- Width at every global row, including a hole, is exactly the child row's width. -/
theorem storedWidth_parallel (i : Fin copies) (r : Fin E) :
    storedWidth (parallelPacks input).layout (parallelName rows) (parallelDummy dummy) (flat i r) =
      storedWidth (input i).layout (rows i) (dummy i) r := by
  by_cases h : r ∈ Set.range (rows i)
  · obtain ⟨u,rfl⟩ := h
    exact (width_slot (parallelPacks input).layout (parallelName rows) (parallelDummy dummy) ⟨i,u⟩).trans
      (width_slot (input i).layout (rows i) (dummy i) u).symm
  · exact (unused_row (parallelPacks input).layout (parallelName rows) (parallelDummy dummy) (flat i r)
      (fun hh => h ((parallelName_mem rows i r).mp hh))).2.2.trans ((unused_row (input i).layout (rows i) (dummy i) r h).2.2.symm)

/-- The global public arrays preserve the complete actual parallel layout,
all opaque payload fields, live masks, false hole masks and local geometric
catalogs. The only width condition concerns the size of the combined site IDs. -/
theorem merge_ready {S : Finset (HyperbolicHost (Cube D))}
    (pos : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (lev+1))
    (field : FieldBit (↥S) (Cube D) (lev+1) → B) (mask : ∀ i, (input i).layout.Edge → Bool)
    (x : Fin copies → Raw B V E w w → Bool)
    (hchild : ∀ i, SegmentReady S (input i).layout (sites i) (rows i) (dummy i) (pos i) field (mask i) (x i))
    (fit : copies*V ≤ 2^w) {f : Frame (Fin copies × Raw B V E w w) (Raw B (copies*V) (copies*E) w w)}
    (merge : MergeRows f) :
    SegmentReady S (parallelPacks input).layout (parallelName sites) (parallelName rows) (parallelDummy dummy)
      (fun v => pos v.1 v.2) field (fun c => mask c.1 c.2) (f.eval fun z => x z.1 z.2) := by
  let z : Fin copies × Raw B V E w w → Bool := fun t => x t.1 t.2
  refine ⟨fun v => (hchild v.1).valid v.2,⟨?_,?_⟩,?_,?_,?_⟩
  · intro j side
    obtain ⟨⟨i,r⟩,rfl⟩ := finProdFinEquiv.surjective j
    change address ((f.eval z) ∘ Sum.inr) (flat i r) side = _
    let v := storedSite (input i).layout (sites i) (rows i) (dummy i) r side
    have hloc : address (fun b => z (i,.inr b)) r side = v.val := (hchild i).names.addresses r side
    have hbound : v.val + V*i.val < 2^w := (flat i v).isLt.trans_le fit
    refine (merge.address z i r side (hloc ▸ hbound)).trans ?_
    rw [hloc]
    exact (congrArg Fin.val (storedSite_parallel input sites rows dummy i r side)).symm
  · intro j
    obtain ⟨⟨i,r⟩,rfl⟩ := finProdFinEquiv.surjective j
    change value (fun b => f.eval z (.inr (.inr (flat i r,.inl b)))) = _
    simp only [merge.width,z]
    exact ((hchild i).names.widths r).trans (storedWidth_parallel input rows dummy i r).symm
  · rintro ⟨i,v⟩ j
    exact (merge.site z i (sites i v) (field j)).trans ((hchild i).payload v j)
  · rintro ⟨i,e⟩
    exact (merge.mask z i (rows i e)).trans ((hchild i).charge e)
  · intro j hj
    obtain ⟨⟨i,r⟩,rfl⟩ := finProdFinEquiv.surjective j
    exact (merge.mask z i r).trans ((hchild i).hole r (fun hh => hj ((parallelName_mem rows i r).mpr hh)))

end Shortening.PublicParallel

end BorderVNP
end Computability
end OAI
