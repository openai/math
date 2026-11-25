import OAI.Computability.BorderVNP.PackedInheritedAddresses
import OAI.Computability.BorderVNP.PackedInheritedState
import OAI.Computability.BorderVNP.ShortenSeedDescriptorFrozen

/-! # Physical interval list for a retained site

Each original cable contributes its compressed bands, using the chosen
source or destination hook when cut. A loop uses the source hook once.
Each attached exterior port contributes one intact interval. Both endpoints
of a slice are stable local addresses in consecutive incidence generations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.SeedIntervals Shortening.CombiningStep
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P A : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
variable {S : Type} [Fintype S] (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (binName : S → ℕ) (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
private noncomputable abbrev G := (output e p bin perm positive first q).layout

/-- The clipped descriptor actually emitted for a charged or uncharged old cable. -/
noncomputable def priorDescriptor (z : p.layout.Edge) (b : Band D) : CutDescriptor :=
  match h : bin z with
  | none => frozenDescriptor p.layout 0 z b
  | some c => descriptor p.layout bin perm m binName (⟨z,h⟩ : {u // bin u = some c}) b

variable (v : p.layout.Site) (z : Incident p.layout v) (b : Band D)

omit [Fintype P] [Fintype S] [Field K] in
/-- The emitted interval width is exactly the live physical band width. -/
theorem priorSpan : (layout p.layout bin perm m).width (z.val,b) = (priorDescriptor (m := m) p bin perm binName z.val b).span := by
  unfold priorDescriptor
  split
  · rename_i h
    exact frozen_width p.layout bin perm m 0 z.val h b
  · rename_i c h
    exact descriptor_width p.layout bin perm m binName (⟨z.val,h⟩ : {u // bin u = some c}) b

omit [Fintype P] [Fintype S] [Field K] in
/-- Clipping preserves the public within-cable order, including empty frozen bands. -/
theorem priorOrdinal (k : Fin ((layout p.layout bin perm m).width (z.val,b))) :
    ((p.layout.bandOrder (label p.layout bin perm m) z.val b k).val).val =
      (priorDescriptor (m := m) p bin perm binName z.val b).localStart+k.val := by
  unfold priorDescriptor
  split
  · rename_i h
    cases b with
    | none => simpa [frozenDescriptor,CutDescriptor.localStart,cutOffset] using frozen_oldBit p.layout bin perm m z.val h k
    | some u =>
      have hk := k.isLt.trans_eq (frozen_width p.layout bin perm m 0 z.val h (some u))
      simp [frozenDescriptor,CutDescriptor.span,overlapWidth,cutOffset] at hk
  · rename_i c h
    exact bandOrder_eq_oldBit p.layout bin perm m binName (⟨z.val,h⟩ : {u // bin u = some c}) b k

omit [Fintype P] [Fintype S] [Field K] in
/-- The end of a clipped descriptor fits even if its band is empty. -/
theorem priorEnd :
    let row := priorDescriptor (m := m) p bin perm binName z.val b
    row.localStart+row.span ≤ p.layout.width z.val := by
  intro row
  have hw : row.width = p.layout.width z.val := by dsimp only [row,priorDescriptor]; split <;> rfl
  rw [← hw]
  simp only [CutDescriptor.localStart,CutDescriptor.span,overlapWidth,cutOffset]
  omega

variable {old next np : ℕ} (oldID : p.layout.Edge ↪ Fin old)
variable (nextID : (G e p bin perm positive first q).Edge ↪ Fin next) (portID : P ↪ Fin np)

/-- All compact equality rows of the site: one per incident cable band and one per attached port. -/
abbrev LayerRow := (Incident p.layout v × Band D) ⊕ Attached p.layout v

/-- Exterior attachments are inherited by the same old fine site. -/
def portOfOld (u : Attached p.layout v) : Attached (G e p bin perm positive first q) (.inl v) :=
  ⟨u.val,congrArg Sum.inl u.property⟩

/-- Public interval between the exact old and successor incidence arrays. -/
noncomputable def layerSlice : LayerRow p v → Slice
  | .inl (z,b) =>
    let d := priorDescriptor (m := m) p bin perm binName z.val b
    ⟨wireStart p.layout oldID portID v z + d.localStart,
      wireStart (G e p bin perm positive first q) nextID portID (.inl v)
        (oldBandWire e p bin perm positive first q v z b),d.span⟩
  | .inr u =>
    ⟨portStart p.layout oldID portID v u,portStart (G e p bin perm positive first q) nextID portID
      (.inl v) (portOfOld e p bin perm positive first q v u),bits u.val⟩

/-- The lane in the new physical array which the old tensor table reads. -/
noncomputable def laneOfOld : InputLane p.layout v → InputLane (G e p bin perm positive first q) (.inl v)
  | .inl ⟨z,k⟩ =>
    let u := (p.layout.bandIndex (label p.layout bin perm m) z.val).symm k
    .inl ⟨oldBandWire e p bin perm positive first q v z u.1,Fin.cast
      (oldBandWire_width e p bin perm positive first q v z u.1).symm u.2⟩
  | .inr ⟨u,k⟩ => .inr ⟨portOfOld e p bin perm positive first q v u,k⟩

omit [Fintype P] in
/-- The physical source selected at a specific compressed band is exactly that successor cable and lane. -/
theorem lane_band (k : Fin ((layout p.layout bin perm m).width (z.val,b))) :
    laneOfOld e p bin perm positive first q v (.inl ⟨z,(p.layout.bandOrder (label p.layout bin perm m) z.val b k).val⟩) =
      .inl ⟨oldBandWire e p bin perm positive first q v z b,
        Fin.cast (oldBandWire_width e p bin perm positive first q v z b).symm k⟩ := by
  let E := p.layout.bandIndex (label p.layout bin perm m) z.val
  let g (u : Σ b : Band D, Fin ((layout p.layout bin perm m).width (z.val,b))) :
      InputLane (G e p bin perm positive first q) (.inl v) :=
    .inl ⟨oldBandWire e p bin perm positive first q v z u.1,
      Fin.cast (oldBandWire_width e p bin perm positive first q v z u.1).symm u.2⟩
  exact congrArg g (E.symm_apply_apply ⟨b,k⟩)

/-- The physical reconstruction map between flattened incidence words. -/
noncomputable def layerRead : Fin (incoming p.layout v) → Fin (incoming (G e p bin perm positive first q) (.inl v)) :=
  (sourceOrder (G e p bin perm positive first q) nextID portID (.inl v)) ∘
    (laneOfOld e p bin perm positive first q v) ∘ (sourceOrder p.layout oldID portID v).symm

/-- The whole compressed interval table of a retained site. -/
noncomputable def layerCuts : List Slice :=
  List.ofFn fun i : Fin (Fintype.card (LayerRow p v)) =>
    layerSlice e p bin perm binName positive first q v oldID nextID portID ((Fintype.equivFin _).symm i)

/-- Every actual old-site row occurs in this table, and all table rows come from such a physical interval. -/
theorem mem_layerCuts {x : Slice} :
    x ∈ layerCuts e p bin perm binName positive first q v oldID nextID portID ↔
      ∃ r, x = layerSlice e p bin perm binName positive first q v oldID nextID portID r := by
  simp only [layerCuts,List.mem_ofFn]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨_,rfl⟩
  · rintro ⟨r,rfl⟩
    exact ⟨Fintype.equivFin _ r,by simp⟩

end Packing.Inherited

end BorderVNP
end Computability
end OAI
