import OAI.Computability.BorderVNP.PackedInheritedPieces
import OAI.Computability.BorderVNP.PackedInheritedStaging

/-! # Exact coverage by the inherited sparse layer

The real interval starts stay inside both generations of incidence words,
every emitted lane reads its specified physical successor, and every old
input bit belongs to a row. This discharges the coverage premise of the
unique-staging calculation for the concrete combining operation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.SeedIntervals Shortening.CombiningStep
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
variable {S : Type} [Fintype S] (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (binName : S → ℕ) (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
variable (v : p.layout.Site)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable {old next np : ℕ} (oldID : p.layout.Edge ↪ Fin old) (nextID : (G e p bin perm positive first q).Edge ↪ Fin next) (portID : P ↪ Fin np)
local notation3 "G₀" => G e p bin perm positive first q
local notation3 "rows₀" => layerSlice e p bin perm binName positive first q v oldID nextID portID
local notation3 "cuts₀" => layerCuts e p bin perm binName positive first q v oldID nextID portID
local notation3 "read₀" => layerRead e p bin perm positive first q v oldID nextID portID
local notation3 "old₀" => sourceOrder p.layout oldID portID v
local notation3 "new₀" => sourceOrder G₀ nextID portID (.inl v)
local notation3 "d₀" => priorDescriptor (m := m) p bin perm binName

private theorem row_limits (r : LayerRow p v) :
    (rows₀ r).oldStart + (rows₀ r).width ≤ incoming p.layout v ∧
      (rows₀ r).newStart + (rows₀ r).width ≤ incoming G₀ (.inl v) := by
  rcases r with ⟨z,b⟩ | u
  · let z' := oldBandWire e p bin perm positive first q v z b
    have h := priorEnd (m := m) p bin perm binName v z b
    have ho := wireEnd_le p.layout oldID portID v z
    have hn := wireEnd_le G₀ nextID portID (.inl v) z'
    have hw : (G₀).width z'.val = (d₀ z.val b).span :=
      (oldBandWire_width e p bin perm positive first q v z b).trans (priorSpan (m := m) p bin perm binName v z b)
    change wireStart p.layout oldID portID v z + (d₀ z.val b).localStart + (d₀ z.val b).span ≤ _ ∧
      wireStart G₀ nextID portID (.inl v) z' + (d₀ z.val b).span ≤ _
    refine ⟨?_, hw ▸ hn⟩
    exact (Nat.add_assoc _ _ _).le.trans ((Nat.add_le_add_left h _).trans ho)
  · exact ⟨portEnd_le p.layout oldID portID v u,portEnd_le G₀ nextID portID (.inl v)
      (portOfOld e p bin perm positive first q v u)⟩

private theorem band_ordinal (z : Incident p.layout v) (b : Band D)
    (k : Fin ((layout p.layout bin perm m).width (z.val,b))) :
    let kOld := old₀ (.inl ⟨z,(p.layout.bandOrder (label p.layout bin perm m) z.val b k).val⟩)
    kOld.val = (rows₀ (.inl (z,b))).oldStart+k.val ∧
      (read₀ kOld).val = (rows₀ (.inl (z,b))).newStart+k.val := by
  intro kOld
  constructor
  · rw [show kOld.val = _ from wireOrdinal p.layout oldID portID v z _,priorOrdinal (m := m) p bin perm binName]
    exact (Nat.add_assoc _ _ _).symm
  · change (new₀ (laneOfOld e p bin perm positive first q v ((old₀).symm (old₀ _)))).val = _
    rw [Equiv.symm_apply_apply,lane_band]
    exact wireOrdinal G₀ nextID portID (.inl v) (oldBandWire e p bin perm positive first q v z b)
      (Fin.cast (oldBandWire_width e p bin perm positive first q v z b).symm k)

private theorem row_lane (r : LayerRow p v) (i : Fin ((rows₀ r).width)) :
    ∃ k : Fin (incoming p.layout v), k.val = (rows₀ r).oldStart+i.val ∧
      (read₀ k).val = (rows₀ r).newStart+i.val := by
  rcases r with ⟨z,b⟩ | u
  · let j := Fin.cast (priorSpan (m := m) p bin perm binName v z b).symm i
    exact ⟨_,band_ordinal e p bin perm binName positive first q v oldID nextID portID z b j⟩
  · let k := old₀ (.inr ⟨u,i⟩)
    refine ⟨k,portOrdinal p.layout oldID portID v u i,?_⟩
    change (new₀ (laneOfOld e p bin perm positive first q v ((old₀).symm (old₀ (.inr ⟨u,i⟩))))).val = _
    rw [Equiv.symm_apply_apply]
    exact portOrdinal G₀ nextID portID (.inl v) (portOfOld e p bin perm positive first q v u) i

/-- The genuine sparse intervals of this retained site cover exactly its named old
incidence lanes in the two virtual address arrays, for every histogram branch. -/
theorem layer_covers : Covers (incoming p.layout v) (incoming G₀ (.inl v)) cuts₀ read₀ := by
  have hm {x : Slice} : x ∈ cuts₀ ↔ ∃ r, x = rows₀ r :=
    mem_layerCuts e p bin perm binName positive first q v oldID nextID portID
  have lim := row_limits e p bin perm binName positive first q v oldID nextID portID
  have hold : ∀ s ∈ cuts₀, s.oldStart+s.width ≤ incoming p.layout v := by
    intro s hs
    obtain ⟨r,rfl⟩ := hm.mp hs
    exact (lim r).1
  have hnew : ∀ s ∈ cuts₀, s.newStart+s.width ≤ incoming G₀ (.inl v) := by
    intro s hs
    obtain ⟨r,rfl⟩ := hm.mp hs
    exact (lim r).2
  refine ⟨hold,hnew,?_,?_⟩
  · intro s hs i
    obtain ⟨r,rfl⟩ := (hm.mp hs)
    obtain ⟨k,hk,hn⟩ := row_lane e p bin perm binName positive first q v oldID nextID portID r i
    exact (congrArg (fun x => (read₀ x).val) (Fin.ext hk).symm).trans hn
  · intro k
    obtain ⟨(⟨z,i⟩ | ⟨u,i⟩),rfl⟩ := (old₀).surjective k
    · obtain ⟨⟨b,j⟩,rfl⟩ := (p.layout.bandIndex (label p.layout bin perm m) z.val).surjective i
      let r : LayerRow p v := .inl (z,b)
      refine ⟨rows₀ r,hm.mpr ⟨r,rfl⟩,Fin.cast (priorSpan (m := m) p bin perm binName v z b) j,?_⟩
      exact (band_ordinal e p bin perm binName positive first q v oldID nextID portID z b j).1.symm
    · let r : LayerRow p v := .inr u
      exact ⟨rows₀ r,hm.mpr ⟨r,rfl⟩,i,(portOrdinal p.layout oldID portID v u i).symm⟩

end Packing.Inherited

end BorderVNP
end Computability
end OAI
