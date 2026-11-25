import OAI.Computability.BorderVNP.FiniteSewnFieldRunCount
import OAI.Computability.BorderVNP.FiniteSewnFieldLanes

/-! # Combining retained cable and free-word interval rows at a sewn site

Each unchanged physical cable has one affine interval. Each old grouped
port contributes its genuine local list of free, linked and zero intervals.
The source directory converts these word offsets to absolute old input
ordinals, including loop edges and zero-width words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open Crossing Inherited Diagonal.ExternalSew
open scoped BigOperators Classical

variable {D : ℕ} {A P U Free Cable : Type} [Fintype A] [Fintype P] [Fintype U] [Fintype Cable]
    {width : A → ℕ} (N : Network D A width) (lane : P ↪ Σ a, Fin (width a))
    {cw : Cable → ℕ} (B : Bundle (FineView.layout N lane) Free Cable cw)
    (gw : U → ℕ) (freeLane : Free ↪ Σ u, Fin (gw u)) (owner : U → N.Site)
    (aligned : ∀ f, owner (freeLane f).1 = B.layout.attach f)
    {ae ap be bp : ℕ} (oldEdge : N.Edge ↪ Fin ae) (oldPort : A ↪ Fin ap)
    (edge : (N.Edge ⊕ Cable) ↪ Fin be) (port : U ↪ Fin bp) (v : N.Site)

local notation "out" => Network.packExternal (Bundle.layout B) gw owner
local notation "ord" => sourceOrder N oldEdge oldPort v
local notation "read₀" => sewnRead N lane B gw freeLane owner aligned oldEdge oldPort edge port v

/-- The actual old physical wire occupies one interval at its new named sparse row. -/
noncomputable def wireInterval (e : Incident N v) : Interval :=
  ⟨wireStart N oldEdge oldPort v e,N.width e.val,
    some (wireStart out edge port v ⟨.inl e.val,e.property⟩)⟩

/-- Relocate an individual port's within-word interval to the actual old incidence ordinal. -/
def atOffset (start : ℕ) (p : Interval) : Interval := ⟨start+p.oldStart,p.width,p.source⟩

local notation "wr" => wireInterval N lane B gw owner oldEdge oldPort edge port v
local notation "pr" => portStart N oldEdge oldPort v

/-- A true per-port interval cover and the one-to-one old wire rows together
cover the entire source map of the exterior-sewn private program. -/
theorem covers_port_words (chunks : Attached N v → List Interval)
    (cover : ∀ p, Covers (chunks p) (fun k : Fin (width p.val) => read₀ (ord (.inr ⟨p,k⟩)))) :
    Covers ((Finset.univ.toList.map wr) ++ (Finset.univ.toList.flatMap fun p => (chunks p).map (atOffset (pr p)))) read₀ := by
  let list := (Finset.univ.toList.map wr) ++ (Finset.univ.toList.flatMap fun p => (chunks p).map (atOffset (pr p)))
  have mem (p : Interval) (hp : p ∈ list) : (∃ e, wr e = p) ∨
      ∃ a q, q ∈ chunks a ∧ atOffset (pr a) q = p := by
    simpa [list,List.mem_flatMap,List.mem_map] using hp
  have wire (e : Incident N v) (k : Fin (N.width e.val)) :
      (read₀ (ord (.inl ⟨e,k⟩))).map Fin.val = some ((wireStart out edge port v ⟨.inl e.val,e.property⟩)+k.val) := by
    simp only [sewnRead,Equiv.symm_apply_apply,sewnLane,Option.map_some]
    exact congrArg some (wireOrdinal out edge port v ⟨.inl e.val,e.property⟩ k)
  constructor
  · intro p hp
    rcases mem p hp with ⟨e,rfl⟩ | ⟨a,q,hq,rfl⟩
    · exact wireEnd_le N oldEdge oldPort v e
    · exact (Nat.add_assoc _ _ _).trans_le ((Nat.add_le_add_left ((cover a).oldFit q hq) _).trans
        (portEnd_le N oldEdge oldPort v a))
  · intro p hp j hj
    rcases mem p hp with ⟨e,rfl⟩ | ⟨a,q,hq,rfl⟩
    · cases hj
      exact wireEnd_le out edge port v ⟨.inl e.val,e.property⟩
    · exact (cover a).newFit q hq j hj
  · intro p hp i hi k hk
    rcases mem p hp with ⟨e,rfl⟩ | ⟨a,q,hq,rfl⟩
    · let j : Fin (N.width e.val) := ⟨i,hi⟩
      have eqn : k = ord (.inl ⟨e,j⟩) := Fin.ext (hk.trans (wireOrdinal N oldEdge oldPort v e j).symm)
      exact eqn ▸ wire e j
    · let j : Fin (width a.val) := ⟨q.oldStart+i,(Nat.add_lt_add_left hi _).trans_le ((cover a).oldFit q hq)⟩
      have eqn : k = ord (.inr ⟨a,j⟩) := Fin.ext
        (hk.trans ((Nat.add_assoc _ _ _).trans (portOrdinal N oldEdge oldPort v a j).symm))
      rw [eqn]
      exact (cover a).agrees q hq i hi j rfl
  · intro k
    obtain ⟨word,rfl⟩ := (ord).surjective k
    rcases word with ⟨e,j⟩ | ⟨a,j⟩
    · exact ⟨wr e,List.mem_append_left _ (List.mem_map.mpr ⟨e,by simp,rfl⟩),j.val,j.isLt,wireOrdinal N oldEdge oldPort v e j⟩
    · obtain ⟨q,hq,i,hi,eqn⟩ := (cover a).covers j
      refine ⟨atOffset (pr a) q,List.mem_append_right _ (List.mem_flatMap.mpr ⟨a,by simp,List.mem_map.mpr ⟨q,hq,rfl⟩⟩),i,hi,?_⟩
      exact (portOrdinal N oldEdge oldPort v a j).trans ((congrArg (pr a+·) eqn).trans (Nat.add_assoc ..).symm)

/-- The actual emitted canonical row count is bounded by one row per old
incident edge plus the exact sum of the old port interval counts. -/
theorem port_words_count (chunks : Attached N v → List Interval)
    (cover : ∀ p, Covers (chunks p) (fun k : Fin (width p.val) => read₀ (ord (.inr ⟨p,k⟩)))) :
    (intervals read₀).length ≤ Fintype.card (Incident N v) + ∑ p, (chunks p).length := by
  have h := intervals_length_le read₀ _ (covers_port_words N lane B gw freeLane owner aligned oldEdge oldPort edge port v chunks cover)
  simpa [List.length_flatMap,List.map_map,Function.comp_def,Finset.sum_toList] using h

end Packing.SewnField

end BorderVNP
end Computability
end OAI
