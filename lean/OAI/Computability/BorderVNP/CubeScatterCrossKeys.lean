import OAI.Computability.BorderVNP.CubeScatterPacketStreams
import Mathlib.Data.List.NodupEquivFin

/-! # Decoding arbitrary raw cut bits in physical packet order

A crossing stream visits every active bit in the chosen direction once. The
physical source order gives an equivalence between its raw positions and
its dependent cut lanes, including selectors with zero width on an edge.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Tally VPVNP.MotifBase

variable {n h K s : ℕ}

/-- One active bit of the chosen cut in a selected packet. -/
abbrev CrossLane (u : Selector n K h) (i : Fin (n+1)) (s : ℕ) :=
  Σ v : Vertex (n+1), Fin (payload (onEdge s) u.2 (v,i))

/-- The physical rectangular address of the cut lane. -/
def crossSlot (b : ℕ) (u : Selector n K h) (i : Fin (n+1)) (q : CrossLane u i s) : BodySlot n b h s :=
  .inr ((q.1,i),⟨q.2.val,q.2.isLt.trans_le (supplyWidth_le u (q.1,i) s)⟩)

/-- Decode the finite slot only when it is a selected bit in the chosen direction. -/
def crossKey {b : ℕ} (u : Selector n K h) (i : Fin (n+1)) : BodySlot n b h s → Option (CrossLane u i s)
  | .inl _ => none
  | .inr ((v,k),j) =>
    if k=i then if hj : j.val < payload (onEdge s) u.2 (v,i) then some ⟨v,⟨j.val,hj⟩⟩ else none else none

/-- The explicit slot map is the inverse of the successful key decoder. -/
theorem crossKey_iff {b : ℕ} (u : Selector n K h) (i : Fin (n+1)) (slot : BodySlot n b h s)
    (q : CrossLane u i s) : crossKey u i slot = some q ↔ slot = crossSlot b u i q := by
  constructor
  · cases slot with
    | inl _ => simp [crossKey]
    | inr a =>
      obtain ⟨⟨v,k⟩,j⟩ := a
      simp only [crossKey]
      split_ifs with hk hj
      · intro he
        obtain rfl := Option.some.inj he
        subst k
        rfl
      · simp
      · simp
  · rintro rfl
    cases q with
    | mk v j => simp [crossSlot,crossKey,j.isLt]

/-- The active cut lanes in the precise order in which the native body reads them. -/
def crossKeys (b : ℕ) (u : Selector n K h) (i : Fin (n+1)) (s : ℕ) : List (CrossLane u i s) :=
  (List.finRange (bodyWidth n b h s)).filterMap fun j => crossKey u i ((bodyOrder n b h s).symm j)

/-- Every selected-axis lane occurs in the raw crossing stream. -/
theorem crossKeys_mem (b : ℕ) (u : Selector n K h) (i : Fin (n+1)) (q : CrossLane u i s) :
    q ∈ crossKeys b u i s := by
  refine List.mem_filterMap.mpr ⟨bodyOrder n b h s (crossSlot b u i q),List.mem_finRange _,?_⟩
  exact (crossKey_iff u i _ q).mpr (Equiv.symm_apply_apply ..)

/-- The traversal uses one raw position per cut lane, without duplicates. -/
theorem crossKeys_nodup (b : ℕ) (u : Selector n K h) (i : Fin (n+1)) (s : ℕ) :
    (crossKeys b u i s).Nodup := by
  apply (List.pairwise_lt_finRange _).filterMap
  intro j k hj q hq q' hq' eq
  subst q'
  apply hj.ne
  apply (bodyOrder n b h s).symm.injective
  exact ((crossKey_iff u i _ q).mp hq).trans ((crossKey_iff u i _ q).mp hq').symm

/-- Reading the concrete supply assignment on the cut-lane list gives the exact native crossing stream. -/
theorem crossingStream_eq_keys (b : ℕ) (u : Selector n K h) (i : Fin (n+1))
    (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) :
    crossingStream b u i z = (crossKeys b u i s).map (fun q => z (q.1,i) q.2) := by
  rw [crossingStream,bodyPositions,List.ofFn_eq_map,List.filterMap_map,crossKeys,List.map_filterMap]
  apply List.filterMap_congr
  intro j _
  simp only [Function.comp_def]
  cases (bodyOrder n b h s).symm j with
  | inl q =>
    rcases q with ⟨e,k⟩
    simp only [ownedPosition,crossKey]
    split_ifs <;> rfl
  | inr q =>
    rcases q with ⟨⟨v,k⟩,a⟩
    by_cases hk : k=i
    · subst k
      simp only [ownedPosition,crossKey,ite_true]
      split_ifs <;> rfl
    · simp only [ownedPosition,crossKey,hk,ite_false]
      split_ifs <;> rfl

/-- The number of cut keys is exactly the selected payload. -/
theorem crossKeys_length (b : ℕ) (u : Selector n K h) (i : Fin (n+1)) (s : ℕ) :
    (crossKeys b u i s).length = ∑ v : Vertex (n+1), payload (onEdge s) u.2 (v,i) := by
  have h := crossingStream_length (s := s) b u i (fun _ _ => false)
  rw [crossingStream_eq_keys,List.length_map] at h
  exact h

/-- A word of exactly the declared cut length has one and only one assignment
to the active cut bits. Its inverse reads the index of the lane in the native traversal. -/
noncomputable def crossingEquiv (b : ℕ) (u : Selector n K h) (i : Fin (n+1)) (s : ℕ) :
    (CrossLane u i s → Bool) ≃ {xs : List Bool // xs.length = (crossKeys b u i s).length} := by
  classical
  let ks := crossKeys b u i s
  let ord := List.Nodup.getEquivOfForallMemList ks (crossKeys_nodup ..) (crossKeys_mem b u i)
  refine ⟨fun f => ⟨ks.map f,by simp [ks]⟩,
    fun xs q => xs.val[(ord.symm q).val]'(by rw [xs.property]; exact (ord.symm q).isLt),?_,?_⟩
  · intro f
    funext q
    simp only [List.getElem_map]
    exact congrArg f (ord.apply_symm_apply q)
  · intro xs
    apply Subtype.ext
    apply List.ext_getElem (by simp [ks,xs.property])
    intro j hj _
    have hlt : j < ks.length := by simpa using hj
    have eq : ord.symm (ks[j]) = ⟨j,hlt⟩ := ord.symm_apply_apply ⟨j,hlt⟩
    simp [eq]

/-- Encoding in the cut-word equivalence preserves the actual table's crossing order. -/
theorem crossingEquiv_encode (b : ℕ) (u : Selector n K h) (i : Fin (n+1))
    (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) :
    ((crossingEquiv b u i s) fun q => z (q.1,i) q.2).val = crossingStream b u i z :=
  (crossingStream_eq_keys ..).symm

end Cube.Scatter

end BorderVNP
end Computability
end OAI
