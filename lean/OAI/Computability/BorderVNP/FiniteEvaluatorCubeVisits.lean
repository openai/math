import OAI.Computability.BorderVNP.CubeISAOwnedVertexReadout
import OAI.Computability.BorderVNP.CubeTeamRowFold

/-! # The actual packet and vertex ordinals of a native team directory

Strict grouping rows enumerate dense successful packet-trial ranks followed
by the local half-cube vertex rank. The team's square traversal keeps exactly
the directed rows whose first symbol it owns. A co-located pair visits the
two disjoint half-cubes in their corresponding ordered rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeVisits

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Physical.Owned
open BorderVNP.Cube.Physical.VertexIndex RoutingISA.OwnedVertex
open scoped Classical

variable {n d : ℕ}

/-- Number of successfully decoded packet trials on a strict symbol pair. -/
def packets (n d blocks : ℕ) := 2*blocks*(d.choose 2)^n

/-- Chronological dense packet rank of the executable row, in both directions. -/
noncomputable def packet (axis : Fin (n+1)) (pair : Symbols d) (blocks : ℕ) :
    Fin (packets n d blocks) ≃ {p : Packet n d blocks // p.1.1 axis=pair} :=
  (densePacketEquiv axis pair).symm.trans (packetRowEquiv axis pair)

private def vertexPair (axis : Fin (n+1)) (high : Bool) {blocks : ℕ} (p : Packet n d blocks) (j : Fin (2^n)) :=
  (p,(owned p axis high j).val)

private noncomputable def atPair (axis : Fin (n+1)) (pair : Symbols d) (high : Bool) (blocks : ℕ)
    (xy : Fin (packets n d blocks) × Fin (2^n)) :=
  vertexPair axis high (packet axis pair blocks xy.1).val xy.2

/-- The emitted triple at a fixed compact packet/vertex rank. -/
noncomputable def atRank (axis : Fin (n+1)) (pair : Symbols d) (high : Bool) (blocks : ℕ)
    (i : Fin (packets n d blocks * 2^n)) : Packet n d blocks × Vertex (n+1) :=
  atPair axis pair high blocks (finProdFinEquiv.symm i)

private theorem at_coordinates (axis : Fin (n+1)) (pair : Symbols d) (high : Bool) (blocks : ℕ)
    (x : Fin (packets n d blocks)) (u : Fin (2^n)) :
    atRank axis pair high blocks (finProdFinEquiv (x,u)) = vertexPair axis high (packet axis pair blocks x).val u := by
  unfold atRank
  rw [Equiv.symm_apply_apply]
  rfl

/-- The exact fixed-length list appended by the strict native vertex emitter. -/
noncomputable def row (axis : Fin (n+1)) (pair : Symbols d) (high : Bool) (blocks : ℕ) :
    List (Packet n d blocks × Vertex (n+1)) := List.ofFn (atRank axis pair high blocks)

/-- Recover the genuine local rank from a packet and vertex in this directed row. -/
noncomputable def rank (axis : Fin (n+1)) (pair : Symbols d) (high : Bool) (blocks : ℕ)
    (p : Packet n d blocks) (v : Vertex (n+1)) (hp : p.1.1 axis = pair)
    (hv : vertexLabel p v axis = groupSymbol p axis high) : Fin (packets n d blocks * 2^n) :=
  finProdFinEquiv ((packet axis pair blocks).symm ⟨p,hp⟩,(owned p axis high).symm ⟨v,hv⟩)

private theorem at_rank (axis : Fin (n+1)) (pair : Symbols d) (high : Bool) (blocks : ℕ)
    (p : Packet n d blocks) (v : Vertex (n+1)) (hp : p.1.1 axis = pair)
    (hv : vertexLabel p v axis = groupSymbol p axis high) :
    atRank axis pair high blocks (rank axis pair high blocks p v hp hv) = (p,v) := by
  unfold rank
  rw [at_coordinates,(packet axis pair blocks).apply_symm_apply,vertexPair,(owned p axis high).apply_symm_apply]

/-- This local list contains the true vertex exactly on its packet's grouping
pair and the selected side, regardless of the orientation bit. -/
theorem mem_row (axis : Fin (n+1)) (pair : Symbols d) (high : Bool) (blocks : ℕ)
    (pv : Packet n d blocks × Vertex (n+1)) :
    pv ∈ row axis pair high blocks ↔ pv.1.1.1 axis=pair ∧ vertexLabel pv.1 pv.2 axis=groupSymbol pv.1 axis high := by
  rw [row,List.mem_ofFn]
  constructor
  · rintro ⟨i,rfl⟩
    let parts := finProdFinEquiv.symm i
    let p := packet axis pair blocks parts.1
    exact ⟨p.property,(owned p.val axis high parts.2).property⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨_,at_rank axis pair high blocks pv.1 pv.2 h₁ h₂⟩

theorem row_nodup (axis : Fin (n+1)) (pair : Symbols d) (high : Bool) (blocks : ℕ) :
    (row axis pair high blocks).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  -- Reindex the source indices by the actual product order used by the loop.
  obtain ⟨i',rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨j',rfl⟩ := finProdFinEquiv.surjective j
  rcases i' with ⟨x,u⟩; rcases j' with ⟨y,v⟩
  rw [at_coordinates,at_coordinates] at hij
  simp only [vertexPair,Prod.mk.injEq] at hij
  obtain ⟨px,pv⟩ := hij
  obtain rfl : x=y := (packet axis pair blocks).injective (Subtype.ext px)
  obtain rfl : u=v := (owned _ axis high).injective (Subtype.ext pv)
  rfl

/-- The unique ordered grouping pair assigned to the given packet vertex. -/
def key (axis : Fin (n+1)) {blocks : ℕ} (pv : Packet n d blocks × Vertex (n+1)) : Fin d × Fin d :=
  if cornerBits pv.1 pv.2 axis then (pv.1.1.1 axis).val.swap else (pv.1.1.1 axis).val

theorem key_fst (axis : Fin (n+1)) {blocks : ℕ} (pv : Packet n d blocks × Vertex (n+1)) :
    (key axis pv).1 = vertexLabel pv.1 pv.2 axis := by simp [key,vertexLabel]; split <;> rfl

private theorem key_pair (axis : Fin (n+1)) (pair : Symbols d) (high : Bool) {blocks : ℕ}
    (pv : Packet n d blocks × Vertex (n+1)) :
    key axis pv = (if high then pair.val.swap else pair.val) ↔
      pv.1.1.1 axis=pair ∧ vertexLabel pv.1 pv.2 axis = groupSymbol pv.1 axis high := by
  let z := pv.1.1.1 axis
  change (if cornerBits pv.1 pv.2 axis then z.val.swap else z.val) = (if high then pair.val.swap else pair.val) ↔
    z=pair ∧ (if cornerBits pv.1 pv.2 axis then z.val.2 else z.val.1) = (if high then z.val.2 else z.val.1)
  have zlt := z.property
  have plt := pair.property
  cases hb : cornerBits pv.1 pv.2 axis <;> cases high <;> simp only [Bool.false_eq_true,ite_false,ite_true, and_true]
  · exact Subtype.val_inj
  · constructor
    · intro e
      have bad := congrArg (fun v : Fin d × Fin d => v.1<v.2) e
      change (z.val.1 < z.val.2) = (pair.val.2 < pair.val.1) at bad
      exact (plt.not_gt (bad.mp zlt)).elim
    · exact fun hh => (zlt.ne hh.2).elim
  · constructor
    · intro e
      have bad := congrArg (fun v : Fin d × Fin d => v.1<v.2) e
      change (z.val.2 < z.val.1) = (pair.val.1 < pair.val.2) at bad
      exact (zlt.not_gt (bad.mpr plt)).elim
    · exact fun hh => (zlt.ne hh.2.symm).elim
  · exact Prod.swap_injective.eq_iff.trans Subtype.val_inj

/-- The actual two possible strict emitter roles, with no vertices on a diagonal row. -/
noncomputable def orderedRow (axis : Fin (n+1)) (blocks : ℕ) (lo hi : Fin d) : List (Packet n d blocks × Vertex (n+1)) :=
  if h : lo<hi then row axis ⟨(lo,hi),h⟩ false blocks
  else if h : hi<lo then row axis ⟨(hi,lo),h⟩ true blocks else []

/-- Each emitted vertex has precisely this ordered pair of grouping symbols. -/
theorem mem_orderedRow (axis : Fin (n+1)) (blocks : ℕ) (lo hi : Fin d)
    (pv : Packet n d blocks × Vertex (n+1)) :
    pv ∈ orderedRow axis blocks lo hi ↔ key axis pv = (lo,hi) := by
  rcases lt_trichotomy lo hi with less | rfl | greater
  · rw [orderedRow,dite_eq_left less,mem_row]
    exact (key_pair axis ⟨(lo,hi),less⟩ false pv).symm
  · simp only [orderedRow,lt_self_iff_false,dite_false,List.not_mem_nil,false_iff]
    intro h
    have diff : (key axis pv).1 ≠ (key axis pv).2 := by
      unfold key; split
      · exact (pv.1.1.1 axis).property.ne.symm
      · exact (pv.1.1.1 axis).property.ne
    exact diff ((congrArg Prod.fst h).trans (congrArg Prod.snd h).symm)
  · rw [orderedRow,dite_eq_right greater.not_gt,dite_eq_left greater,mem_row]
    exact (key_pair axis ⟨(hi,lo),greater⟩ true pv).symm

private theorem ordered_nodup (axis : Fin (n+1)) (blocks : ℕ) (lo hi : Fin d) :
    (orderedRow axis blocks lo hi).Nodup := by unfold orderedRow; split <;> first | exact row_nodup .. | (split <;> first | exact row_nodup .. | exact List.nodup_nil)

end FiniteEvaluator.CubeVisits

end BorderVNP
end Computability
end OAI
