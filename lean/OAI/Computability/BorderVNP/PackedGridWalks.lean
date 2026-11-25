import OAI.Computability.BorderVNP.PackedGridCells
import OAI.Computability.BorderVNP.CoverLorentzSubdivisionRecords
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! # Realizing host-graph walks as physical cable routes

The ordered vertices of each walk become equality boxes. Its first and last
boxes share the endpoint cell, so those two extra hops never add cross-cell load.
The same visit count controls the private equality records retained in a cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.WalkLayout

open BorderVNP.Crossing BorderVNP.Shortening Finset SimpleGraph
open scoped Classical
variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {G : Type} (graph : SimpleGraph G) (place : N.Site → G)
variable (walk : ∀ e : N.Edge, graph.Walk (place (N.src e)) (place (N.dst e)))
variable (position : G → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- One inserted equality box for every ordered vertex in the physical route. -/
abbrev routes : N.WireRoutes where
  interior e := (walk e).length + 1
  place e i := position ((walk e).getVert i.val)

/-- Old sites retain their placement. Equality sites are placed at the visited tiles. -/
abbrev cells : (N.subdivide (routes N graph place walk position)).Site → G :=
  Sum.elim place (fun p => (walk p.1).getVert p.2.val)

/-- Each vertex is counted with its multiplicity in the ordered walk. -/
theorem sum_vertex_hits {s t : G} (w : graph.Walk s t) (g : G) :
    (∑ i : Fin (w.length+1), if w.getVert i.val = g then 1 else 0) = w.support.count g := by
  induction w with
  | @nil u =>
    change (∑ _ : Fin 1, if u = g then 1 else 0) = [u].count g
    rw [Fin.sum_univ_one]
    by_cases hu : u = g <;> simp [hu]
  | @cons x y z h w ih =>
    rw [Walk.length_cons, Fin.sum_univ_succ]
    change (if x = g then 1 else 0) + (∑ i : Fin (w.length+1), if w.getVert i.val = g then 1 else 0) =
      (x :: w.support).count g
    rw [ih,List.count_cons,add_comm]
    simp

/-- At a fixed cell, the crossing load omits all same-cell wires. -/
private theorem crossing_eq {C : Type} (c : N.Site → C) (v : C) :
    N.crossingLoad c v =
      ∑ e, if c (N.src e) ≠ c (N.dst e) then
        if c (N.src e) = v then N.width e else 0 else 0 := by
  unfold Network.crossingLoad
  symm
  rw [← sum_filter]
  exact sum_subtype _ (fun _ => by simp) _

private abbrev hopSrc (e : N.Edge) (i : Fin ((walk e).length+2)) :=
  cells N graph place walk position ((N.subdivide (routes N graph place walk position)).src ⟨e,i⟩)

private abbrev hopDst (e : N.Edge) (i : Fin ((walk e).length+2)) :=
  cells N graph place walk position ((N.subdivide (routes N graph place walk position)).dst ⟨e,i⟩)

private theorem src_zero (e : N.Edge) : hopSrc N graph place walk position e 0 = place (N.src e) :=
  rfl

private theorem src_succ (e : N.Edge) (i : Fin ((walk e).length+1)) :
    hopSrc N graph place walk position e i.succ = (walk e).getVert i.val := by
  change cells N graph place walk position ((N.subdivide (routes N graph place walk position)).src ⟨e,i.succ⟩) =
    cells N graph place walk position (.inr ⟨e,i⟩)
  apply congrArg
  simp only [Network.subdivide, Fin.cases_succ]

private theorem dst_cast (e : N.Edge) (i : Fin ((walk e).length+1)) :
    hopDst N graph place walk position e i.castSucc = (walk e).getVert i.val := by
  change cells N graph place walk position ((N.subdivide (routes N graph place walk position)).dst ⟨e,i.castSucc⟩) =
    cells N graph place walk position (.inr ⟨e,i⟩)
  apply congrArg
  simp only [Network.subdivide, Fin.lastCases_castSucc]

private theorem dst_last (e : N.Edge) :
    hopDst N graph place walk position e (Fin.last ((walk e).length+1)) = place (N.dst e) := by
  change cells N graph place walk position ((N.subdivide (routes N graph place walk position)).dst ⟨e,(Fin.last ((walk e).length+1))⟩) =
    cells N graph place walk position (.inl (N.dst e))
  apply congrArg
  simp only [Network.subdivide, Fin.lastCases_last]

private theorem dst_zero (e : N.Edge) : hopDst N graph place walk position e 0 = place (N.src e) :=
  (dst_cast N graph place walk position e 0).trans (walk e).getVert_zero

/-- The outgoing cross-cell width is at most the width-weighted number of actual visits. -/
theorem crossingLoad_le (g : G) :
    (N.subdivide (routes N graph place walk position)).crossingLoad
      (cells N graph place walk position) g ≤ ∑ e, N.width e * (walk e).support.count g := by
  rw [crossing_eq]
  erw [Fintype.sum_sigma]
  apply sum_le_sum
  intro e _
  rw [← sum_vertex_hits graph, mul_sum]
  change (∑ i : Fin ((walk e).length+2), if hopSrc N graph place walk position e i ≠
    hopDst N graph place walk position e i then if hopSrc N graph place walk position e i = g then N.width e else 0
    else 0) ≤ _
  rw [Fin.sum_univ_succ, src_zero, dst_zero]
  simp only [ne_self_iff_false,ite_false,zero_add,src_succ]
  apply sum_le_sum
  intro i _
  by_cases hv : (walk e).getVert i.val = g <;> simp [hv]
  split <;> omega

/-- Every actual crossing hop is one edge of the host graph. -/
theorem adjacent (e : (N.subdivide (routes N graph place walk position)).CrossingEdge
    (cells N graph place walk position)) :
    graph.Adj (cells N graph place walk position ((N.subdivide (routes N graph place walk position)).src e.val))
      (cells N graph place walk position ((N.subdivide (routes N graph place walk position)).dst e.val)) := by
  rcases e with ⟨⟨e,i⟩,hc⟩
  change hopSrc N graph place walk position e i ≠ hopDst N graph place walk position e i at hc
  change graph.Adj (hopSrc N graph place walk position e i) (hopDst N graph place walk position e i)
  revert hc
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [src_zero,dst_zero]; simp
  · rw [src_succ]
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [Fin.succ_last, dst_last, Fin.val_last, Walk.getVert_length]
      simp
    · rw [Fin.succ_castSucc, dst_cast]
      intro _
      exact (walk e).adj_getVert_succ k.isLt

/-- Public and expanded private equality records use the same visit bound. Every visit
costs one inserted site and two endpoint records of the original cable width. -/
theorem fine_records [Fintype P] (expanded : Bool) (prior payload : N.Site → ℕ) (g : G) :
    localRecords (N.subdivide (routes N graph place walk position)) expanded
      (Sum.elim prior (fun _ => 0)) (Sum.elim payload (fun _ => 0))
        (fun v => cells N graph place walk position v = g) =
    localRecords N expanded prior payload (fun v => place v = g) +
      ∑ e, (1+2*recordCost expanded (N.width e)) * (walk e).support.count g := by
  rw [BorderVNP.Cover.subdivision_records_eq]
  congr 1
  apply sum_congr rfl
  intro e _
  rw [← sum_vertex_hits graph, mul_sum]
  apply sum_congr rfl
  intro i _
  by_cases h : (walk e).getVert i.val = g <;> simp [cells,h]

end Packing.WalkLayout

end BorderVNP
end Computability
end OAI
