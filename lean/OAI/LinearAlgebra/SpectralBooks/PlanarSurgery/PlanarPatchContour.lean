import OAI.Geometry.HyperbolicGroups.PairingForest
import OAI.Geometry.HyperbolicGroups.PictureUnderlyingGraph
import OAI.Geometry.HyperbolicGroups.BoundaryEnumeration

/-! # Spanning-tree boundary orders in the patch replacement

Run Kruskal on the actual internal edges in dart order. Its retained bands and
the vertex disks have one boundary walk per connected patch. Filtering that
walk to the external darts gives the stub list, with every stub appearing once.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PlanarSurgery

open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

variable {D P : Type*} [LinearOrder D] [Fintype D] [DecidableEq P] (M : PictureMap D)
  (patch : M.GraphVertex → P)

/-- Ordered internal pairs. Both directions may be offered to Kruskal. -/
def internalPairs : List (D × D) :=
  ((Finset.univ.filter fun d => patch (M.vertexClass d) = patch (M.vertexClass (M.edge d))).sort
    (· ≤ ·)).map fun d => (d, M.edge d)

@[simp] theorem mem_internalPairs {x y : D} : (x, y) ∈ internalPairs M patch ↔
    M.edge x = y ∧ patch (M.vertexClass x) = patch (M.vertexClass y) := by
  simp [internalPairs]
  grind

private theorem joins_pair_mem {A : Type*} (s : Setoid A) (l : List (A × A)) {x y : A}
    (h : (x, y) ∈ l) : joins s l x y := by
  induction l generalizing s with
  | nil => simp at h
  | cons ab l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_joins (glue s x y) l (glue_pair s x y)
    · exact ih _ h

private theorem patch_joins (hc : ∀ i, (M.underlyingGraph.induce {v | patch v = i}).Preconnected) :
    joins (SameCycle.setoid M.vertex) (internalPairs M patch) =
      Setoid.ker (fun d => patch (M.vertexClass d)) := by
  let s := joins (SameCycle.setoid M.vertex) (internalPairs M patch)
  apply le_antisymm
  · apply joins_le
    · intro x y h
      exact congrArg patch ((M.vertexClass_eq_iff x y).mpr h)
    · intro ⟨x, y⟩ h
      exact (mem_internalPairs M patch).mp h |>.2
  · intro x y he
    let f : M.GraphVertex → Quotient s := Quotient.map id (fun _ _ h => le_joins _ _ h)
    let i := patch (M.vertexClass x)
    have move {v w : {v : M.GraphVertex // patch v = i}}
        (h : (M.underlyingGraph.induce {v | patch v = i}).Adj v w) : f v = f w := by
      change M.underlyingGraph.Adj v.val w.val at h
      obtain ⟨_, z, hz, hz'⟩ := h
      rw [← hz, ← hz']
      apply Quotient.sound
      apply joins_pair_mem
      exact (mem_internalPairs M patch).mpr ⟨rfl, by simp only [id_eq, hz, hz', v.property, w.property]⟩
    obtain ⟨walk⟩ := hc i ⟨M.vertexClass x, rfl⟩ ⟨M.vertexClass y, he.symm⟩
    have eq_end {v w : {v : M.GraphVertex // patch v = i}}
        (p : (M.underlyingGraph.induce {v | patch v = i}).Walk v w) : f v = f w := by
      induction p with
      | nil => rfl
      | cons h p ih => exact (move h).trans ih
    exact Quotient.exact (eq_end walk)

/-- Turning around the tree neighborhood means crossing a retained edge when
one is present, then turning at the incident vertex. -/
def contour : Perm D := M.vertex * swaps (forestEdges (SameCycle.setoid M.vertex) (internalPairs M patch))

/-- A connected patch has exactly one boundary cycle after retaining its
spanning tree, even if it surrounds another patch in the full map. -/
theorem contour_sameCycle (hc : ∀ i, (M.underlyingGraph.induce {v | patch v = i}).Preconnected)
    (x y : D) : (contour M patch).SameCycle x y ↔ patch (M.vertexClass x) = patch (M.vertexClass y) := by
  let s := SameCycle.setoid M.vertex
  let l := internalPairs M patch
  have hle : SameCycle.setoid (contour M patch) ≤ joins s l := by
    rw [← forestEdges_joins s l]
    exact sameCycle_joins le_rfl _
  have heq : SameCycle.setoid (contour M patch) = joins s l := by
    apply setoid_eq_of_card_eq hle
    have hCycle := forestEdges_cycles M.vertex s le_rfl l
    have hCard := forestEdges_card s l
    change cycles (contour M patch) = cycles M.vertex - _ at hCycle
    rw [cycles_eq_card_classes, cycles_eq_card_classes] at hCycle
    change (Nat.card (Quotient (joins s l)) : ℤ) + (forestEdges s l).length =
      Nat.card (Quotient (SameCycle.setoid M.vertex)) at hCard
    change (Nat.card (Quotient (SameCycle.setoid (contour M patch))) : ℤ) =
      Nat.card (Quotient (SameCycle.setoid M.vertex)) - (forestEdges s l).length at hCycle
    omega
  change SameCycle.setoid (contour M patch) x y ↔ _
  rw [heq, patch_joins M patch hc]
  rfl

/-- Enumerate the boundary in its positive orientation, based at the chosen
port. Fixed ports give a singleton boundary. -/
def boundaryWalk (x : D) : List D :=
  let f := contour M patch
  if f x = x then [x] else f.toList x

theorem boundaryWalk_spec (x : D) :
    IsBoundary (contour M patch) (boundaryWalk M patch x) ∧ x ∈ boundaryWalk M patch x := by
  let f := contour M patch
  change IsBoundary f (if f x = x then [x] else f.toList x) ∧ _
  by_cases h : f x = x
  · simp only [h, ite_true, boundaryWalk, ← show f = contour M patch from rfl,
      List.mem_singleton, and_true]
    refine ⟨by simp, ?_⟩
    intro z hz
    obtain rfl := List.mem_singleton.mp hz
    simpa only [List.formPerm_singleton, one_apply] using h
  · have hx := mem_support.mpr h
    have hlist : x ∈ f.toList x := mem_toList_iff.mpr ⟨SameCycle.rfl, hx⟩
    rw [ite_eq_right h]
    refine ⟨⟨f.nodup_toList x, ?_⟩, ?_⟩
    · intro y hy
      rw [formPerm_toList, cycleOf_apply, ite_eq_left (mem_toList_iff.mp hy).1]
    · simpa only [boundaryWalk, ← show f = contour M patch from rfl, ite_eq_right h] using hlist

/-- Drop all internal ports after traversing the chosen tree. -/
def stubOrder (x : D) : List D := (boundaryWalk M patch x).filter
  (fun y => decide (patch (M.vertexClass y) ≠ patch (M.vertexClass (M.edge y))))

theorem stubOrder_nodup (x : D) : (stubOrder M patch x).Nodup :=
  (boundaryWalk_spec M patch x).1.nodup.filter _

theorem mem_stubOrder (hc : ∀ i, (M.underlyingGraph.induce {v | patch v = i}).Preconnected)
    (x y : D) : y ∈ stubOrder M patch x ↔ patch (M.vertexClass x) = patch (M.vertexClass y) ∧
      patch (M.vertexClass y) ≠ patch (M.vertexClass (M.edge y)) := by
  obtain ⟨h, hx⟩ := boundaryWalk_spec M patch x
  simp only [stubOrder, List.mem_filter, decide_eq_true_eq]
  refine and_congr_left fun _ => ?_
  exact (Iff.intro (h.sameCycle hx) (h.mem_of_sameCycle hx)).trans (contour_sameCycle M patch hc x y)

end PlanarSurgery

end

end SpectralBooks
end LinearAlgebra
end OAI
