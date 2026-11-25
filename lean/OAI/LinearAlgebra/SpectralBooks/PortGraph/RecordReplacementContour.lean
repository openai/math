import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPatchRecord
import OAI.Geometry.HyperbolicGroups.PairingForest
import Mathlib.GroupTheory.Perm.Fin

/-! # The spanning-tree contour of a single numbered record

The vertex rotation reads the recorded slot numbers cyclically. Kruskal considers
internal wires in lexicographic order of their tail darts. On a connected record,
crossing just the retained wires and then turning gives one orbit on all darts.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

namespace PortGraph.PatchShape

variable {K : ℕ} (R : PatchShape K)

/-- The internal connectivity test of a record, on its numbered vertices. -/
abbrev InternallyConnected :=
  (PlanarPatch.underlying R.toPiece.graph.tail R.toPiece.graph.head).Connected

/-- Advance by one numbered port, wrapping around that vertex. -/
def contourTurn : Perm R.Dart := Equiv.sigmaCongrRight fun v => finRotate (R.typeAt v).degree.val

private theorem rotate_sameCycle {n : ℕ} (a b : Fin n) : (finRotate n).SameCycle a b := by
  cases n with
  | zero => exact Fin.elim0 a
  | succ n =>
    cases n with
    | zero => exact (show a = b by apply Fin.ext; omega).sameCycle _
    | succ n => exact isCycle_finRotate.sameCycle (by simp) (by simp)

theorem contourTurn_sameCycle (x y : R.Dart) : R.contourTurn.SameCycle x y ↔ x.1 = y.1 := by
  constructor
  · exact fun h => sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm R.Vertex))
      (j := Sigma.fst) (fun _ => rfl) h)
  · rcases x with ⟨v, a⟩
    rintro rfl
    exact semiconj_perm_sameCycle (j := Sigma.mk _) (fun _ => rfl) (rotate_sameCycle a _)

/-- The vertex index precedes the slot index when comparing numbered darts. -/
abbrev dartOrder : LinearOrder R.Dart := inferInstanceAs (LinearOrder (Lex R.Dart))

/-- Each internal wire occurs once, represented by its outgoing dart. -/
def contourPairs : List (R.Dart × R.Dart) :=
  let darts := (Finset.univ : Finset (Lex R.Dart)).filter fun x =>
    R.opposite (ofLex x) ≠ ofLex x ∧ (ofLex x).side = false
  (darts.sort (· ≤ ·)).map fun x => (ofLex x, R.opposite (ofLex x))

@[simp] theorem mem_contourPairs {x y : R.Dart} : (x,y) ∈ R.contourPairs ↔
    R.opposite x ≠ x ∧ x.side = false ∧ R.opposite x = y := by
  unfold contourPairs
  simp only [List.mem_map, Finset.mem_sort, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨e, ⟨hne, hside⟩, rfl, rfl⟩
    exact ⟨hne, hside, rfl⟩
  · rintro ⟨h, hd, rfl⟩
    exact ⟨toLex x, ⟨h, hd⟩, rfl, rfl⟩

/-- The retained internal wires, in deterministic record order. -/
def contourForest : List (R.Dart × R.Dart) :=
  forestEdges (SameCycle.setoid R.contourTurn) R.contourPairs

/-- The positive boundary walk crosses a retained wire and then turns at the vertex. -/
def contourPerm : Perm R.Dart := R.contourTurn * swaps R.contourForest

private theorem joins_wire {D : Type*} (s : Setoid D) (l : List (D × D)) {x y : D}
    (h : (x, y) ∈ l) : joins s l x y := by
  induction l generalizing s with
  | nil => simp at h
  | cons ab l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_joins (glue s x y) l (glue_pair s x y)
    · exact ih _ h

/-- Each component of the graph of all internal wires is a single orbit
for the contour of the retained forest, before imposing connectivity. -/
theorem contourPerm_orbits : SameCycle.setoid R.contourPerm =
    joins (SameCycle.setoid R.contourTurn) R.contourPairs := by
  let s := SameCycle.setoid R.contourTurn
  let l := R.contourPairs
  apply setoid_eq_of_card_eq
  · rw [← forestEdges_joins s l]
    exact sameCycle_joins le_rfl _
  · have hCycle := forestEdges_cycles R.contourTurn s le_rfl l
    have hCard := forestEdges_card s l
    rw [cycles_eq_card_classes, cycles_eq_card_classes] at hCycle
    change (Nat.card (Quotient (joins s l)) : ℤ) + (forestEdges s l).length =
      Nat.card (Quotient (SameCycle.setoid R.contourTurn)) at hCard
    change (Nat.card (Quotient (SameCycle.setoid R.contourPerm)) : ℤ) =
      Nat.card (Quotient (SameCycle.setoid R.contourTurn)) - (forestEdges s l).length at hCycle
    change Nat.card (Quotient (SameCycle.setoid R.contourPerm)) = Nat.card (Quotient (joins s l))
    omega

/-- The entire numbered dart set of a connected record is covered by one orbit. -/
theorem contourPerm_sameCycle (hc : R.InternallyConnected) (x y : R.Dart) :
    R.contourPerm.SameCycle x y := by
  let s := joins (SameCycle.setoid R.contourTurn) R.contourPairs
  have vertex {x y : R.Dart} (h : x.1 = y.1) : s x y :=
    le_joins _ _ ((R.contourTurn_sameCycle x y).2 h)
  have wire (e : R.Wire) : s e.val (R.opposite e.val) :=
    joins_wire _ _ ((mem_contourPairs R).2 ⟨e.property.1, e.property.2, rfl⟩)
  have adj {v w : R.Vertex} (h : (PlanarPatch.underlying R.toPiece.graph.tail R.toPiece.graph.head).Adj v w) :
      ∃ a b : R.Dart, a.1 = v ∧ b.1 = w ∧ s a b := by
    obtain ⟨_, e, h | h⟩ := h
    · exact ⟨e.val, R.opposite e.val, h.1, h.2, wire e⟩
    · exact ⟨R.opposite e.val, e.val, h.2, h.1, s.symm (wire e)⟩
  have walk {v w : R.Vertex} (p : (PlanarPatch.underlying R.toPiece.graph.tail R.toPiece.graph.head).Walk v w) :
      ∀ a b : R.Dart, a.1 = v → b.1 = w → s a b := by
    induction p with
    | nil => exact fun a b h h' => vertex (h.trans h'.symm)
    | cons h p ih =>
      intro a b ha hb
      obtain ⟨u,u',hu,hu',hwire⟩ := adj h
      exact s.trans (vertex (ha.trans hu.symm)) (s.trans hwire (ih u' b hu' hb))
  change SameCycle.setoid R.contourPerm x y
  rw [contourPerm_orbits]
  exact walk (hc.preconnected x.1 y.1).some x y rfl rfl

end PortGraph.PatchShape

end

end SpectralBooks
end LinearAlgebra
end OAI
