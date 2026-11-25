import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineModel
import OAI.Optimization.LinearProgramming.PriceGame.MarketBitStackBridge

/-! The generated adjacency rows agree in order, cost, target and arc identifier with
the graph that the verified Bellman implementation serializes. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace FlowMachine
namespace Rows

open OAI.Optimization.LinearProgramming.PriceGame.Market.Graph Quiver GridMachine.Table

variable {m g : ℕ} (n : Network (Fin m) (Fin g))

private theorem byVertex {α : Type*} (f : Vertex n → α) :
    (List.finRange (m+(g+1))).map (fun i => f ((Augment.vertexIndex n).symm i)) =
      (List.finRange m).map (fun e => f (.expert e)) ++
      (List.finRange (g+1)).map (fun j => f (.opt (finSuccEquiv g j))) := by
  simp only [List.finRange, List.map_ofFn, Function.comp_def]
  rw [List.ofFn_add (n := m) (m := g+1)]
  congr 1
  · apply congrArg List.ofFn
    funext i
    change f ((Augment.vertexIndex n).symm (i.castAdd (g+1))) = _
    rw [decode_expert]
  · apply congrArg List.ofFn
    funext i
    rw [decode_option]

private theorem range_from_fin (k : ℕ) : List.range k = (List.finRange k).map Fin.val := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

private theorem outgoing_reference (dec : ∀ e j, Decidable (n.accepts e j)) (D : ℕ) (u : Vertex n) :
    (Augment.outgoing n dec u).map (serializeArc (Augment.vertexIndex n) n.weight (arcID n) D) =
    ((List.finRange (m+(g+1))).map fun j =>
      referenceArc n dec D u ((Augment.vertexIndex n).symm j)).flatten := by
  simp only [Augment.outgoing, Potentials.Cost.prepareDense, Potentials.Cost.outgoing_prepare,
    Potentials.Cost.denseRow]
  generalize List.finRange (m+(g+1)) = js
  induction js with
  | nil => rfl
  | cons j js ih =>
    cases he : Augment.edgeAt n dec u ((Augment.vertexIndex n).symm j) <;>
      simp [he, referenceArc, serializeArc, ih]

private theorem flatten_empty {α β : Type*} (xs : List α) :
    (xs.map (fun _ => ([] : List β))).flatten = [] := by
  induction xs <;> simp_all

private theorem expertReference (dec : ∀ e j, Decidable (n.accepts e j)) (D : ℕ) (e : Fin m) :
    (Augment.outgoing n dec (.expert e)).map (serializeArc (Augment.vertexIndex n) n.weight (arcID n) D) =
      ((List.finRange (g+1)).map (fun j => referenceArc n dec D (.expert e)
        (.opt (finSuccEquiv g j)))).flatten := by
  rw [outgoing_reference, byVertex n, List.flatten_append]
  simp only [reference_experts, flatten_empty, List.nil_append]

private theorem optionReference (dec : ∀ e j, Decidable (n.accepts e j)) (D : ℕ) (o : Option (Fin g)) :
    (Augment.outgoing n dec (.opt o)).map (serializeArc (Augment.vertexIndex n) n.weight (arcID n) D) =
      ((List.finRange m).map (fun e => referenceArc n dec D (.opt o) (.expert e))).flatten := by
  rw [outgoing_reference, byVertex n, List.flatten_append]
  simp only [reference_options, flatten_empty, List.append_nil]

theorem expertRow (dec : ∀ e j, Decidable (n.accepts e j)) (D : ℕ) (r : Vertex n → ℚ) (e : Fin m) :
    row true (e.val,encodeRaw n dec D r) =
      serializeRow (Augment.vertexIndex n) n.weight r (Augment.outgoing n dec) (arcID n) D (.expert e) := by
  let raw := encodeRaw n dec D r
  have hterm : read 0 raw.2.2.1 e.val = Grid.scaleInput D (r (.expert e)) := read_ofFn ..
  have hcount : raw.2.2.2.length = g+1 := List.length_ofFn
  change (read 0 raw.2.2.1 e.val, ((List.range raw.2.2.2.length).map
    (fun k => emit true ((e.val,k),raw))).flatten) = (_, _)
  rw [hterm, hcount, range_from_fin, List.map_map, expertReference]
  congr 1
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  simpa only [Function.comp_apply, Equiv.symm_apply_apply, ite_true] using
    emit_reference n dec D r e (finSuccEquiv g j) true

theorem optionRow (dec : ∀ e j, Decidable (n.accepts e j)) (D : ℕ) (r : Vertex n → ℚ) (j : Fin (g+1)) :
    row false (j.val,encodeRaw n dec D r) =
      serializeRow (Augment.vertexIndex n) n.weight r (Augment.outgoing n dec) (arcID n) D
        (.opt (finSuccEquiv g j)) := by
  let raw := encodeRaw n dec D r
  have hterm : read 0 raw.2.2.2 j.val = Grid.scaleInput D (r (.opt (finSuccEquiv g j))) := read_ofFn ..
  have hcount : raw.1.1.length = m := List.length_ofFn
  change (read 0 raw.2.2.2 j.val, ((List.range raw.1.1.length).map
    (fun k => emit false ((k,j.val),raw))).flatten) = (_, _)
  rw [hterm, hcount, range_from_fin, List.map_map, optionReference]
  congr 1
  apply congrArg List.flatten
  apply List.map_congr_left
  intro e _
  simpa only [Function.comp_apply, Equiv.symm_apply_apply, Bool.false_eq_true, ite_false] using
    emit_reference n dec D r e (finSuccEquiv g j) false

/-- Every serialized row and its complete list of arcs equals the independent typed-graph
reference, preserving its deterministic destination order. -/
theorem make_eq_serializeGraph (dec : ∀ e j, Decidable (n.accepts e j)) (D : ℕ) (r : Vertex n → ℚ) :
    make (encodeRaw n dec D r) =
      serializeGraph (Augment.vertexIndex n) n.weight r (Augment.outgoing n dec) (arcID n) D := by
  let raw := encodeRaw n dec D r
  have he : raw.1.1.length = m := List.length_ofFn
  have ho : raw.2.2.2.length = g+1 := List.length_ofFn
  change ((List.range raw.1.1.length).map (fun i => row true (i,raw))) ++
    ((List.range raw.2.2.2.length).map (fun i => row false (i,raw))) = _
  rw [he, ho, range_from_fin m, range_from_fin (g+1), List.map_map, List.map_map,
    serializeGraph, byVertex n]
  congr 1
  · apply List.map_congr_left
    intro i _
    exact expertRow n dec D r i
  · apply List.map_congr_left
    intro i _
    exact optionRow n dec D r i

end Rows
end FlowMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
