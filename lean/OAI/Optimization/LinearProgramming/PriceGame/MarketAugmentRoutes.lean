import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentUnit
import OAI.Optimization.LinearProgramming.PriceGame.MarketPotentialsCost

/-! Deterministic shortest maximizing routes, using the explicit row and column numbering. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment

open Quiver OAI.Optimization.LinearProgramming.PriceGame.Market.Graph
open OAI.Optimization.LinearProgramming.PriceGame.Market.Potentials

variable {m g : ℕ} (n : Network (Fin m) (Fin g))

/-- Experts come first, then the dummy option and the real goods. -/
def vertexIndex : Vertex n ≃ Fin (m + (g + 1)) :=
  let sum : Vertex n ≃ Fin m ⊕ Option (Fin g) :=
    { toFun := fun v => match v with | .expert e => .inl e | .opt o => .inr o
      invFun := fun v => match v with | .inl e => .expert e | .inr o => .opt o
      left_inv := by rintro (_|_) <;> rfl
      right_inv := by rintro (_|_) <;> rfl }
  sum.trans ((Equiv.sumCongr (Equiv.refl _) (finSuccEquiv g).symm).trans finSumFinEquiv)

def decideAllowed (dec : ∀ e i, Decidable (n.accepts e i)) (a b : Vertex n) :
    Decidable (n.Allowed a b) := by
  letI : ∀ e i, Decidable (n.accepts e i) := dec
  letI (e : Fin m) (o : Option (Fin g)) : Decidable (eligible n.accepts e o) := by
    cases o with
    | none => exact isTrue True.intro
    | some j => exact dec e j
  cases a <;> cases b <;> unfold Network.Allowed <;> infer_instance

/-- The optional arc in the residual network's dense adjacency representation. -/
def edgeAt (dec : ∀ e i, Decidable (n.accepts e i)) (u v : Vertex n) : Option (u ⟶ v) :=
  letI := decideAllowed n dec u v
  if h : n.Allowed u v then some ⟨h⟩ else none

theorem edgeAt_eq (dec : ∀ e i, Decidable (n.accepts e i)) {u v : Vertex n} (h : u ⟶ v) :
    edgeAt n dec u v = some h := by
  simp [edgeAt, h.down]
  exact @Subsingleton.elim (PLift (n.Allowed u v)) inferInstance _ _

/-- Materialize the outgoing lists once, in the fixed vertex order. -/
def outgoing (dec : ∀ e i, Decidable (n.accepts e i)) : (u : Vertex n) → List (Σ v, u ⟶ v) :=
  let rows := Cost.prepareDense (vertexIndex n) (edgeAt n dec)
  Cost.outgoing (vertexIndex n) rows

theorem mem_outgoing (dec : ∀ e i, Decidable (n.accepts e i)) {u v : Vertex n} (h : u ⟶ v) :
    (⟨v, h⟩ : Σ z, u ⟶ z) ∈ outgoing n dec u :=
  Cost.dense_complete (vertexIndex n) (edgeAt n dec) h (edgeAt_eq n dec h)

theorem outgoing_length (dec : ∀ e i, Decidable (n.accepts e i)) (u : Vertex n) :
    (outgoing n dec u).length ≤ m + (g + 1) := by
  simpa [outgoing, Cost.prepareDense] using Cost.denseRow_length_le (vertexIndex n) (edgeAt n dec) u

/-- Output of one Bellman table with witness and all potential coordinates. -/
structure Route (i : Fin m) where
  last : Vertex n
  path : Path (start n i) last
  dual : Vertex n → ℚ

/-- Compute one Bellman table, sharing it between witness reconstruction and dual lookup. -/
def route (dec : ∀ e i, Decidable (n.accepts e i)) (π : Vertex n → ℚ) (i : Fin m) : Route n i :=
  let r := targetReward n.weight π (direct n i).toPath
  let rows := Cost.prepareDense (vertexIndex n) (edgeAt n dec)
  let layer := plans (vertexIndex n) n.weight r (Cost.outgoing (vertexIndex n) rows) (m + (g + 1) - 1)
  let read (v : Vertex n) : Plan n.weight r v := Layer.lookup (vertexIndex n) layer v
  let p := read (start n i)
  ⟨p.finish, p.path, fun v => (read v).total⟩

theorem route_length (dec : ∀ e i, Decidable (n.accepts e i)) (π : Vertex n → ℚ) (i : Fin m) :
    (route n dec π i).path.length ≤ m + (g + 1) - 1 := by
  let r := targetReward n.weight π (direct n i).toPath
  let K := m + (g + 1) - 1
  let L := plans (vertexIndex n) n.weight r (outgoing n dec) K
  let z : Plan n.weight r (start n i) := Layer.lookup (vertexIndex n) L (start n i)
  change z.path.length ≤ K
  rw [← z.steps_spec]
  exact plans_steps_le _ _ _ _ _ _

/-- The tabulated dual value at every vertex agrees with the Bellman potential used in the proof. -/
theorem route_dual (dec : ∀ e i, Decidable (n.accepts e i)) (π : Vertex n → ℚ)
    (i : Fin m) (v : Vertex n) :
    (route n dec π i).dual v = targetedPotential n.weight π (direct n i).toPath v := by
  have hcard : Fintype.card (Vertex n) = m + (g + 1) := by simpa using Fintype.card_congr (vertexIndex n)
  simpa [route, targetedPotential, potential, hcard, outgoing] using
    plans_total_eq_value (vertexIndex n) n.weight (targetReward n.weight π (direct n i).toPath)
      (outgoing n dec) (mem_outgoing n dec) (m + (g + 1) - 1) v

theorem route_spec (dec : ∀ e i, Decidable (n.accepts e i)) (π : Vertex n → ℚ)
    (hπ : ∀ {u v : Vertex n} (a : u ⟶ v), n.weight a ≤ π u - π v) (i : Fin m) :
    let z := route n dec π i
    z.last = finish n i ∧ z.path.vertices.Nodup ∧
      (∀ {u v : Vertex n} (a : u ⟶ v), n.weight a ≤ z.dual u - z.dual v) ∧
      z.path.addWeight n.weight = z.dual (start n i) - z.dual (finish n i) := by
  let ref := (direct n i).toPath
  let r := targetReward n.weight π ref
  let L := plans (vertexIndex n) n.weight r (outgoing n dec) (m + (g + 1) - 1)
  let read (v : Vertex n) : Plan n.weight r v := Layer.lookup (vertexIndex n) L v
  let plan := read (start n i)
  change plan.finish = finish n i ∧ plan.path.vertices.Nodup ∧ _ ∧ _
  have hc : NonpositiveSimpleCircuits n.weight := nonpositive_of_potential n.weight hπ
  have htotal (v : Vertex n) : (read v).total = targetedPotential n.weight π ref v :=
    route_dual n dec π i v
  have hp : targetedPotential n.weight π ref (start n i) = plan.path.addWeight n.weight + r plan.finish :=
    (htotal (start n i)).symm.trans plan.total_spec
  obtain ⟨ended, tight⟩ := target_attainment n.weight π hπ ref plan.path hp
  refine ⟨ended, plans_simple _ _ _ _ (mem_outgoing n dec) hc _ _, ?_, ?_⟩
  · intro u v a
    change n.weight a ≤ (read u).total - (read v).total
    rw [htotal, htotal]
    exact arc_le_potential_sub n.weight r hc a
  · change plan.path.addWeight n.weight = (read (start n i)).total - (read (finish n i)).total
    rw [htotal, htotal]; exact tight

end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
