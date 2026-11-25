import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachine
import OAI.Optimization.LinearProgramming.PriceGame.MarketBitStackBridge
import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentSolver
import Mathlib.Logic.Equiv.Fin.Basic

/-! The row-major arc identifier convention links a binary route and the flow in `State.pack`
to the literal input and output words of `FlowMachine.updateP`. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace FlowMachine

open Quiver OAI.Optimization.LinearProgramming.PriceGame.Market.Graph
open scoped BigOperators

variable {m g : ℕ}

/-- The zero option is the dummy and real options follow it, exactly as in `State.pack`. -/
def cellEquiv (m g : ℕ) : Fin m × Option (Fin g) ≃ Fin (m*(g+1)) :=
  (Equiv.prodCongr (Equiv.refl _) (finSuccEquiv g).symm).trans finProdFinEquiv

def cellIndex (e : Fin m) (o : Option (Fin g)) : ℕ := (cellEquiv m g (e,o)).val

theorem cellIndex_row_major (e : Fin m) (o : Option (Fin g)) :
    cellIndex e o = e.val * (g+1) + ((finSuccEquiv g).symm o).val := by
  change ((finSuccEquiv g).symm o).val + (g+1) * e.val = _
  ac_rfl

theorem cellIndex_in_bounds (e : Fin m) (o : Option (Fin g)) :
    cellIndex e o < m*(g+1) := (cellEquiv m g (e,o)).isLt

private theorem cellIndex_inj {e j : Fin m} {o i : Option (Fin g)} :
    cellIndex e o = cellIndex j i ↔ e = j ∧ o = i := by
  constructor
  · intro h
    exact Prod.mk.inj ((cellEquiv m g).injective (Fin.ext h))
  · rintro ⟨rfl,rfl⟩
    rfl

/-- Arc identifiers sent through the Bellman path table. For both expert signs, increasing
the amount is even and decreasing it is odd. -/
def arcID (n : Network (Fin m) (Fin g)) : ∀ {a b : Vertex n}, (a ⟶ b) → ℕ
  | .expert e, .opt o, _ => if n.pos e then 2*cellIndex e o else 2*cellIndex e o+1
  | .opt o, .expert e, _ => if n.pos e then 2*cellIndex e o+1 else 2*cellIndex e o
  | .expert _, .expert _, h => h.down.elim
  | .opt _, .opt _, h => h.down.elim

theorem arcID_in_bounds (n : Network (Fin m) (Fin g)) {a b : Vertex n} (h : a ⟶ b) :
    arcID n h < 2 * (m*(g+1)) := by
  cases a <;> cases b
  · exact h.down.elim
  · rename_i e o
    have := cellIndex_in_bounds e o
    dsimp [arcID]
    split <;> omega
  · rename_i o e
    have := cellIndex_in_bounds e o
    dsimp [arcID]
    split <;> omega
  · exact h.down.elim

/-- Forward order agrees with the finite Bellman trace. -/
abbrev route (n : Network (Fin m) (Fin g)) {a b : Vertex n} (p : Path a b) : Route :=
  GridMachine.Table.pathIds (arcID n) p

theorem route_comp (n : Network (Fin m) (Fin g)) {a b c : Vertex n} (p : Path a b) (q : Path b c) :
    route n (p.comp q) = route n p ++ route n q :=
  GridMachine.Table.pathIds_comp (arcID n) p q

theorem route_length (n : Network (Fin m) (Fin g)) {a b : Vertex n} (p : Path a b) :
    (route n p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p h ih =>
    change (route n p ++ [arcID n h]).length = p.length + 1
    rw [List.length_append, ih]
    rfl

private def contribution (k id : ℕ) : ℤ :=
  (if id = 2*k then 1 else 0) - (if id = 2*k+1 then 1 else 0)

private theorem contribution_even (k j : ℕ) :
    contribution k (2*j) = if k = j then 1 else 0 := by
  have hz : 2*j ≠ 2*k+1 := by omega
  have he : 2*j = 2*k ↔ k=j := by omega
  simp only [contribution, hz, ite_false, he, sub_zero]

private theorem contribution_odd (k j : ℕ) :
    contribution k (2*j+1) = -(if k = j then 1 else 0) := by
  have hz : 2*j+1 ≠ 2*k := by omega
  have he : 2*j+1 = 2*k+1 ↔ k=j := by omega
  simp only [contribution, hz, ite_false, he, zero_sub]

private theorem arc_contribution (n : Network (Fin m) (Fin g)) {a b : Vertex n} (h : a ⟶ b)
    (e : Fin m) (o : Option (Fin g)) :
    n.edgeUnits h e o = contribution (cellIndex e o) (arcID n h) := by
  cases a <;> cases b
  · exact h.down.elim
  · rename_i j i
    by_cases hcell : e = j ∧ o = i <;> cases hj : n.pos j <;>
      simp [Network.edgeUnits, Network.signedUnit, arcID, hj, contribution_even, contribution_odd,
        cellIndex_inj, hcell]
  · rename_i i j
    by_cases hcell : e = j ∧ o = i <;> cases hj : n.pos j <;>
      simp [Network.edgeUnits, Network.signedUnit, arcID, hj, contribution_even, contribution_odd,
        cellIndex_inj, hcell]
  · exact h.down.elim

private theorem singleton_count (k j : ℕ) :
    (([j].count k : ℕ) : ℤ) = if j = k then 1 else 0 := by
  by_cases h : j = k <;> simp [h]

theorem change_counts (n : Network (Fin m) (Fin g)) {a b : Vertex n} (p : Path a b)
    (e : Fin m) (o : Option (Fin g)) :
    n.change p e o = ((route n p).count (2*cellIndex e o) : ℤ) -
      ((route n p).count (2*cellIndex e o+1) : ℤ) := by
  induction p with
  | nil => simp [route, GridMachine.Table.pathIds]
  | cons p h ih =>
    rw [Network.change_cons, ih, arc_contribution]
    simp only [route, GridMachine.Table.pathIds, List.count_append, Nat.cast_add, singleton_count, contribution]
    ring

/-- The wire data are the actual natural entries in the dense packed state, row by row. -/
def packedCells {α : Type*} (f : Fin m → Option (Fin g) → α) : List α :=
  List.ofFn fun k : Fin (m*(g+1)) =>
    let eo := (cellEquiv m g).symm k
    f eo.1 eo.2

abbrev packedFlow (f : Fin m → Option (Fin g) → ℕ) : Flow := packedCells f

@[simp] theorem packedFlow_length (f : Fin m → Option (Fin g) → ℕ) :
    (packedFlow f).length = m*(g+1) := List.length_ofFn

theorem update_getElem (xs : Flow) (p : Route) (k : ℕ) (hk : k < xs.length) :
    (update (xs,p))[k]'(by simpa [update] using hk) =
      xs[k] + p.count (2*k) - p.count (2*k+1) := by
  simp [update, updatedCell, List.getElem?_eq_getElem hk]

theorem packedFlow_getElem (f : Fin m → Option (Fin g) → ℕ) (k : Fin (m*(g+1))) :
    (packedFlow f)[k.val]'(by simp) =
      f ((cellEquiv m g).symm k).1 ((cellEquiv m g).symm k).2 := by
  simp [packedFlow, packedCells]

/-- The program agrees on every cell with the signed, then truncated path perturbation.
The identity even holds for a nonsimple path or one with repeated arcs. -/
theorem update_packedFlow (n : Network (Fin m) (Fin g)) {a b : Vertex n} (p : Path a b) :
    update (packedFlow n.f, route n p) = packedFlow (Augment.applyPath n p) := by
  apply List.ext_getElem
  · simp [update]
  · intro k hk _
    have hlt : k < m*(g+1) := by simpa [update] using hk
    let i : Fin (m*(g+1)) := ⟨k,hlt⟩
    let eo := (cellEquiv m g).symm i
    have hindex : cellIndex eo.1 eo.2 = k := congrArg Fin.val ((cellEquiv m g).apply_symm_apply i)
    rw [update_getElem _ _ _ (by simpa using hlt), packedFlow_getElem n.f i,
      packedFlow_getElem (Augment.applyPath n p) i]
    change n.f eo.1 eo.2 + (route n p).count (2*k) - (route n p).count (2*k+1) =
      ((n.f eo.1 eo.2 : ℤ) + n.change p eo.1 eo.2).toNat
    rw [change_counts, hindex]
    omega

theorem packedFlow_double (f : Fin m → Option (Fin g) → ℕ) :
    (packedFlow f).map (2*·) = packedFlow (fun e o => 2*f e o) := by
  simp [packedFlow, packedCells, List.map_ofFn, Function.comp_def]

theorem packedState_view (f : Fin m → Option (Fin g) → ℕ)
    (p : Fin m → ℚ) (q : Option (Fin g) → ℚ) :
    packedFlow (Augment.State.pack f p q).flow = packedFlow f := by simp

end FlowMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
