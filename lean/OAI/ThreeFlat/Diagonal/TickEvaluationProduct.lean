import OAI.ThreeFlat.Diagonal.TickRangeChronology
import OAI.ThreeFlat.Diagonal.TickSlotForest
import OAI.ThreeFlat.RAM.TickMemoryLayout
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace OAI
/-! # Regrouping all team evaluations in one physical group -/

namespace ThreeFlat.Diagonal.TickEvaluationProduct
open TickChronology TickRangeChronology
open scoped BigOperators Classical

variable {F Cell : Type*} [CommMonoid F] [Fintype Cell] {teams : ℕ}

def time (c : Clock) (group : Fin c.groups) (j : Fin c.evaluateTicks) :=
  c.base group.val+(c.chunks+1+j.val)

/-- Actual control word S1+3 selects the row-major time/team processor slot. -/
theorem clock_slot (c : Clock) (a : ℕ) (g : Fin c.groups) (j : Fin c.evaluateTicks) (k : Fin teams) :
    RAM.TickClockWords.values c a teams k.val (time c g j) 3 = (finProdFinEquiv (j,k)).val := by
  have e := j.isLt
  have b := c.room
  have h := (c.in_group g.isLt (show c.chunks+1+j.val<c.groupDuration by omega)).2.2
  change (c.offset (c.base g.val+(c.chunks+1+j.val))-(c.chunks+1))*teams+k.val = k.val+teams*j.val
  rw [h,Nat.add_sub_cancel_left]
  ac_rfl

abbrev Owned {slots : ℕ} (owner : Cell → Fin slots) (slot : Fin slots) := {i : Cell // owner i=slot}

theorem eval_product (c : Clock) (g : Fin c.groups) (owner : Cell → Fin (c.evaluateTicks*teams))
    (f : Cell → F) (value : ℕ → F)
    (atTime : ∀ j : Fin c.evaluateTicks, value (time c g j) =
      ∏ k : Fin teams, ∏ i : Owned owner (finProdFinEquiv (j,k)), f i.val) :
    ((evalTicks c g.val).map value).prod = ∏ i, f i := by
  let slots (s : Fin (c.evaluateTicks*teams)) := ∏ i : Owned owner s, f i.val
  change ((List.ofFn (time c g)).map value).prod = _
  rw [← List.ofFn_comp',List.prod_ofFn]
  simp_rw [atTime]
  change (∏ j, ∏ k, slots (finProdFinEquiv (j,k))) = _
  calc
    _ = ∏ s : Fin c.evaluateTicks × Fin teams, slots (finProdFinEquiv s) :=
      (Fintype.prod_prod_type (f:=fun v : Fin c.evaluateTicks × Fin teams => slots (finProdFinEquiv v))).symm
    _ = ∏ s, slots s := finProdFinEquiv.prod_comp slots
    _ = ∏ i, f i := Fintype.prod_fiberwise owner f

section
variable {K : Type*} [CommSemiring K] {p : ℕ}

/-- The product of the actual padded ordered forests, with the enumerated
roots of each team, computes each root in the group exactly once. Root pins
may use both the packed pair registers and the decoded shared final wires. -/
theorem forest_product (c : Clock) (g : Fin c.groups) (owner : Cell → Fin (c.evaluateTicks*teams))
    (cost : Cell → K) (num : Fin c.evaluateTicks → Fin teams → ℕ)
    (root : ∀ j k, Fin (num j k) ≃ Owned owner (finProdFinEquiv (j,k)))
    (raw : ∀ j k, Fin (num j k) → BitNetwork K p) (input : Fin c.evaluateTicks → Fin teams → Fin p → Bool)
    (b u : Fin c.evaluateTicks → Fin teams → ℕ)
    (values : ∀ j k i, (raw j k i).eval (input j k) = cost (root j k i).val)
    (value : ℕ → K) (atTime : ∀ j, value (time c g j) =
      ∏ k, (TraceCircuit.addPadding (TickSlotForest.network (raw j k)) (b j k) (u j k)).eval (input j k)) :
    ((evalTicks c g.val).map value).prod = ∏ i, cost i := by
  apply eval_product c g owner cost value
  intro j
  rw [atTime]
  apply Finset.prod_congr rfl
  intro k _
  rw [TraceCircuit.addPadding_eval,TickSlotForest.eval]
  simp_rw [values]
  exact (root j k).prod_comp (fun i => cost i.val)

end
end ThreeFlat.Diagonal.TickEvaluationProduct

end OAI
