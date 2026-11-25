import Mathlib.Data.List.FinRange
import Mathlib.Tactic

namespace OAI
/-! # Fixed addresses of the adaptive outer reductions and reserve mesh -/

namespace Hierarchy.ProtocolRAM.Calendar
structure Mesh where
  inject : ℕ
  cool : ℕ
  outerFuel : ℕ
  reserveSteps : ℕ
  innerFuel : ℕ

inductive Attempt
  | outer (phase trial : ℕ)
  | inner (phase trial slice repair : ℕ)
  deriving DecidableEq

inductive Boundary
  | outer (phase : ℕ)
  | inner (phase trial slice : ℕ)
  deriving DecidableEq

inductive Event
  | attempt (a : Attempt)
  | feed (b : Boundary)
  deriving DecidableEq

def reserveBlock (c : Mesh) (p a j : ℕ) : List Event :=
  (List.range c.innerFuel).map (fun b=>.attempt (.inner p a j b)) ++ [.feed (.inner p a j)]

def trialBlock (c : Mesh) (p a : ℕ) : List Event :=
  .attempt (.outer p a) :: (List.range c.reserveSteps).flatMap (reserveBlock c p a)

def outerBlock (c : Mesh) (p : ℕ) : List Event :=
  (List.range c.outerFuel).flatMap (trialBlock c p) ++ [.feed (.outer p)]

def events (c : Mesh) : List Event :=
  (List.range (c.inject+c.cool)).flatMap (outerBlock c)

private theorem length_blocks {α β : Type*} (xs : List α) (f : α → List β) (k : ℕ)
    (constant : ∀ x, (f x).length = k) : (xs.flatMap f).length=xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,constant,Nat.succ_mul,Nat.add_comm]

theorem event_count (c : Mesh) :
    (events c).length = (c.inject+c.cool)*(c.outerFuel*(1+c.reserveSteps*(c.innerFuel+1))+1) := by
  have sub p a j : (reserveBlock c p a j).length=c.innerFuel+1 := by simp [reserveBlock]
  have one p a : (trialBlock c p a).length=1+c.reserveSteps*(c.innerFuel+1) := by
    simp only [trialBlock,List.length_cons,length_blocks _ _ _ (sub p a),List.length_range,Nat.add_comm 1]
  have outer p : (outerBlock c p).length=c.outerFuel*(1+c.reserveSteps*(c.innerFuel+1))+1 := by
    simp [outerBlock,length_blocks _ _ _ (one p)]
  simp [events,length_blocks _ _ _ outer]

end Hierarchy.ProtocolRAM.Calendar

end OAI
