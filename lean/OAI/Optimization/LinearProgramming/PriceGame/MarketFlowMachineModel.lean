import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineRows
import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachinePaths
import Mathlib.Data.List.OfFn

/-! Concrete dense input words for the residual network and pointwise agreement of
the emitted directed arcs with the network used by the typed augmentation proof. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace FlowMachine
namespace Rows

open OAI.Optimization.LinearProgramming.PriceGame.Market.Graph Quiver GridMachine.Table

variable {m g : ℕ}
variable (n : Network (Fin m) (Fin g))

@[simp] theorem index_expert (e : Fin m) :
    Augment.vertexIndex n (.expert e) = e.castAdd (g+1) := rfl

@[simp] theorem index_option (o : Option (Fin g)) :
    Augment.vertexIndex n (.opt o) = ((finSuccEquiv g).symm o).natAdd m := rfl

@[simp] theorem decode_expert (e : Fin m) :
    (Augment.vertexIndex n).symm (e.castAdd (g+1)) = .expert e := by
  exact (Augment.vertexIndex n).symm_apply_apply (.expert e)

@[simp] theorem decode_option (j : Fin (g+1)) :
    (Augment.vertexIndex n).symm (j.natAdd m) = .opt (finSuccEquiv g j) := by
  apply (Augment.vertexIndex n).injective
  simp

theorem start_index (i : Fin m) :
    (Augment.vertexIndex n (Augment.start n i)).val = if n.pos i then i.val else m := by
  cases h : n.pos i <;> simp [Augment.start, h]

theorem finish_index (i : Fin m) :
    (Augment.vertexIndex n (Augment.finish n i)).val = if n.pos i then m else i.val := by
  cases h : n.pos i <;> simp [Augment.finish, h]

def eligibleBit (dec : ∀ e j, Decidable (n.accepts e j)) (e : Fin m) : Option (Fin g) → Bool
  | none => true
  | some j => @decide _ (dec e j)

theorem eligibleBit_iff (dec : ∀ e j, Decidable (n.accepts e j)) (e : Fin m) (o : Option (Fin g)) :
    eligibleBit n dec e o = true ↔ eligible n.accepts e o := by
  cases o <;> simp [eligibleBit, eligible]

/-- The static word contains signs, availability flags and scaled bids. The dynamic word
contains the current flow and terminal potentials of the two vertex families. -/
def encodeRaw (dec : ∀ e j, Decidable (n.accepts e j)) (D : ℕ) (r : Vertex n → ℚ) : Raw :=
  ((List.ofFn n.pos, packedCells (eligibleBit n dec),
     packedCells (fun e o => Grid.scaleInput D (bid n.c e o))),
   (packedFlow n.f, List.ofFn fun e => Grid.scaleInput D (r (.expert e)),
    List.ofFn fun j : Fin (g+1) => Grid.scaleInput D (r (.opt (finSuccEquiv g j)))))

theorem read_ofFn {α : Type*} {k : ℕ} (d : α) (f : Fin k → α) (i : Fin k) :
    read d (List.ofFn f) i.val = f i := by
  rw [read, List.headD_eq_head?_getD, List.head?_drop,
    List.getElem?_eq_getElem (by simp), Option.getD_some]
  simp

theorem read_packedCells {α : Type*} (d : α) (f : Fin m → Option (Fin g) → α)
    (e : Fin m) (o : Option (Fin g)) :
    read d (packedCells f) (e.val*(g+1)+((finSuccEquiv g).symm o).val) = f e o := by
  rw [← cellIndex_row_major]
  unfold cellIndex packedCells
  rw [read_ofFn]
  simp

/-- The packed word also arises by concatenating the expert rows, with the dummy first
in every row. This form is convenient for a machine reading the input market row by row. -/
theorem packedCells_eq_flatten {α : Type*} (f : Fin m → Option (Fin g) → α) :
    packedCells f = (List.ofFn fun e : Fin m =>
      List.ofFn fun j : Fin (g+1) => f e (finSuccEquiv g j)).flatten := by
  rw [packedCells, List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext e
  apply congrArg List.ofFn
  funext j
  have heq (v : Fin (m*(g+1))) (hv : v.val = e.val*(g+1)+j.val) :
      (cellEquiv m g).symm v = (e,finSuccEquiv g j) := by
    apply (cellEquiv m g).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    change v.val = cellIndex e (finSuccEquiv g j)
    simp [hv, cellIndex_row_major]
  have bound : e.val*(g+1)+j.val < m*(g+1) := by
    simpa [cellIndex_row_major] using cellIndex_in_bounds e (finSuccEquiv g j)
  exact congrArg (fun pair : Fin m × Option (Fin g) => f pair.1 pair.2)
    (heq ⟨e.val*(g+1)+j.val,bound⟩ rfl)

/-- One entry in the independent typed adjacency representation. -/
def referenceArc (dec : ∀ e j, Decidable (n.accepts e j)) (D : ℕ) (u v : Vertex n) : List Arc :=
  ((Augment.edgeAt n dec u v).toList).map fun a =>
    (((Augment.vertexIndex n v).val, Grid.scaleInput D (n.weight a)),arcID n a)

private theorem scale_neg (D : ℕ) (x : ℚ) : Grid.scaleInput D (-x) = -Grid.scaleInput D x := by
  simp [Grid.scaleInput]

theorem emit_reference (dec : ∀ e j, Decidable (n.accepts e j)) (D : ℕ) (r : Vertex n → ℚ)
    (e : Fin m) (o : Option (Fin g)) (forward : Bool) :
    emit forward ((e.val,((finSuccEquiv g).symm o).val),encodeRaw n dec D r) =
      referenceArc n dec D (if forward then .expert e else .opt o)
        (if forward then .opt o else .expert e) := by
  simp only [emit, encodeRaw, List.length_ofFn, read_ofFn, packedFlow, read_packedCells]
  have hk := cellIndex_row_major e o
  by_cases ha : eligible n.accepts e o
  · have hb := (eligibleBit_iff n dec e o).mpr ha
    cases forward <;> cases he : n.pos e <;> by_cases hz : n.f e o = 0 <;>
      simp [referenceArc, Augment.edgeAt, Network.Allowed, ha, hb, he, hz, Nat.pos_iff_ne_zero,
        Network.weight, side, arcID, hk, scale_neg] <;> rfl
  · have hb : eligibleBit n dec e o = false := by
      cases he : eligibleBit n dec e o
      · rfl
      · exact (ha ((eligibleBit_iff n dec e o).mp he)).elim
    cases forward <;> simp [referenceArc, Augment.edgeAt, Network.Allowed, ha, hb]

@[simp] theorem reference_experts (dec : ∀ e j, Decidable (n.accepts e j)) (D : ℕ) (e e' : Fin m) :
    referenceArc n dec D (.expert e) (.expert e') = [] := by
  simp [referenceArc, Augment.edgeAt, Network.Allowed]

@[simp] theorem reference_options (dec : ∀ e j, Decidable (n.accepts e j)) (D : ℕ)
    (o o' : Option (Fin g)) :
    referenceArc n dec D (.opt o) (.opt o') = [] := by
  simp [referenceArc, Augment.edgeAt, Network.Allowed]

end Rows
end FlowMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
