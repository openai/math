import OAI.Computability.BorderVNP.PackedHistoryCorrect
import OAI.Computability.BorderVNP.ShortenAdaptiveFlatten

/-! # An inner shortening tree as the next outer epoch's local profile circuit

The epoch reads the flat, ordered K^b child states and the disjoint local slots
of its b internal shortening rounds. Its output frame can be used directly
as a local transform in the outer history traversal.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Shortening.Adaptive Packing VPVNP.VerifierNetwork

variable {k b : ℕ} {A : ℕ → Type*} {W G : ℕ → Type}
variable [∀ j, Fintype (W j)] [∀ j, Fintype (G j)] {S : System k b A}

/-- Relabel the genuine inner dependent sum by its final physical state. -/
def flatChoice (S : System k b A) (c : Fin (k^b) → A 0) : ProfileSum (A b) :=
  let a := leavesEquiv k (A 0) b c
  ⟨(S.histories b le_rfl a).Index, inferInstance, state b le_rfl a⟩

/-- The local word of an outer epoch is exactly its full inner profile bit tree. -/
def flatWord (C : Codec S G) (c : Fin (k^b) → A 0) (q : (flatChoice S c).Index) : Slot k G b → Bool :=
  encode C b le_rfl (leavesEquiv k (A 0) b c) q

omit [∀ j, Fintype (G j)] in
theorem flatWord_injective (C : Codec S G) (c : Fin (k^b) → A 0) : Function.Injective (flatWord C c) :=
  encode_injective C b le_rfl _

private noncomputable def leafFrames (k b : ℕ) (T : Type) [Fintype T] :=
  leavesEquiv k (Frame (Fin (k^b) × T) T) b (fun i => Frame.initial fun j => (i,j))

/-- A full inner traversal as a single physical epoch frame on its row-major child state wires. -/
noncomputable def flatEpoch (step : Steps k b W G) :
    Frame (LocalPins (k^b) (W 0) (Slot k G b)) (Result (W b)) :=
  compile step b le_rfl (leafFrames k b (W 0))

private theorem every_flat {T : Type*} (test : T → Prop) (n : ℕ) (t : Fin (k^n) → T) (ht : ∀ i, test (t i)) :
    everyLeaf test n (leavesEquiv k T n t) := by
  induction n with
  | zero => exact ht 0
  | succ n ih => exact fun i => ih (fun j => t (copyIndex k n (i,j))) (fun j => ht _)

theorem flatEpoch_size (step : Steps k b W G) (M : ℕ) (hm : ∀ j (hj : j<b), (step j hj).size + (2*k+4) ≤ M) :
    (flatEpoch step).size ≤ historyTreeCost k 1 M b :=
  compile_size step b le_rfl (leafFrames k b (W 0)) 0 M
    (every_flat (fun f : Frame (Fin (k^b) × W 0) (W 0) => f.size ≤ 0) b _ (fun _ => le_rfl)) hm

private theorem flat_leaf_state {σ : Type*} [Fintype σ] (rep : Represents A W) (n : ℕ)
    (x : σ → Bool) (c : Fin (k^n) → A 0) (f : Fin (k^n) → Frame σ (W 0))
    (hr : ∀ i, rep 0 ((f i).eval x) (c i)) :
    LeafState rep x n (leavesEquiv k (A 0) n c) (leavesEquiv k (Frame σ (W 0)) n f) := by
  induction n with
  | zero => exact hr 0
  | succ n ih =>
    exact fun i => ih (fun j => c (copyIndex k n (i,j))) (fun j => f (copyIndex k n (i,j))) (fun j => hr _)

/-- Guard and successor specification for the outer traversal, derived from its actual inner
node frames. The guess bits encode precisely one summand of the complete adaptive epoch. -/
theorem flatEpoch_correct (C : Codec S G) (rep : Represents A W) (step : Steps k b W G)
    (correct : LocalCorrect C rep step) (c : Fin (k^b) → A 0) (y : Fin (k^b) → W 0 → Bool)
    (hy : ∀ i, rep 0 (y i) (c i)) (g : Slot k G b → Bool) :
    let raw := Sum.elim (fun p : Fin (k^b) × W 0 => y p.1 p.2) g
    ((flatEpoch step).eval raw (.inr ()) = true ↔ ∃ q, g = flatWord C c q) ∧
    ∀ q, g = flatWord C c q → rep b (fun j => (flatEpoch step).eval raw (.inl j)) ((flatChoice S c).term q) := by
  intro raw
  let x := fun p : Fin (k^b) × W 0 => y p.1 p.2
  let f := fun i : Fin (k^b) => Frame.initial (fun j : W 0 => (i,j))
  have hs (i) : (f i).eval x = y i := funext (Frame.initial_eval _ _)
  have hl := flat_leaf_state rep b x c f (fun i => (hs i).symm ▸ hy i)
  exact semantics C rep step correct b le_rfl _ _ x hl g

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
