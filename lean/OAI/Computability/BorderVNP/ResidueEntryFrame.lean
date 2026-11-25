import OAI.Computability.QuantumFactoring.BooleanAlgebra
import OAI.Computability.VPVNP.VerifierMachineNetwork

/-! # Compiling a shared verifier frame into a Boolean network

The residue index frame computes one validity flag and all binary exponent differences.
Translate its gate list once and expose the same live outputs to the field evaluator.
An OR gate costs four AND/NOT gates by De Morgan's law. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryFrame

open ExactQuantumFactoring (BooleanNetwork)
open ExactQuantumFactoring.BooleanNetwork
open BinPackingGames.Foundations.Complexity.CookLevin
open VPVNP.VerifierNetwork (Frame)

private def gate {n : ℕ} : (g : Gate) → g.Bounded n → BooleanNetwork n 1
  | .const b, _ => constant b
  | .not j, h => (bit ⟨j,h⟩).bnot
  | .and j k, h => (bit ⟨j,h.1⟩).band (bit ⟨k,h.2⟩)
  | .or j k, h => (bit ⟨j,h.1⟩).bor (bit ⟨k,h.2⟩)

private theorem gate_eval {n : ℕ} (g : Gate) (h : g.Bounded n) (a : ℕ → Bool) :
    (gate g h).eval (fun i => a i) 0 = g.eval a := by
  cases g <;> simp [gate, Gate.eval]

private theorem gate_count {n : ℕ} (g : Gate) (h : g.Bounded n) :
    (gate g h).net.count ≤ 4 := by
  cases g <;> simp [gate]

private def push {n : ℕ} (g : Gate) (h : g.Bounded n) : BooleanNetwork n (n+1) :=
  (select id).pair (gate g h)

private theorem push_eval {n : ℕ} (g : Gate) (h : g.Bounded n) (a : ℕ → Bool) :
    (push g h).eval (fun i => a i) = fun j : Fin (n+1) => Function.update a n (g.eval a) j := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun k => ?_) j
  · simp only [push, eval_pair, Fin.append_left, eval_select, Function.comp_apply, id_eq,
      Fin.val_castAdd]
    exact (Function.update_of_ne (Nat.ne_of_lt i.isLt) _ _).symm
  · have hk : k = 0 := Subsingleton.elim ..
    subst k
    simp only [push, eval_pair, Fin.append_right, gate_eval, Fin.val_natAdd, Fin.val_zero,
      Nat.add_zero, Function.update_self]

private def gates (n : ℕ) : (gs : List Gate) → Ordered n gs →
    BooleanNetwork n (n + gs.length)
  | [], _ => select id
  | g :: gs, h =>
    let hs := (ordered_cons n g gs).mp h
    ((push g hs.1).comp (gates (n+1) gs hs.2)).rewire (Fin.cast (by simp; omega))

private theorem gates_eval (gs : List Gate) (n : ℕ) (h : Ordered n gs) (a : ℕ → Bool)
    (i : Fin (n+gs.length)) : (gates n gs h).eval (fun j => a j) i = run n gs a i := by
  induction gs generalizing n a with
  | nil => rfl
  | cons g gs ih =>
    simp only [gates, eval_rewire, Function.comp_apply, eval_comp, push_eval, run]
    exact ih _ _ _ _

private theorem gates_count (gs : List Gate) (n : ℕ) (h : Ordered n gs) :
    (gates n gs h).net.count ≤ 4*gs.length := by
  induction gs generalizing n with
  | nil => simp [gates]
  | cons g gs ih =>
    obtain ⟨hg,hs⟩ := (ordered_cons n g gs).mp h
    have := gate_count g hg
    have := ih (n+1) hs
    simp only [gates, count_rewire, count_comp, push, count_pair, count_select, zero_add,
      List.length_cons, Nat.mul_succ]
    omega

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

/-- Compile a frame with named wires to one shared ordinal-indexed network. -/
def network (f : Frame σ τ) : BooleanNetwork (Fintype.card σ) (Fintype.card τ) :=
  (gates _ f.core.fragment.gates f.core.fragment.ordered).rewire f.core.wires

/-- The compiled network retains all named output values under the canonical wire numbering. -/
theorem network_eval (f : Frame σ τ) (x : σ → Bool) (i : τ) :
    (network f).eval (x ∘ (Fintype.equivFin σ).symm) (Fintype.equivFin τ i) = f.eval x i := by
  let a := inputEnv (x ∘ (Fintype.equivFin σ).symm)
  have hx : x ∘ (Fintype.equivFin σ).symm = fun i : Fin (Fintype.card σ) => a i := by
    funext j
    simp [a,inputEnv,j.isLt]
  unfold network
  rw [eval_rewire, Function.comp_apply, hx, gates_eval]
  rfl

/-- No gate is duplicated across frame outputs; at most four Boolean nodes suffice per gate. -/
theorem network_count (f : Frame σ τ) : (network f).net.count ≤ 4*f.size :=
  gates_count _ _ _

end ResidueEntryFrame

end BorderVNP
end Computability
end OAI
