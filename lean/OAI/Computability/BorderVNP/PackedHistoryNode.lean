import OAI.Computability.BorderVNP.PackedHistoryEquiv
import OAI.Computability.BorderVNP.CrossingParallelFrame
import OAI.Computability.BorderVNP.ParseBatchVerifierConjunction

/-! # One shared bottom-up circuit node of an adaptive public history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP.VerifierNetwork ParseBatchVerifier
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {k : ℕ} {σ : Type*} [Fintype σ] {U V G : Type} [Fintype U] [Fintype V] [Fintype G]

/-- Every compiled state carries its subtree validity wire. -/
abbrev Result (U : Type) := U ⊕ Unit

/-- Actual child state pins and static local profile guesses. -/
abbrev LocalPins (k : ℕ) (U G : Type) := (Fin k × U) ⊕ G

private abbrev NodePins (k : ℕ) (U G : Type) := (Fin k × Result U) ⊕ G

private def statePin : LocalPins k U G → NodePins k U G :=
  Sum.elim (fun j => .inl (j.1,.inl j.2)) Sum.inr

private def validExpr : Expr (NodePins k U G ⊕ Result V) :=
  .and (.input (.inr (.inr ()))) (every (fun i : Fin k => .input (.inl (.inl (i,.inr ())))))

private noncomputable def post : Frame (NodePins k U G ⊕ Result V) (Result V) :=
  (((Frame.initial id).step (fun _ : Unit => validExpr)).withInput).select
    (Sum.elim (fun u => .inl (.inr (.inl u))) Sum.inr)

private noncomputable def node (f : Frame (LocalPins k U G) (Result V)) :
    Frame (NodePins k U G) (Result V) :=
  post.subst (f.subst (Frame.initial statePin)).withInput

private theorem node_state (f : Frame (LocalPins k U G) (Result V)) (z : NodePins k U G → Bool) (v : V) :
    (node f).eval z (.inl v) = f.eval (z ∘ statePin) (.inl v) := by
  have he : (Frame.initial statePin).eval z = z ∘ statePin := funext (Frame.initial_eval statePin z)
  simp [node,post,he]

private theorem node_flag (f : Frame (LocalPins k U G) (Result V)) (z : NodePins k U G → Bool) :
    (node f).eval z (.inr ()) = true ↔
      (∀ i, z (.inl (i,.inr ())) = true) ∧ f.eval (z ∘ statePin) (.inr ()) = true := by
  let u := (f.subst (Frame.initial statePin)).withInput.eval z
  have hi : (Frame.initial (id : NodePins k U G ⊕ Result V → _)).eval u = u := funext (Frame.initial_eval id u)
  have hf : (Frame.initial statePin).eval z = z ∘ statePin := funext (Frame.initial_eval statePin z)
  simp only [node, Frame.subst_eval]
  change post.eval u (.inr ()) = true ↔ _
  simp [post,hi,validExpr,StatementCircuit.Expr.eval,every_eval,u,hf,and_comm]

private theorem node_size (f : Frame (LocalPins k U G) (Result V)) : (node f).size ≤ f.size + 2*k+3 := by
  have hh := every_size (fun i : Fin k => (StatementCircuit.Expr.input (.inl (.inl (i,.inr ()))) : Expr (NodePins k U G ⊕ Result V)))
    1 (fun _ => le_rfl)
  have hv : (validExpr (k := k) (U := U) (V := V) (G := G)).size ≤ 2*k+3 := by
    simp only [validExpr, StatementCircuit.Expr.size]
    omega
  have h := Frame.step_size_le (Frame.initial (id : NodePins k U G ⊕ Result V → _)) (fun _ : Unit => validExpr)
    _ (fun _ => hv)
  simp only [Frame.initial_size,zero_add,Fintype.card_unit,one_mul] at h
  simpa only [node, post, Frame.subst_size, Frame.withInput_size, Frame.select_size, Frame.initial_size,
    Nat.zero_add, Nat.add_assoc] using Nat.add_le_add_left h f.size

/-- Concatenate child fragments once, exposing all of their gate references. -/
noncomputable def gather (children : Fin k → Frame σ (Result U)) : Frame σ (Fin k × Result U) :=
  ((Crossing.exists_parallelFrames (out := fun _ : Fin k => Result U) children).choose).select
    fun p => ⟨p.1,p.2⟩

theorem gather_eval (children : Fin k → Frame σ (Result U)) (x : σ → Bool) (p : Fin k × Result U) :
    (gather children).eval x p = (children p.1).eval x p.2 := by
  rw [gather,Frame.select_eval]
  exact (Crossing.exists_parallelFrames children).choose_spec.2 x p.1 p.2

theorem gather_size (children : Fin k → Frame σ (Result U)) :
    (gather children).size ≤ 1 + ∑ i, (children i).size := by
  rw [gather,Frame.select_size]
  exact (Crossing.exists_parallelFrames children).choose_spec.1

private noncomputable def sources (children : Fin k → Frame σ (Result U)) (guess : G → σ) :
    Frame σ (NodePins k U G) :=
  (gather children).withInput.select (Sum.elim Sum.inr (fun g => .inl (guess g)))

/-- Apply the actual local transform and profile check to the already computed child states.
Retaining child references makes the gate count additive over the children. -/
noncomputable def combine (f : Frame (LocalPins k U G) (Result V)) (children : Fin k → Frame σ (Result U))
    (guess : G → σ) : Frame σ (Result V) := (node f).subst (sources children guess)

private theorem sources_state (children : Fin k → Frame σ (Result U)) (guess : G → σ) (x : σ → Bool) :
    (sources children guess).eval x ∘ statePin =
      Sum.elim (fun p : Fin k × U => (children p.1).eval x (.inl p.2)) (x ∘ guess) := by
  funext j
  cases j <;> simp [sources,statePin,Function.comp_def,gather_eval]

theorem combine_state (f : Frame (LocalPins k U G) (Result V)) (children : Fin k → Frame σ (Result U))
    (guess : G → σ) (x : σ → Bool) (u : V) :
    (combine f children guess).eval x (.inl u) =
      f.eval (Sum.elim (fun p => (children p.1).eval x (.inl p.2)) (x ∘ guess)) (.inl u) := by
  rw [combine, Frame.subst_eval, node_state, sources_state]

theorem combine_flag (f : Frame (LocalPins k U G) (Result V)) (children : Fin k → Frame σ (Result U))
    (guess : G → σ) (x : σ → Bool) :
    (combine f children guess).eval x (.inr ()) = true ↔
      (∀ i, (children i).eval x (.inr ()) = true) ∧
      f.eval (Sum.elim (fun p => (children p.1).eval x (.inl p.2)) (x ∘ guess)) (.inr ()) = true := by
  rw [combine, Frame.subst_eval, node_flag, sources_state]
  simp [sources,gather_eval]

theorem combine_size (f : Frame (LocalPins k U G) (Result V)) (children : Fin k → Frame σ (Result U))
    (guess : G → σ) : (combine f children guess).size ≤ (∑ i, (children i).size) + f.size + (2*k+4) := by
  rw [combine, Frame.subst_size, sources, Frame.select_size, Frame.withInput_size]
  have h₁ := gather_size children
  have h₂ := node_size f
  omega

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
