import OAI.Computability.BorderVNP.CellMoveWord
import OAI.Computability.QuantumFactoring.BitStackProcedures

/-! # Calling a finite Boolean-stack procedure inside a private cell

The source branch and loop both consume their tested symbol. They lower directly
to the native returning pop instructions, preserving their exact operational
step counts. An isolated call moves the encoded input and output through a private
register bank and clears every scratch stack at return.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator.PrivateProcedure

open VPVNP.RAMTape ExactQuantumFactoring.BitStackProgram

variable {K : Type} [DecidableEq K]

/-- Compile a deterministic Boolean-stack program to a finite native instruction table. -/
def lower : Program K → FiniteRoutine K
  | .skip => .ret
  | .push k b => .ofRoutine (.push k b)
  | .seq p q => (lower p).followedBy (lower q)
  | .cases k p q r => .ofRoutine (Routine.popCase k (lower p).body (lower q).body (lower r).body)
  | .loop k p q => .ofRoutine (Routine.popLoop k (fun _ => true) (lower p).body (lower q).body)

/-- All source derivations lower to native returning stack traces with exactly the original clock. -/
theorem lower_runs {p : Program K} {s u : Store K} {t : ℕ} (h : Runs p s u t) :
    (lower p).Runs t s u := by
  induction h with
  | skip s => exact Routine.runs_ret s
  | push s k b => exact Routine.runs_push k b s
  | seq _ _ ih₁ ih₂ => rw [Nat.add_comm]; exact FiniteRoutine.Runs.followedBy ih₁ ih₂
  | cases_nil hs _ ih => exact Routine.runs_popCase_empty _ _ _ _ hs ih
  | cases_false hs _ ih => exact Routine.runs_popCase_false _ _ _ _ hs ih
  | cases_true hs _ ih => exact Routine.runs_popCase_true _ _ _ _ hs ih
  | @loop_nil k p q s hs => exact Routine.Runs.popLoop_empty k (fun _ => true) (lower p).body (lower q).body hs
  | @loop_false k p q s t u xs a b hs _ _ ih₁ ih₂ =>
    rw [show b+a+1=1+a+b by omega]
    exact Routine.Runs.popLoop_false_continue k (fun _ => true) (lower p).body (lower q).body hs rfl ih₁ ih₂
  | @loop_true k p q s t u xs a b hs _ _ ih₁ ih₂ =>
    rw [show b+a+1=1+a+b by omega]
    exact Routine.Runs.popLoop_true_continue k (fun _ => true) (lower p).body (lower q).body hs rfl ih₁ ih₂

variable {A B : Type} {ea : A → List Bool} {eb : B → List Bool} {f : A → B}

/-- Run the procedure using its own finite registers and replace one public argument word with its result. -/
def call (p : Procedure ea eb f) (port : K) : Fragment K :=
  let enter := Fragment.moveWord (.inl port) (.inr p.input)
  let body := (Fragment.plain (lower p.program)).mount (Sum.inr (α := K))
  let leave := Fragment.moveWord (.inr p.output) (.inl port)
  (enter.seq (body.seq leave)).hide

/-- The private invocation executes the source trace and spends at most eight
steps per input and output symbol plus twelve boundary steps for the two moves. -/
theorem call_runs (p : Procedure ea eb f) (port : K) {x y : List Bool} {c : ℕ}
    (h : Runs p.program (singletonStore p.input x) (singletonStore p.output y) c)
    (s : Stacks K) (hs : s port = x) :
    ∃ t ≤ c+8*x.length+8*y.length+12, (call p port).Runs t s (Function.update s port y) := by
  let cleared := Function.update s port []
  let s₀ : Stacks (K ⊕ p.K) := Sum.elim s (fun _ => [])
  let s₁ : Stacks (K ⊕ p.K) := Sum.elim cleared (singletonStore p.input x)
  let s₂ : Stacks (K ⊕ p.K) := Sum.elim cleared (singletonStore p.output y)
  let s₃ : Stacks (K ⊕ p.K) := Sum.elim (Function.update s port y) (fun _ => [])
  obtain ⟨t₁,ht₁,h₁⟩ := Fragment.moveWord_run (src := Sum.inl port) (dst := Sum.inr p.input) (by simp) s₀ rfl
  have e₁ : Function.update (Function.update s₀ (.inl port) []) (.inr p.input) (s₀ (.inl port)) = s₁ := by
    change Function.update (Function.update (Sum.elim _ _) _ _) _ (s port) = _
    rw [Fragment.update_left,Fragment.update_right,hs]
    rfl
  rw [e₁] at h₁
  let body := Fragment.plain (lower p.program)
  have h₂ : (body.mount Sum.inr).Runs c s₁ s₂ := by
    apply Fragment.runs_mount _ Sum.inr_injective (Fragment.runs_plain (lower_runs h))
    · intro i; rfl
    · intro i; rfl
    · rintro (i|i) hi
      · rfl
      · exact (hi i rfl).elim
  obtain ⟨t₃,ht₃,h₃⟩ := Fragment.moveWord_run (src := Sum.inr p.output) (dst := Sum.inl port) (by simp) s₂
    (Function.update_self ..)
  have hy : s₂ (.inr p.output) = y := by
    change singletonStore p.output y p.output = y
    rw [singletonStore,Function.update_self]
  have e₃ : Function.update (Function.update s₂ (.inr p.output) []) (.inl port) (s₂ (.inr p.output)) = s₃ := by
    rw [hy]
    dsimp only [s₂,s₃,cleared,singletonStore]
    rw [Fragment.update_right, Function.update_idem, Function.update_eq_self, Fragment.update_left, Function.update_idem]
  rw [e₃] at h₃
  refine ⟨t₁+(c+t₃), ?_, Fragment.runs_hide (Fragment.runs_seq _ _ h₁ (Fragment.runs_seq _ _ h₂ h₃))⟩
  change t₁ ≤ 2*(4*(s port).length+3) at ht₁
  rw [hs] at ht₁
  rw [hy] at ht₃
  omega

/-- An isolated compiled call has a polynomial clock evaluated at the original input length. -/
noncomputable def clock (p : Procedure ea eb f) : Polynomial ℕ := 16*Polynomial.X + 9*p.bound + 12

/-- The source procedure guarantee implies a total native run and a polynomial
bound, with all caller stacks except the argument preserved verbatim. -/
theorem call_run (p : Procedure ea eb f) (port : K) (a : A) (s : Stacks K) (hs : s port = ea a) :
    ∃ t ≤ (clock p).eval (ea a).length, (call p port).Runs t s (Function.update s port (eb (f a))) := by
  obtain ⟨c,hc,hr⟩ := p.runs a
  obtain ⟨t,ht,he⟩ := call_runs p port hr s hs
  refine ⟨t,?_,he⟩
  have := p.output_length_le a
  simp only [clock,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
  omega

end CellMacro.Generator.PrivateProcedure

end BorderVNP
end Computability
end OAI
