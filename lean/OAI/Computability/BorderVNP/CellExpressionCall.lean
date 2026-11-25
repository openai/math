import OAI.Computability.BorderVNP.CellMoveWord

/-! # Calling binary address procedures with an enclosing loop environment

The caller frames the row, copies the environment, and runs a fixed procedure in its own
register bank. Returning its binary result to the row preserves the environment and every
previously emitted bit. This also applies when the procedure uses the same register for its
input and output.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator

open RationalHitting RationalHitting.StackLanguage VPVNP.RAMTape

variable {A B C : Type} {ca : A → List Bool} {cb : B → List Bool} {cc : C → List Bool}
  {f : A × B → C}

/-- Call a clean pair-input procedure on the row and environment and place its result on the row. -/
def pairCall (p : Procedure (pairCode ca cb) cc f) : Fragment IO :=
  let copyEnv := Fragment.copyWord (.inl IO.env) (.inr p.input)
  let packRow := Fragment.prepend (.inl IO.row) (.inr p.input)
  let call := (Fragment.plain (Structured.lower p.program)).mount (Sum.inr (α := IO))
  let ret := Fragment.moveWord (.inr p.output) (.inl IO.row)
  (copyEnv.seq (packRow.seq (call.seq ret))).hide

/-- A polynomial in the framed input length bounds the call, including register transfers. -/
def pairClock (p : Procedure (pairCode ca cb) cc f) : TimeBound :=
  32 * .variable + 32 + 10 * p.bound

private theorem io_set_row (row env out newRow : List Bool) :
    Function.update (io row env out) IO.row newRow = io newRow env out := by
  funext k; cases k <;> rfl

private theorem single_set {K : Type} [DecidableEq K] (k : K) (xs ys : List Bool) :
    Function.update (single k xs) k ys = single k ys := Function.update_idem ..

/-- Actual elementary steps, with empty private registers on both ends of the call. -/
theorem pairCall_run (p : Procedure (pairCode ca cb) cc f) (a : A) (b : B) (out : List Bool) :
    ∃ t ≤ (pairClock p).eval ((pairCode ca cb (a,b)).length+1),
      (pairCall p).Runs t (io (ca a) (cb b) out) (io (cc (f (a,b))) (cb b) out) := by
  let s₀ : Stacks (IO ⊕ p.Registers) := Sum.elim (io (ca a) (cb b) out) (fun _ => [])
  let s₁ : Stacks (IO ⊕ p.Registers) := Sum.elim (io (ca a) (cb b) out) (single p.input (cb b))
  let s₂ : Stacks (IO ⊕ p.Registers) := Sum.elim (io [] (cb b) out) (single p.input (pairCode ca cb (a,b)))
  let s₃ : Stacks (IO ⊕ p.Registers) := Sum.elim (io [] (cb b) out) (single p.output (cc (f (a,b))))
  let s₄ : Stacks (IO ⊕ p.Registers) := Sum.elim (io (cc (f (a,b))) (cb b) out) (fun _ => [])
  obtain ⟨t₁, ht₁, h₁⟩ := Fragment.copyWord_run (src := Sum.inl IO.env) (dst := Sum.inr p.input)
    (by simp) s₀
  have e₁ : Function.update s₀ (.inr p.input) (s₀ (.inl .env)) = s₁ := Fragment.update_right ..
  rw [e₁] at h₁
  obtain ⟨t₂, ht₂, h₂⟩ := Fragment.prepend_run (src := Sum.inl IO.row) (dst := Sum.inr p.input)
    (by simp) s₁
  have e₂ : Function.update (Function.update s₁ (.inl .row) []) (.inr p.input)
      (codeWord (s₁ (.inl .row)) ++ s₁ (.inr p.input)) = s₂ := by
    change Function.update (Function.update (Sum.elim _ _) _ _) _ (codeWord (ca a) ++ single p.input (cb b) p.input) = _
    rw [Fragment.update_left, io_set_row, Fragment.update_right, single_self, single_set]
    rfl
  rw [e₂] at h₂
  obtain ⟨v, hv, h⟩ := p.correct (a,b)
  obtain ⟨t₃, ht₃, h₃⟩ := Structured.run h
  let call := Fragment.plain (Structured.lower p.program)
  have hcall : (call.mount Sum.inr).Runs t₃ s₂ s₃ := by
    apply Fragment.runs_mount _ Sum.inr_injective (Fragment.runs_plain h₃)
    · intro i; rfl
    · intro i; rfl
    · rintro (i|i) hi
      · rfl
      · exact (hi i rfl).elim
  obtain ⟨t₄, ht₄, h₄⟩ := Fragment.moveWord_run (src := Sum.inr p.output) (dst := Sum.inl IO.row)
    (by simp) s₃ rfl
  have e₄ : Function.update (Function.update s₃ (.inr p.output) []) (.inl .row) (s₃ (.inr p.output)) = s₄ := by
    change Function.update (Function.update (Sum.elim _ _) _ _) _ (single p.output (cc (f (a,b))) p.output) = _
    rw [Fragment.update_right, single_set, single_nil, Fragment.update_left, single_self, io_set_row]
  rw [e₄] at h₄
  refine ⟨t₁+(t₂+(t₃+t₄)), ?_, Fragment.runs_hide (Fragment.runs_seq _ _ h₁
    (Fragment.runs_seq _ _ h₂ (Fragment.runs_seq _ _ hcall h₄)))⟩
  change t₁ ≤ 2*(7*(cb b).length+2*0+7) at ht₁
  change t₂ ≤ 2*(6*(ca a).length+5) at ht₂
  change t₄ ≤ 2*(4*(single p.output (cc (f (a,b))) p.output).length+3) at ht₄
  rw [single_self] at ht₄
  have hsize := p.size (a,b)
  simp only [pairClock, TimeBound.eval_add, TimeBound.eval_mul, TimeBound.eval_variable,
    TimeBound.eval_numeral, pairCode_length] at *
  omega

/-- Fixed-depth private expression evaluator, with binary result on the row register. -/
noncomputable def eval (d : ℕ) : Fragment IO := pairCall (Address.machine d).choose

/-- The time bound depends only on the fixed expression depth and the encoded input length. -/
noncomputable def evalClock (d : ℕ) : TimeBound := pairClock (Address.machine d).choose

/-- Evaluate the packed syntax tree in its original lexical environment. -/
theorem eval_run (d : ℕ) (e : CellSparse.NatExpr) (env : List ℕ) (out : List Bool)
    (hd : Address.depth e ≤ d) :
    ∃ t ≤ (evalClock d).eval ((Coding.code (Address.pack d e,env)).length+1),
      (eval d).Runs t (io (Coding.code (Address.pack d e)) (Coding.code env) out)
        (io (e.eval env).bits (Coding.code env) out) := by
  have h := pairCall_run (Address.machine d).choose (Address.pack d e) env out
  rw [Address.eval_pack e env hd] at h
  exact h

end CellMacro.Generator

end BorderVNP
end Computability
end OAI
