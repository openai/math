import OAI.Optimization.LinearProgramming.PrimalDual.Finite
import OAI.Optimization.LinearProgramming.PrimalDual.State
import Mathlib.Tactic.NormNum

/-! Calling a concrete, bounded RAM feasibility program from the two-query reduction.
The program's trace guarantee is used only to prove correctness of the data read.
In particular, the evaluator never chooses a witness from an existential theorem. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Execute at most the given number of RAM steps. A legal halt is preserved if
there is excess fuel. An illegal instruction or division is propagated as failure. -/
def runCall (p : Program) (s : State K) : Nat → Option (State K)
  | 0 => some s
  | k+1 => (runCall p s k).bind fun z => if z.output.isSome then some z else step p z

private theorem output_none_of_step {p : Program} {s v : State K} (h : step p s = some v) :
    s.output = none := by
  cases hs : s.output with
  | none => rfl
  | some tag => simp [step, hs] at h

theorem runCall_of_trace {p : Program} {s : State K} {k : Nat} {t : Fin (k+1) → State K}
    (h : Trace p s k t) (i : Fin (k+1)) : runCall p s i.val = some (t i) := by
  induction i using Fin.induction with
  | zero => exact congrArg some h.1.symm
  | succ i ih =>
    change (runCall p s i.castSucc.val).bind _ = _
    rw [ih]
    simp only [Option.bind_some, output_none_of_step (h.2 i), Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte]
    exact h.2 i

theorem runCall_stays_halted {p : Program} {s z : State K} {k : Nat}
    (h : runCall p s k = some z) (hh : z.output ≠ none) (extra : Nat) :
    runCall p s (k+extra) = some z := by
  induction extra with
  | zero => exact h
  | succ e ih =>
    rw [Nat.add_succ, runCall, ih]
    cases hz : z.output with
    | none => exact (hh hz).elim
    | some _ => simp [hz]

variable {m d : Nat}

omit [IsStrictOrderedRing K] in
private theorem tag_present {A : Matrix (Fin m) (Fin d) K} {b : Fin m → K} {s : State K}
    (h : FeasibilityOutput A b s) : s.output ≠ none := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]

/-- The bounded oracle call has a legal, verified trace on this particular instance. -/
def CallValid (p : Program) (fuel : Nat) (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) : Prop :=
  ∃ (k : Nat) (t : Fin (k+1) → State K), Trace p (start [m,d] (lpInput A b)) k t ∧ k ≤ fuel ∧
    FeasibilityOutput A b (t (Fin.last k))

theorem runCall_returns {p : Program} {fuel : Nat} {A : Matrix (Fin m) (Fin d) K} {b : Fin m → K}
    (h : CallValid p fuel A b) :
    ∃ s, runCall p (start [m,d] (lpInput A b)) fuel = some s ∧ FeasibilityOutput A b s := by
  rcases h with ⟨k, t, htrace, hbound, hout⟩
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hbound
  exact ⟨t (Fin.last k), runCall_stays_halted (runCall_of_trace htrace (Fin.last k))
    (tag_present hout) r, hout⟩

/-- Run the scalar program and read its exact output. The legal-trace proof is erased. -/
def callWithProof (p : Program) (fuel : Nat) (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K)
    (h : CallValid p fuel A b) : FeasibilityReply A b :=
  match he : runCall p (start [m,d] (lpInput A b)) fuel with
  | none => False.elim (by obtain ⟨_,h1,_⟩ := runCall_returns h; simp [he] at h1)
  | some s => decodeFeasibility A b s (by
      obtain ⟨s',hs,hout⟩ := runCall_returns h
      rw [he] at hs; cases hs; exact hout)

/-- A uniform dimensional step guarantee for the given feasibility program. -/
def ValidProgram (p : Program) (C E : Nat) : Prop :=
  ∀ (m d : Nat), 0 < m → 0 < d → ∀ (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ),
    CallValid p (polyBound C E (m+d)) A b

/-- Invoke the same concrete feasibility program on the original matrix, and, if
needed, on the ordinal-indexed primal/dual matrix. The tag decides the branch. -/
def optimizeWithRAM {p : Program} {C E : Nat} (h : ValidProgram p C E) (hm : 0 < m) (hd : 0 < d)
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) : State ℚ × Nat :=
  match callWithProof p _ A b (h m d hm hd A b) with
  | .infeasible y hy => (encodeOptimization (c := c) (.infeasible y hy), 1)
  | .feasible x₀ hx₀ =>
    let M := finJointMatrix A b c
    let r := finJointRhs b c
    let answer := callWithProof p _ M r (h _ _ (by omega) (by omega) M r)
    (encodeOptimization (finishFinite A b c x₀ hx₀ answer), 2)

theorem optimizeWithRAM_correct {p : Program} {C E : Nat} (h : ValidProgram p C E)
    (hm : 0 < m) (hd : 0 < d) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) :
    OptimizationOutput A b c (optimizeWithRAM h hm hd A b c).1 ∧
      (optimizeWithRAM h hm hd A b c).2 ≤ 2 := by
  unfold optimizeWithRAM
  split <;> exact ⟨encodeOptimization_correct _, by norm_num⟩

theorem feasibility_supplies_program (h : StronglyPolynomialFeasibility) :
    ∃ p C E, ValidProgram p C E := by
  rcases h with ⟨p,C,E,B,D,hp⟩
  refine ⟨p,C,E,?_⟩
  intro m d hm hd A b
  obtain ⟨k,t,ht,hk,_,hout⟩ := hp m d hm hd A b
  exact ⟨k,t,ht,hk,hout⟩

end PrimalDual
end LinearProgramming
end Optimization
end OAI
