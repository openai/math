import OAI.Computability.VPVNP.RankQueryGramReadSpace

/-! # Calling convention for a streamed greedy index

The input is a dense basis ordinal. A physical selector returns its original
index in a fresh binary result word. Its auxiliary ports can be reused by a
subsequent scalar query as soon as they satisfy the ready predicate again.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.OrdinalRead

open RAMTape UniversalCountStack

/-- An ordinal reader receives a binary input index and writes the selected original index on
its result stack. -/
inductive Port (K : Type) where
  | input | result | aux (k : K)
  deriving DecidableEq, Fintype

/-- Initialize the ordinal reader with a fixed-width input index, a result stack, and its
auxiliary stacks. -/
def bank {K : Type} (w i : ℕ) (result : List Bool) (aux : Stacks K) : Stacks (Port K)
  | .input => digits w i | .result => result | .aux k => aux k

/-- For every valid ordinal and ready auxiliary bank, preserve the input word and return the
selected index in a width-w word within the step and per-stack height bounds. The final
auxiliary bank is ready for another call. -/
def CorrectSpace {K : Type} [DecidableEq K] {r n : ℕ} (read : FiniteRoutine (Port K))
    (g : Fin r → Fin n) (w B S : ℕ) (ready : Stacks K → Prop) : Prop :=
  ∀ (i : Fin r) (aux : Stacks K), ready aux → ∃ t ≤ B, ∃ out, ready out ∧
    read.BoundedRun S t (bank w i [] aux) (bank w i (digits w (g i)) out)

end RankQuery.Stack.OrdinalRead

end VPVNP
end Computability
end OAI
