import OAI.Computability.VPVNP.RankQueryStackEngineAssembly
import OAI.Computability.VPVNP.RankQueryGramAlias

/-! # The shared determinant and scalar-reader ports for the weighted Gram matrix -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.GramEngine

open Engine RAMTape Dispatch

/-- Auxiliary ports shared by the Schur descriptor, the matrix-entry reader, and the
multiply-and-add routine. -/
abbrev Aux (K : Type) := DescribeAdapter.Aux K ⊕ Option MultiplyAdd.Aux

variable {K : Type}

/-- Embed the Schur dispatch registers into the descriptor side of the Gram engine's auxiliary
bank. -/
def bank : EngineAlias.Small ↪ Aux K := ⟨fun i => .inl (.inl i), fun _ _ h => Sum.inl.inj (Sum.inl.inj h)⟩
/-- The temporary stack reserved for the Gram engine's scan and child-call routines. -/
def scratch : Aux K := .inr none
/-- Embed a multiply-and-add port into the Gram engine's auxiliary bank. -/
def macPort (i : MultiplyAdd.Aux) : Aux K := .inr (some i)

/-- Route descriptor calls through the Gram engine, sharing the live frame, result, and
condition ports. -/
def route : Engine.Port (DescribeAdapter.Aux K) → Engine.Port (Aux K)
  | .frame j => .frame j | .result => .result | .condition => .condition | .aux j => .aux (.inl j)

theorem route_injective : Function.Injective (route (K := K)) := by
  intro a b h; cases a <;> cases b <;> simp_all [route]

/-- The descriptor's scalar workspace and matrix reader are ready for a query with column count
`m`. -/
def extra {p e : ℕ} (w v m : ℕ) (c : SliceArithmetic.Vector p e) (readerReady : Stacks K → Prop)
    (s : Stacks (Aux K)) : Prop := DescribeAdapter.RightReady w v m c readerReady (s ∘ Sum.inl)

/-- Entry condition for the Gram engine, combining the dispatch register bank, scratch stack,
scalar arithmetic advice, and reader state. -/
abbrev Ready {p e : ℕ} (w v n m : ℕ) (c : SliceArithmetic.Vector p e) (readerReady : Stacks K → Prop) :=
  Assembly.Ready (bank (K := K)) scratch macPort (extra w v m c readerReady) n w v c

/-- State of the Gram engine after staging a child query and before activating its six output
words. -/
abbrev Pending {p e n U Z : ℕ} (w v m : ℕ) (c : SliceArithmetic.Vector p e) (readerReady : Stacks K → Prop) :=
  Assembly.Pending (n := n) (U := U) (Z := Z) (bank (K := K)) scratch macPort (extra w v m c readerReady) w v c

end RankQuery.Stack.GramEngine

end VPVNP
end Computability
end OAI
