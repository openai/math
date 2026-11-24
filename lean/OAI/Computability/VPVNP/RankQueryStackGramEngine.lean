import OAI.Computability.VPVNP.RankQueryStackGramPorts
import OAI.Computability.VPVNP.RankQueryDescribeAdapter

/-!
# The fixed Schur determinant machine for weighted Gram coefficients

A concrete scalar reader for the input matrix is the only matrix-dependent
subroutine. The Schur interpreter, the Gram index calculation, the two field
products and the continuation stack all have fixed finite controls.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.GramEngine

open Engine RAMTape Dispatch

variable {K : Type}

variable [DecidableEq K]

/-- Build the Gram evaluator actions using the supplied signed scalar-read callbacks. -/
def actionsWith (call : Bool → FiniteRoutine (GramScalar.Port K)) : Actions (Aux K) :=
  Assembly.actions bank scratch macPort ((DescribeAdapter.describeWith call).onPorts route)

/-- Instantiate the Gram evaluator actions with the scalar routine built from a Macaulay entry
reader. -/
def actions (read : FiniteRoutine (MacaulayRead.Port K)) : Actions (Aux K) :=
  actionsWith (GramScalar.machine read)

/-- Assemble the stack machine that evaluates Gram queries using the supplied Macaulay entry
reader. -/
def machine (read : FiniteRoutine (MacaulayRead.Port K)) := Engine.machine (actions read)

variable {w v d p e n m U Z B : ℕ} {c : SliceArithmetic.Vector p e}

omit [DecidableEq K] in
private theorem extra_stable {readerReady : Stacks K → Prop} {s t : Stacks (Aux K)}
    (h : extra w v m c readerReady s) (same : ∀ j, (∀ i, bank i ≠ j) → t j = s j) :
    extra w v m c readerReady t := by
  obtain ⟨rs, persist, ls, hf, hr, hb⟩ := h
  exact ⟨rs, persist, ls, hf, hr, fun z => (same (.inl (.inr z)) (fun _ eq => by cases eq)).trans (hb z)⟩

private theorem lift_control (inner : FiniteRoutine (Engine.Port (DescribeAdapter.Aux K)))
    (ctl next : Ctl n U Z c) (fs : List (F n U Z c)) (out : Stacks (DescribeAdapter.Aux K))
    (base : Stacks (Aux K)) (signal : List Bool) {t : ℕ}
    (run : inner.Runs t (atControl w v ctl fs (base ∘ Sum.inl)) (atControl w v next fs out signal)) :
    (inner.onPorts route).Runs t (atControl w v ctl fs base)
      (atControl w v next fs (Sum.elim out (base ∘ Sum.inr)) signal) := by
  apply FiniteRoutine.runs_onPorts_framed _ route_injective run
  · intro j; cases j with | frame k => cases k <;> rfl | _ => rfl
  · intro j; cases j with | frame k => cases k <;> rfl | _ => rfl
  · intro j hj; cases j with
    | frame i => exact (hj (.frame i) rfl).elim
    | result => exact (hj .result rfl).elim
    | condition => exact (hj .condition rfl).elim
    | aux i => cases i with
      | inl j => exact (hj (.aux j) rfl).elim
      | inr j => rfl

variable [Fact p.Prime] [NeZero e]

/-- Install all five engine callbacks on one finite bank. The matrix-entry
reader can be reused for different query degrees and both child directions. -/
theorem contractsWith {T : ℕ} (call : Bool → FiniteRoutine (GramScalar.Port K)) (entry : Entry n (Scalar c))
    {readerReady : Stacks K → Prop} (hc : DescribeAdapter.CallRuns call entry w v m d T readerReady)
    (hv : SliceArithmetic.Word.workingWidth p ≤ v) (hw₃ : 3 ≤ w) (hw : (d+1)*widthFactor ≤ w)
    (hd : d ≤ w) (hsize : n+U+Z+m+8 < 2^d)
    (s : ℕ) (hn : n ≤ 2^s) (hu : U ≤ 2^s) (hz : Z ≤ 2^s)
    (hs : 2*s+6 ≤ w) (hws : (2*s+6+1)*widthFactor ≤ w) :
    Contracts (actionsWith call) (SchurKey.program (U := U) (Z := Z) entry) w v
      (Assembly.localBudget w e v) (SchurKey.arityBound n U Z) (Ready w v n m c readerReady)
      (Pending w v m c readerReady) (DescribeAdapter.timeWith w v e T) := by
  apply Assembly.contracts (s := s) bank scratch macPort (fun _ _ h => Option.some.inj (Sum.inr.inj h))
    (fun _ h => by cases h) (fun _ _ h => by cases h) _ (fun _ _ => extra_stable)
    _ _ hn hu hz hs hws hv
  intro q fs aux ha
  have small : DescribeAdapter.Ready w v n m c readerReady (aux ∘ Sum.inl) := ⟨ha.1,ha.2.2.2⟩
  obtain ⟨t,ht,out,ho,desc⟩ := DescribeAdapter.describe_entries call entry hc hv hw₃ hw hd hsize q fs _ small
  let big := Sum.elim out (aux ∘ Sum.inr)
  have hb : Ready w v n m c readerReady big := ⟨ho.1,ha.2.1,ha.2.2.1,ho.2⟩
  refine ⟨t, ht, big, hb, ?_⟩
  cases h : (SchurKey.program entry).describe q <;>
    rw [h] at desc <;> exact lift_control _ _ _ _ _ _ _ desc

theorem contracts (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin m) (Scalar c))
    {readerReady : Stacks K → Prop} (hc : MacaulayRead.Correct read M w v B readerReady)
    (hv : SliceArithmetic.Word.workingWidth p ≤ v) (hw₃ : 3 ≤ w) (hw : (d+1)*widthFactor ≤ w)
    (hd : d ≤ w) (hsize : n+U+Z+m+8 < 2^d)
    (s : ℕ) (hn : n ≤ 2^s) (hu : U ≤ 2^s) (hz : Z ≤ 2^s)
    (hs : 2*s+6 ≤ w) (hws : (2*s+6+1)*widthFactor ≤ w) :
    Contracts (actions read) (SchurKey.program (U := U) (Z := Z) (weightedGramEntryCoeff M)) w v
      (Assembly.localBudget w e v) (SchurKey.arityBound n U Z) (Ready w v n m c readerReady)
      (Pending w v m c readerReady) (DescribeAdapter.clock w v e B) :=
  contractsWith (GramScalar.machine read) (weightedGramEntryCoeff M)
    (GramScalar.machine_runs read M hc hv (by omega) hw) hv hw₃ hw hd hsize s hn hu hz hs hws

end RankQuery.Stack.GramEngine

end VPVNP
end Computability
end OAI
