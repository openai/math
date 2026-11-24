import OAI.Computability.VPVNP.RankQueryStackGramEngine
import OAI.Computability.VPVNP.RankQueryStackGramInitialization
import OAI.Computability.VPVNP.RankQueryStackEngineSpace
import OAI.Computability.VPVNP.RankQueryGramReadSpace

/-! # Space for a matrix-entry callback on the complete Schur register bank -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.GramEngine

open Engine RAMTape Dispatch

variable {K : Type} [DecidableEq K] {n m U Z p e w v B A S depth : ℕ} {c : SliceArithmetic.Vector p e}

/-- Live frame data, saved frames and the underlying reader all fit at entry. -/
def entryCap (w v e A depth : ℕ) := max (w+v+e+e*v+A) (max (max 1 (max w (e*v))) (depth*(2*max 1 (max w (e*v))+1)))

omit [DecidableEq K] in
private theorem start_cap {readerReady : Stacks K → Prop} (ha : ∀ s, readerReady s → ∀ i, (s i).length ≤ A)
    (q : Key n U Z) (fs : List (F n U Z c)) (hfs : fs.length ≤ depth) (aux : Stacks (Aux K))
    (haux : Ready w v n m c readerReady aux) (i : Engine.Port (Aux K)) :
    (atControl w v (.enter q) fs aux [] i).length ≤ entryCap w v e A depth :=
  state_length (d := depth) (.enter q,fs) hfs aux (ready_length haux ha) i

omit [DecidableEq K] in
theorem inner_start_cap {readerReady : Stacks K → Prop} (ha : ∀ s, readerReady s → ∀ i, (s i).length ≤ A)
    (q : Key n U Z) (fs : List (F n U Z c)) (hfs : fs.length ≤ depth) (aux : Stacks (Aux K))
    (haux : Ready w v n m c readerReady aux) (i : Engine.Port (DescribeAdapter.Aux K)) :
    (atControl w v (.enter q) fs (aux ∘ Sum.inl) [] i).length ≤ entryCap w v e A depth := by
  have h := start_cap ha q fs hfs aux haux (route i)
  cases i with | frame k => cases k <;> exact h | _ => exact h

/-- A bounded descriptor call executes on the whole bank while the arithmetic
advice and the unrelated scratch slot remain available to later summands. -/
theorem lift_boundedWith {readerReady : Stacks K → Prop} {call : Bool → FiniteRoutine (GramScalar.Port K)}
    {entry : Entry n (Scalar c)} [Fact p.Prime] [NeZero e]
    (ha : ∀ s, readerReady s → ∀ i, (s i).length ≤ A)
    (inner : ∀ (q : Key n U Z) (fs : List (F n U Z c)) (aux : Stacks (DescribeAdapter.Aux K)),
      DescribeAdapter.Ready w v n m c readerReady aux →
      (∀ j, (atControl w v (.enter q) fs aux [] j).length ≤ entryCap w v e A depth) →
      ∃ t ≤ B, ∃ out, DescribeAdapter.Ready w v n m c readerReady out ∧
        (DescribeAdapter.describeWith call).BoundedRun S t (atControl w v (.enter q) fs aux)
          (match (SchurKey.program entry).describe q with
           | .inl r => atControl w v (.returned r) fs out [true]
           | .inr k => atControl w v (.scan q k 0) fs out [false])) :
    DescribeBounded (actionsWith call) (SchurKey.program (U := U) (Z := Z) entry) w v B
      (max (entryCap w v e A depth) S) depth (Ready w v n m c readerReady) := by
  intro q fs aux hfs haux
  have small : DescribeAdapter.Ready w v n m c readerReady (aux ∘ Sum.inl) := ⟨haux.1,haux.2.2.2⟩
  obtain ⟨t,ht,out,ho,run⟩ := inner q fs _ small (inner_start_cap ha q fs hfs aux haux)
  let big := Sum.elim out (aux ∘ Sum.inr)
  have hb : Ready w v n m c readerReady big := ⟨ho.1,haux.2.1,haux.2.2.1,ho.2⟩
  refine ⟨t, ht, big, hb, ?_⟩
  have place (ctl : Ctl n U Z c) (sig : List Bool)
      (h : (DescribeAdapter.describeWith call).BoundedRun S t (atControl w v (.enter q) fs (aux ∘ Sum.inl))
        (atControl w v ctl fs out sig)) :
      ((actionsWith call).describe).BoundedRun (max (entryCap w v e A depth) S) t
        (atControl w v (.enter q) fs aux) (atControl w v ctl fs big sig) := by
    apply FiniteRoutine.BoundedRun.framed route_injective (h.enlarge (le_max_right ..))
      (fun j => (start_cap ha q fs hfs aux haux j).trans (le_max_left ..))
    · intro i; cases i with | frame k => cases k <;> rfl | _ => rfl
    · intro i; cases i with | frame k => cases k <;> rfl | _ => rfl
    · intro j hj; cases j with
      | frame i => exact (hj (.frame i) rfl).elim
      | result => exact (hj .result rfl).elim
      | condition => exact (hj .condition rfl).elim
      | aux i => cases i with
        | inl j => exact (hj (.aux j) rfl).elim
        | inr j => rfl
  cases h : (SchurKey.program entry).describe q <;> rw [h] at run <;> exact place _ _ run

theorem lift_bounded {readerReady : Stacks K → Prop} {read : FiniteRoutine (MacaulayRead.Port K)}
    {M : Matrix (Fin n) (Fin m) (Scalar c)} [Fact p.Prime] [NeZero e]
    (ha : ∀ s, readerReady s → ∀ i, (s i).length ≤ A)
    (inner : ∀ (q : Key n U Z) (fs : List (F n U Z c)) (aux : Stacks (DescribeAdapter.Aux K)),
      DescribeAdapter.Ready w v n m c readerReady aux →
      (∀ j, (atControl w v (.enter q) fs aux [] j).length ≤ entryCap w v e A depth) →
      ∃ t ≤ B, ∃ out, DescribeAdapter.Ready w v n m c readerReady out ∧
        (DescribeAdapter.describe read).BoundedRun S t (atControl w v (.enter q) fs aux)
          (match (SchurKey.program (weightedGramEntryCoeff M)).describe q with
           | .inl r => atControl w v (.returned r) fs out [true]
           | .inr k => atControl w v (.scan q k 0) fs out [false])) :
    DescribeBounded (actions read) (SchurKey.program (U := U) (Z := Z) (weightedGramEntryCoeff M)) w v B
      (max (entryCap w v e A depth) S) depth (Ready w v n m c readerReady) :=
  lift_boundedWith ha inner

end RankQuery.Stack.GramEngine

end VPVNP
end Computability
end OAI
