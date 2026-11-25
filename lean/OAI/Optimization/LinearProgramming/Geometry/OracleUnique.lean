import OAI.Optimization.LinearProgramming.Geometry.OracleSegments

/-! Determinacy of terminal scalar-oracle executions and of relocatable subroutine runs. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace OracleSegments

open RAM Contract

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem step_live {p : OracleProgram} {o : ScalarOracle K} {s t : Config K} {c : ℕ}
    (h : oracleStep p o s=some (c,t)) : s.state.output=none := by
  cases v : s.state.output with
  | none => rfl
  | some _ => simp [oracleStep,v] at h

/-- Determinism includes the number of packet words charged for each oracle exchange. -/
theorem oracleRun_terminal_unique {p : OracleProgram} {o : ScalarOracle K} {s t z : Config K} {k l : ℕ}
    (first : OracleRun p o s k t) (endFirst : t.state.output≠none)
    (second : OracleRun p o s l z) (endSecond : z.state.output≠none) : k=l ∧ t=z := by
  induction first generalizing z l with
  | refl =>
    cases second with
    | refl => exact ⟨rfl,rfl⟩
    | next edge _ => exact (endFirst (step_live edge)).elim
  | next edge tail ih =>
    cases second with
    | refl => exact (endSecond (step_live edge)).elim
    | next other rest =>
      cases Option.some.inj (edge.symm.trans other)
      obtain ⟨time,out⟩ := ih endFirst rest endSecond
      exact ⟨by omega,out⟩

/-- Test both segments against the very same halt continuation. Their times, resulting
caller memory, and scalar transcript therefore coincide, for any two safety predicates. -/
theorem Runs.unique {seg : Segment} {o : ScalarOracle K} {P Q : Memory K → Prop}
    {m t z : Memory K} {h ht hz : Contract.History K} {k l : ℕ}
    (left : Runs seg o P m h k t ht) (right : Runs seg o Q m h l z hz) :
    k=l ∧ t=z ∧ ht=hz := by
  have stopped₁ := (left.halted 0).plain
  have stopped₂ := (right.halted 0).plain
  obtain ⟨time,finish⟩ := oracleRun_terminal_unique stopped₁ (by simp) stopped₂ (by simp)
  exact ⟨Nat.add_right_cancel time,congrArg (fun c : Config K => c.state.memory) finish,
    congrArg Config.history finish⟩

end OracleSegments
end Geometry
end LinearProgramming
end Optimization
end OAI
