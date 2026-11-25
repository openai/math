import OAI.Optimization.LinearProgramming.Geometry.OracleQueryHistory
import OAI.Optimization.LinearProgramming.Geometry.MarkedSegments

/-! Attach a public nonzero minor index to every individual marked scalar exchange. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Contract OracleSpec OracleSegments

variable {r s n : ℕ}

/-- Physical preconditions for the native handler together with the genuine sealed
minor represented by the words in the submitting scalar registers. -/
def namedMark (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (physical : QueryMark ℚ) : QueryMark ℚ := fun m src len dst count =>
  physical m src len dst count ∧ ∃ u : MinorLog.Index D E, sentPacket m src len=(MinorLog.words u.val).map Nat.cast

/-- Each request of the actual run, even one that returns restart, has both kinds of
certificate. Previously existing history entries impose no condition here. -/
theorem mark_named_run {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}
    {physical : QueryMark ℚ} {p : OracleProgram} {o : ScalarOracle ℚ} {P : Memory ℚ → Prop}
    {u final : Config ℚ} {k : ℕ} (run : MarkedRun physical p o P u k final) :
    ∀ old fresh : Contract.History ℚ, final.history=fresh++old → NamedTraffic D E fresh →
      (∃ past, u.history=past++old) → MarkedRun (namedMark D E physical) p o P u k final := by
  induction run with
  | refl state hs => intro _ _ _ _ _; exact .refl state hs
  | @next u v z c l hs checked edge tail ih =>
    intro old fresh shape good seen
    have nextSeen : ∃ past, v.history=past++old := by
      obtain ⟨earlier,he⟩ := seen
      obtain ⟨new,hn⟩ := oracleStep_history_extension edge
      exact ⟨new++earlier,by rw [hn,he,List.append_assoc]⟩
    refine .next hs ?_ edge (ih old fresh shape good nextSeen)
    intro src len dst count instr
    refine ⟨checked src len dst count instr,?_⟩
    exact good.query_edge_recent shape seen instr edge tail.forget.plain

/-- Strengthen an entire relocatable segment on its true final transcript. -/
theorem mark_named_segment {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}
    {physical : QueryMark ℚ} {seg : Segment} {o : ScalarOracle ℚ} {P : Memory ℚ → Prop}
    {m t : Memory ℚ} {before final : Contract.History ℚ} {k : ℕ}
    (run : MarkedRuns physical seg o P m before k t final)
    (traffic : ∃ fresh, final=fresh++before ∧ NamedTraffic D E fresh) :
    MarkedRuns (namedMark D E physical) seg o P m before k t final := by
  obtain ⟨fresh,shape,known⟩ := traffic
  intro p pc code
  exact mark_named_run (run p pc code) before fresh shape known ⟨[],rfl⟩

end Geometry
end LinearProgramming
end Optimization
end OAI
