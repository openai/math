import OAI.Optimization.LinearProgramming.Geometry.MarkedSegments
import OAI.Optimization.LinearProgramming.Geometry.OracleUnique

/-! A previously proved ordinary-numeric segment may be marked without replaying its
arithmetic proof. In an ambient program, temporarily replace every outside query by a halt;
a run ending live thereby consists entirely of actual ordinary instruction steps. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace OracleSegments

open RAM RAM.Block Contract Contraction.Machine

/-- Every instruction emitted by this relocatable segment belongs to the ordinary RAM. -/
def CoreOnly (seg : Segment) : Prop := ∀ pc i, i ∈ seg.emit pc → ∃ x, i=OracleInstr.core x

namespace CoreOnly

theorem core (b : Block) : CoreOnly (.core b) := by
  intro pc i hi
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
  exact ⟨j,rfl⟩

theorem seq {a b : Segment} (ha : CoreOnly a) (hb : CoreOnly b) : CoreOnly (.seq a b) := by
  intro pc i hi
  rcases List.mem_append.mp hi with h | h
  · exact ha _ _ h
  · exact hb _ _ h

theorem branch (c : Cond) {a b : Segment} (ha : CoreOnly a) (hb : CoreOnly b) : CoreOnly (.branch c a b) := by
  intro pc i hi
  simp only [Segment.branch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with (((rfl | h) | rfl) | h)
  · exact ⟨_,rfl⟩
  · exact ha _ _ h
  · exact ⟨_,rfl⟩
  · exact hb _ _ h

theorem loop (c : Cond) {b : Segment} (hb : CoreOnly b) : CoreOnly (.loop c b) := by
  intro pc i hi
  simp only [Segment.loop,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with ((rfl | h) | rfl)
  · exact ⟨_,rfl⟩
  · exact hb _ _ h
  · exact ⟨_,rfl⟩

end CoreOnly

private def scrub (p : OracleProgram) : OracleProgram := (coreView p).map OracleInstr.core

private theorem scrub_pure (seg : Segment) (hg : CoreOnly seg) (pc : ℕ) : scrub (seg.emit pc)=seg.emit pc := by
  unfold scrub coreView
  rw [List.map_map]
  conv_rhs => rw [←List.map_id (l := seg.emit pc)]
  apply List.map_congr_left
  intro i hi
  obtain ⟨x,rfl⟩ := hg _ _ hi
  rfl

private theorem scrub_code {p : OracleProgram} {pc : ℕ} {seg : Segment}
    (code : At p pc (seg.emit pc)) (pure : CoreOnly seg) : At (scrub p) pc (seg.emit pc) := by
  obtain ⟨pre,post,rfl,rfl⟩ := code
  refine ⟨scrub pre,scrub post,by simp [scrub,coreView],?_⟩
  have eq := scrub_pure seg pure pre.length
  simpa [scrub,coreView] using congrArg (fun l => scrub pre ++ l ++ scrub post) eq

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem ordinary_edge {p : Program} {o : ScalarOracle K} {s t : Config K} {k : ℕ}
    (edge : oracleStep (p.map OracleInstr.core) o s=some (k,t)) :
    k=1 ∧ t.history=s.history ∧ step p s.state=some t.state := by
  obtain ⟨z,hist⟩ := s
  cases out : z.output with
  | some q => simp [oracleStep,out] at edge
  | none =>
    cases ins : p[z.pc]? with
    | none => simp [oracleStep,out,List.getElem?_map,ins] at edge
    | some i =>
      cases raw : execInstr i z with
      | none => simp [oracleStep,out,List.getElem?_map,ins,raw] at edge
      | some v =>
        simp [oracleStep,out,List.getElem?_map,ins,raw] at edge
        obtain ⟨rfl,rfl⟩ := edge
        exact ⟨rfl,rfl,by simp [step,out,ins,raw]⟩

private theorem ordinary_run {p : Program} {o : ScalarOracle K} {P : Memory K → Prop} {s t : Config K} {k : ℕ}
    (run : SafeRun (p.map OracleInstr.core) o P s k t) :
    t.history=s.history ∧ Execution p (fun z => P z.memory) s.state k t.state := by
  induction run with
  | refl s hs => exact ⟨rfl,.done _ hs⟩
  | next hs edge _ ih =>
    obtain ⟨rfl,hist,step⟩ := ordinary_edge edge
    exact ⟨ih.1.trans hist,by simpa only [Nat.one_add] using Execution.next hs step ih.2⟩

/-- This principle applies directly to an already checked numerical suffix with arbitrary
branches and loops as soon as its finite instruction list has no query. -/
theorem MarkedRuns.of_coreOnly {mark : QueryMark K} {seg : Segment} {o : ScalarOracle K}
    {P : Memory K → Prop} {m t : Memory K} {hist final : Contract.History K} {k : ℕ}
    (pure : CoreOnly seg) (existing : Runs seg o P m hist k t final) : MarkedRuns mark seg o P m hist k t final := by
  intro p pc code
  obtain ⟨same,trace⟩ := ordinary_run (existing (scrub p) pc (scrub_code code pure))
  change final=hist at same
  subst final
  exact MarkedRun.lift o hist trace rfl

/-- Attach the local mark to an already-established one-query transition. The unique
cost, memory, and history of a terminating segment identify the same query execution. -/
theorem MarkedRuns.of_query {mark : QueryMark K} {o : ScalarOracle K} {P : Memory K → Prop}
    {m t : Memory K} {hist final : Contract.History K} {k src len dst cnt : ℕ}
    (existing : Runs (.query src len dst cnt) o P m hist k t final) (checked : mark m src len dst cnt) :
    MarkedRuns mark (.query src len dst cnt) o P m hist k t final := by
  have base := Runs.query (P := fun _ => True) src len dst cnt o hist m trivial trivial
  obtain ⟨cost,endState,endHistory⟩ := existing.unique base
  subst k t final
  exact MarkedRuns.query src len dst cnt o hist m existing.start existing.finish checked

end OracleSegments
end Geometry
end LinearProgramming
end Optimization
end OAI
