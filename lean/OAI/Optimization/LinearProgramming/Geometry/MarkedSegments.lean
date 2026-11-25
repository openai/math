import OAI.Optimization.LinearProgramming.Geometry.MarkedRun

/-! Composition of per-query ABI certificates through relocatable arithmetic-oracle code. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace OracleSegments

open RAM RAM.Block Contract

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

abbrev MarkedRuns (mark : QueryMark K) (seg : Segment) (o : ScalarOracle K) (P : Memory K → Prop)
    (m : Memory K) (hist : Contract.History K) (k : ℕ) (t : Memory K) (past : Contract.History K) : Prop :=
  ∀ (p : OracleProgram) (pc : ℕ), At p pc (seg.emit pc) →
    MarkedRun mark p o P ⟨m.atPC pc,hist⟩ k ⟨t.atPC (pc+seg.size),past⟩

namespace MarkedRuns
variable {mark : QueryMark K} {o : ScalarOracle K} {P Q : Memory K → Prop} {m t z : Memory K} {h h' h'' : Contract.History K} {k l : ℕ}

theorem forget {b : Segment} (x : MarkedRuns mark b o P m h k t h') : Runs b o P m h k t h' :=
  fun p pc code => (x p pc code).forget

theorem core {b : Block} (x : Eval P b m k t) (o : ScalarOracle K) (h : Contract.History K) :
    MarkedRuns mark (.core b) o P m h k t h := by
  intro p pc code
  have here : Contraction.Machine.CoreAt p pc (b.compile pc) := code
  exact MarkedRun.lift o h (x.compile_correct here.view) rfl

theorem query (src len dst count : ℕ) (o : ScalarOracle K) (h : Contract.History K)
    (m : Memory K) (hs : P m)
    (hout : P (received m dst count (o h (sentPacket m src len)))) (checked : mark m src len dst count) :
    let q := sentPacket m src len
    let a := o h q
    MarkedRuns mark (.query src len dst count) o P m h (1+q.length+a.length) (received m dst count a) ((q,a)::h) := by
  dsimp only
  intro p pc code
  have here : p[pc]? = some (.query src len dst count) := code.head
  have edge := Contraction.Machine.query_exchange p o (m.atPC pc) h here rfl
  have valid : CheckedEdge mark p ⟨m.atPC pc,h⟩ := by
    intro a b d e fetch
    change p[pc]?=some (.query a b d e) at fetch
    rw [here] at fetch
    cases fetch
    exact checked
  exact MarkedRun.next (k := 0) hs valid edge (.refl _ hout)

/-- The relocatable segment can also be exposed as a closed program with a final `halt`.
The raw oracle history is identical to that of the segment and the halt costs one. -/
theorem halted {b : Segment} (x : MarkedRuns mark b o P m h k t h') (tag : ℕ) :
    MarkedRun mark (b.emit 0 ++ [.core (.halt tag)]) o P ⟨m.atPC 0,h⟩ (k+1)
      ⟨{ t.atPC b.size with output := some tag },h'⟩ := by
  let p := b.emit 0 ++ [.core (.halt tag)]
  have code : At p 0 (b.emit 0) := ⟨[],[.core (.halt tag)],rfl,rfl⟩
  have first := x p 0 code
  rw [Nat.zero_add] at first
  have endPC : p[b.size]? = some (.core (.halt tag)) := by
    change (b.emit 0 ++ [.core (.halt tag)])[b.size]? = _
    rw [List.getElem?_append_right (le_of_eq (b.length_emit 0)), b.length_emit]; simp
  have last := Contraction.Machine.core_instruction p o (t.atPC b.size)
    {t.atPC b.size with output:=some tag} h' (.halt tag) endPC rfl rfl
  exact first.append (.next first.finish (MarkedRun.checked_core endPC) last (.refl _ first.finish))

theorem weaken {b : Segment} (x : MarkedRuns mark b o P m h k t h') (hp : ∀ v, P v → Q v) : MarkedRuns mark b o Q m h k t h' :=
  fun p pc code => (x p pc code).weaken hp

theorem start {b : Segment} (x : MarkedRuns mark b o P m h k t h') : P m :=
  (x (b.emit 0) 0 ⟨[],[],rfl,by simp⟩).start

theorem finish {b : Segment} (x : MarkedRuns mark b o P m h k t h') : P t :=
  (x (b.emit 0) 0 ⟨[],[],rfl,by simp⟩).finish

theorem seq {a b : Segment} (first : MarkedRuns mark a o P m h k t h') (second : MarkedRuns mark b o P t h' l z h'') :
    MarkedRuns mark (.seq a b) o P m h (k+l) z h'' := by
  intro p pc code
  change At p pc (a.emit pc ++ b.emit (pc+a.size)) at code
  have right := code.right
  rw [a.length_emit] at right
  simpa only [Segment.seq,Nat.add_assoc] using (first _ _ code.left).append (second _ _ right)

private theorem branch_parts {p : OracleProgram} {pc : ℕ} {c : Cond} {a b : Segment}
    (code : At p pc ((Segment.branch c a b).emit pc)) :
    p[pc]? = some (.core (c.instr (pc+1) (pc+1+a.size+1))) ∧ At p (pc+1) (a.emit (pc+1)) ∧
    p[pc+1+a.size]? = some (.core (.jump (pc+1+a.size+1+b.size))) ∧ At p (pc+1+a.size+1) (b.emit (pc+1+a.size+1)) := by
  have whole : At p pc (.core (c.instr (pc+1) (pc+1+a.size+1)) ::
      (a.emit (pc+1) ++ (.core (.jump (pc+1+a.size+1+b.size)) :: b.emit (pc+1+a.size+1)))) := by
    simpa [Segment.branch,List.append_assoc] using code
  have rest := whole.tail.right
  rw [a.length_emit] at rest
  exact ⟨whole.head,whole.tail.left,rest.head,rest.tail⟩

theorem branchTrue {a b : Segment} {c : Cond} (hc : c.test m = true) (run : MarkedRuns mark a o P m h k t h') :
    MarkedRuns mark (.branch c a b) o P m h (1+k+1) t h' := by
  intro p pc code
  obtain ⟨cond,ac,jmp,_⟩ := branch_parts code
  have mid := run _ _ ac
  have first := MarkedRun.guard_run (mark := mark) p o P m h c _ _ _ cond mid.start
  simp only [hc,ite_true] at first
  have last := MarkedRun.jump_run (mark := mark) p o P t h' _ _ jmp mid.finish
  simpa only [Segment.branch,Nat.add_assoc] using (first.append mid).append last

theorem branchFalse {a b : Segment} {c : Cond} (hc : c.test m = false) (run : MarkedRuns mark b o P m h k t h') :
    MarkedRuns mark (.branch c a b) o P m h (1+k) t h' := by
  intro p pc code
  obtain ⟨cond,_,_,bc⟩ := branch_parts code
  have mid := run _ _ bc
  have first := MarkedRun.guard_run (mark := mark) p o P m h c _ _ _ cond mid.start
  simp only [hc,Bool.false_eq_true,ite_false] at first
  simpa only [Segment.branch,Nat.add_assoc] using first.append mid

private theorem loop_parts {p : OracleProgram} {pc : ℕ} {c : Cond} {b : Segment}
    (code : At p pc ((Segment.loop c b).emit pc)) :
    p[pc]? = some (.core (c.instr (pc+1) (pc+1+b.size+1))) ∧ At p (pc+1) (b.emit (pc+1)) ∧
    p[pc+1+b.size]? = some (.core (.jump pc)) := by
  have whole : At p pc (.core (c.instr (pc+1) (pc+1+b.size+1)) :: (b.emit (pc+1) ++ [.core (.jump pc)])) := code
  have rest := whole.tail.right
  rw [b.length_emit] at rest
  exact ⟨whole.head,whole.tail.left,rest.head⟩

theorem loopFalse (c : Cond) (b : Segment) (hm : P m) (hc : c.test m = false) :
    MarkedRuns mark (.loop c b) o P m h 1 m h := by
  intro p pc code
  obtain ⟨cond,_,_⟩ := loop_parts code
  have x := MarkedRun.guard_run (mark := mark) p o P m h c _ _ _ cond hm
  simpa only [Segment.loop,hc,Bool.false_eq_true,ite_false,Nat.add_assoc] using x

theorem loopTrue {c : Cond} {b : Segment} (hc : c.test m = true) (x : MarkedRuns mark b o P m h k t h')
    (y : MarkedRuns mark (.loop c b) o P t h' l z h'') : MarkedRuns mark (.loop c b) o P m h (1+k+1+l) z h'' := by
  intro p pc code
  obtain ⟨cond,bc,jmp⟩ := loop_parts code
  have mid := x _ _ bc
  have first := MarkedRun.guard_run (mark := mark) p o P m h c _ _ _ cond mid.start
  simp only [hc,ite_true] at first
  have last := MarkedRun.jump_run (mark := mark) p o P t h' _ _ jmp mid.finish
  exact ((first.append mid).append last).append (y _ _ code)

end MarkedRuns
end OracleSegments
end Geometry
end LinearProgramming
end Optimization
end OAI
