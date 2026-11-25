import OAI.Optimization.LinearProgramming.Contraction.MachineExchange

/-! Relocatable blocks of the genuine scalar-oracle RAM. Both clocks and the full answer
history survive composition, with a scalar memory invariant at every executed instruction. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace OracleSegments

open RAM RAM.Block Contract

/-- A fixed finite instruction block assembled at a supplied program counter. -/
structure Segment where
  size : ℕ
  emit : ℕ → OracleProgram
  length_emit (pc) : (emit pc).length = size

/-- Actual contiguous instruction slice at a known program counter. -/
def At (p : OracleProgram) (pc : ℕ) (part : OracleProgram) : Prop :=
  ∃ before after, before.length = pc ∧ p = before ++ part ++ after

namespace At
variable {p a b : OracleProgram} {pc : ℕ}

theorem head {i : OracleInstr} (h : At p pc (i :: a)) : p[pc]? = some i := by
  obtain ⟨pre,post,rfl,rfl⟩ := h
  simp

theorem left (h : At p pc (a++b)) : At p pc a := by
  obtain ⟨pre,post,he,rfl⟩ := h
  exact ⟨pre,b++post,he,by simp [List.append_assoc]⟩

theorem right (h : At p pc (a++b)) : At p (pc+a.length) b := by
  obtain ⟨pre,post,rfl,rfl⟩ := h
  exact ⟨pre++a,post,by simp,by simp [List.append_assoc]⟩

theorem tail {i : OracleInstr} (h : At p pc (i::a)) : At p (pc+1) a :=
  h.right (a := [i])

end At

namespace Segment

def core (b : RAM.Block) : Segment where
  size := b.size
  emit pc := (b.compile pc).map OracleInstr.core
  length_emit _ := by simp

/-- One genuine scalar exchange, charged for every transmitted and received word. -/
def query (src len dst count : ℕ) : Segment where
  size := 1
  emit _ := [.query src len dst count]
  length_emit _ := rfl

def seq (a b : Segment) : Segment where
  size := a.size+b.size
  emit pc := a.emit pc ++ b.emit (pc+a.size)
  length_emit _ := by simp [a.length_emit,b.length_emit]

def branch (c : Cond) (a b : Segment) : Segment where
  size := 1+a.size+1+b.size
  emit pc :=
    let endA := pc+1+a.size
    [.core (c.instr (pc+1) (endA+1))] ++ a.emit (pc+1) ++ [.core (.jump (endA+1+b.size))] ++ b.emit (endA+1)
  length_emit _ := by simp [a.length_emit,b.length_emit]; omega

def loop (c : Cond) (b : Segment) : Segment where
  size := 1+b.size+1
  emit pc := [.core (c.instr (pc+1) (pc+1+b.size+1))] ++ b.emit (pc+1) ++ [.core (.jump pc)]
  length_emit _ := by simp [b.length_emit]; omega

end Segment

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Each edge is a real `oracleStep`, including the full word cost of a query. -/
inductive SafeRun (p : OracleProgram) (o : ScalarOracle K) (P : Memory K → Prop) :
    Config K → ℕ → Config K → Prop where
  | refl (s : Config K) (hs : P s.state.memory) : SafeRun p o P s 0 s
  | next {s t z : Config K} {c k : ℕ} (hs : P s.state.memory)
      (edge : oracleStep p o s = some (c,t)) (rest : SafeRun p o P t k z) : SafeRun p o P s (c+k) z

namespace SafeRun
variable {p : OracleProgram} {o : ScalarOracle K} {P Q : Memory K → Prop} {s t z : Config K} {k l : ℕ}

theorem plain (h : SafeRun p o P s k t) : OracleRun p o s k t := by
  induction h with
  | refl => exact .refl _
  | next hs edge tail ih => exact .next edge ih

theorem start (h : SafeRun p o P s k t) : P s.state.memory := by cases h <;> assumption

theorem finish (h : SafeRun p o P s k t) : P t.state.memory := by induction h <;> assumption

theorem append (h : SafeRun p o P s k t) (g : SafeRun p o P t l z) : SafeRun p o P s (k+l) z := by
  induction h with
  | refl => simpa using g
  | next hs edge tail ih => simpa only [Nat.add_assoc] using SafeRun.next hs edge (ih g)

theorem weaken (h : SafeRun p o P s k t) (hq : ∀ m, P m → Q m) : SafeRun p o Q s k t := by
  induction h with
  | refl z hz => exact .refl _ (hq _ hz)
  | next hs edge tail ih => exact .next (hq _ hs) edge ih

private theorem live_before {p : Program} {x y : State K} (h : step p x = some y) : x.output = none := by
  cases ho : x.output with
  | none => rfl
  | some i => simp [step,ho] at h

private theorem live_initial {p : Program} {P : State K → Prop} {x y : State K} {k : ℕ}
    (h : Execution p P x k y) (hy : y.output = none) : x.output = none := by
  cases h with
  | done => exact hy
  | next _ he _ => exact live_before he

private theorem ordinary_edge (o : ScalarOracle K) (hist : Contract.History K) {p : OracleProgram}
    {s t : State K} (h : step (Contraction.Machine.coreView p) s = some t) (ht : t.output = none) :
    oracleStep p o ⟨s,hist⟩ = some (1,⟨t,hist⟩) := by
  have hs := live_before h
  cases hpc : p[s.pc]? with
  | none => simp [Contraction.Machine.coreView,step,hs,hpc] at h
  | some i => cases i with
    | core i =>
      exact Contraction.Machine.core_instruction p o s t hist i hpc hs (by simpa [Contraction.Machine.coreView,step,hs,hpc] using h)
    | query a b c d =>
      have he : { s with output:=some 0 } = t := by simpa [Contraction.Machine.coreView,step,hs,hpc,execInstr] using h
      subst t; simp at ht

theorem lift {p : OracleProgram} (o : ScalarOracle K) (hist : Contract.History K)
    {s t : State K} {P : Memory K → Prop} {k : ℕ}
    (h : Execution (Contraction.Machine.coreView p) (fun z => P z.memory) s k t) (ht : t.output = none) :
    SafeRun p o P ⟨s,hist⟩ k ⟨t,hist⟩ := by
  induction h with
  | done s hs => exact .refl _ hs
  | next hs edge tail ih =>
    simpa only [Nat.one_add] using SafeRun.next hs (ordinary_edge o hist edge (live_initial tail ht)) (ih ht)

private theorem ctrl (p : OracleProgram) (o : ScalarOracle K) (P : Memory K → Prop) (m : Memory K)
    (hist : Contract.History K) {i : Instr} {pc dst : ℕ} (hpc : p[pc]? = some (.core i))
    (hi : execInstr i (m.atPC pc) = some (m.atPC dst)) (hs : P m) :
    SafeRun p o P ⟨m.atPC pc,hist⟩ 1 ⟨m.atPC dst,hist⟩ :=
  .next hs (Contraction.Machine.core_instruction p o _ _ hist _ hpc rfl hi) (.refl _ hs)

private theorem guard_run (p : OracleProgram) (o : ScalarOracle K) (P : Memory K → Prop)
    (m : Memory K) (hist : Contract.History K) (c : Cond) (pc yes no : ℕ)
    (hpc : p[pc]? = some (.core (c.instr yes no))) (hs : P m) :
    SafeRun p o P ⟨m.atPC pc,hist⟩ 1 ⟨m.atPC (if c.test m then yes else no),hist⟩ := by
  apply ctrl p o P m hist hpc _ hs
  cases c with
  | scalarLT i j => by_cases cmp : m.data i < m.data j <;> simp [Memory.atPC,Cond.instr,Cond.test,execInstr,cmp]
  | addrLT i j => by_cases cmp : m.index i < m.index j <;> simp [Memory.atPC,Cond.instr,Cond.test,execInstr,cmp]

private theorem jump_run (p : OracleProgram) (o : ScalarOracle K) (P : Memory K → Prop)
    (m : Memory K) (hist : Contract.History K) (pc dst : ℕ)
    (hpc : p[pc]? = some (.core (.jump dst))) (hs : P m) :
    SafeRun p o P ⟨m.atPC pc,hist⟩ 1 ⟨m.atPC dst,hist⟩ := ctrl p o P m hist hpc rfl hs

end SafeRun

abbrev Runs (seg : Segment) (o : ScalarOracle K) (P : Memory K → Prop)
    (m : Memory K) (hist : Contract.History K) (k : ℕ) (t : Memory K) (past : Contract.History K) : Prop :=
  ∀ (p : OracleProgram) (pc : ℕ), At p pc (seg.emit pc) →
    SafeRun p o P ⟨m.atPC pc,hist⟩ k ⟨t.atPC (pc+seg.size),past⟩

/-- The exact memory action of a scalar-oracle reply. -/
def received (m : Memory K) (dst count : ℕ) (ans : List K) : Memory K :=
  (Contraction.Machine.receivePacket (m.atPC 0) dst count ans).memory

/-- A query packet is read solely from the public scalar and address banks. -/
def sentPacket (m : Memory K) (src len : ℕ) : List K :=
  Contraction.Machine.registerPacket (m.atPC 0) src len

namespace Runs
variable {o : ScalarOracle K} {P Q : Memory K → Prop} {m t z : Memory K} {h h' h'' : Contract.History K} {k l : ℕ}

theorem core {b : Block} (x : Eval P b m k t) (o : ScalarOracle K) (h : Contract.History K) :
    Runs (.core b) o P m h k t h := by
  intro p pc code
  have here : Contraction.Machine.CoreAt p pc (b.compile pc) := code
  exact SafeRun.lift o h (x.compile_correct here.view) rfl

theorem query (src len dst count : ℕ) (o : ScalarOracle K) (h : Contract.History K)
    (m : Memory K) (hs : P m)
    (hout : P (received m dst count (o h (sentPacket m src len)))) :
    let q := sentPacket m src len
    let a := o h q
    Runs (.query src len dst count) o P m h (1+q.length+a.length) (received m dst count a) ((q,a)::h) := by
  dsimp only
  intro p pc code
  have here : p[pc]? = some (.query src len dst count) := code.head
  have edge := Contraction.Machine.query_exchange p o (m.atPC pc) h here rfl
  exact SafeRun.next (k := 0) hs edge (.refl _ hout)

/-- The relocatable segment can also be exposed as a closed program with a final `halt`.
The raw oracle history is identical to that of the segment and the halt costs one. -/
theorem halted {b : Segment} (x : Runs b o P m h k t h') (tag : ℕ) :
    SafeRun (b.emit 0 ++ [.core (.halt tag)]) o P ⟨m.atPC 0,h⟩ (k+1)
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
  exact first.append (.next first.finish last (.refl _ first.finish))

theorem weaken {b : Segment} (x : Runs b o P m h k t h') (hp : ∀ v, P v → Q v) : Runs b o Q m h k t h' :=
  fun p pc code => (x p pc code).weaken hp

theorem start {b : Segment} (x : Runs b o P m h k t h') : P m :=
  (x (b.emit 0) 0 ⟨[],[],rfl,by simp⟩).start

theorem finish {b : Segment} (x : Runs b o P m h k t h') : P t :=
  (x (b.emit 0) 0 ⟨[],[],rfl,by simp⟩).finish

theorem seq {a b : Segment} (first : Runs a o P m h k t h') (second : Runs b o P t h' l z h'') :
    Runs (.seq a b) o P m h (k+l) z h'' := by
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

theorem branchTrue {a b : Segment} {c : Cond} (hc : c.test m = true) (run : Runs a o P m h k t h') :
    Runs (.branch c a b) o P m h (1+k+1) t h' := by
  intro p pc code
  obtain ⟨cond,ac,jmp,_⟩ := branch_parts code
  have mid := run _ _ ac
  have first := SafeRun.guard_run p o P m h c _ _ _ cond mid.start
  simp only [hc,ite_true] at first
  have last := SafeRun.jump_run p o P t h' _ _ jmp mid.finish
  simpa only [Segment.branch,Nat.add_assoc] using (first.append mid).append last

theorem branchFalse {a b : Segment} {c : Cond} (hc : c.test m = false) (run : Runs b o P m h k t h') :
    Runs (.branch c a b) o P m h (1+k) t h' := by
  intro p pc code
  obtain ⟨cond,_,_,bc⟩ := branch_parts code
  have mid := run _ _ bc
  have first := SafeRun.guard_run p o P m h c _ _ _ cond mid.start
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
    Runs (.loop c b) o P m h 1 m h := by
  intro p pc code
  obtain ⟨cond,_,_⟩ := loop_parts code
  have x := SafeRun.guard_run p o P m h c _ _ _ cond hm
  simpa only [Segment.loop,hc,Bool.false_eq_true,ite_false,Nat.add_assoc] using x

theorem loopTrue {c : Cond} {b : Segment} (hc : c.test m = true) (x : Runs b o P m h k t h')
    (y : Runs (.loop c b) o P t h' l z h'') : Runs (.loop c b) o P m h (1+k+1+l) z h'' := by
  intro p pc code
  obtain ⟨cond,bc,jmp⟩ := loop_parts code
  have mid := x _ _ bc
  have first := SafeRun.guard_run p o P m h c _ _ _ cond mid.start
  simp only [hc,ite_true] at first
  have last := SafeRun.jump_run p o P t h' _ _ jmp mid.finish
  exact ((first.append mid).append last).append (y _ _ code)

end Runs
end OracleSegments
end Geometry
end LinearProgramming
end Optimization
end OAI
