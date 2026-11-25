import OAI.Optimization.LinearProgramming.Geometry.OracleSegments

/-! Actual scalar-oracle runs carrying an additional precondition only at a genuine
query instruction. Ordinary arithmetic, control flow, costs, bounds and states are unchanged. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace OracleSegments

open RAM RAM.Block Contract

abbrev QueryMark (K : Type) := Memory K → ℕ → ℕ → ℕ → ℕ → Prop

def CheckedEdge {K : Type} (mark : QueryMark K) (p : OracleProgram) (s : Config K) : Prop :=
  ∀ src len dst count,p[s.state.pc]?=some (.query src len dst count) → mark s.state.memory src len dst count

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

inductive MarkedRun (mark : QueryMark K) (p : OracleProgram) (o : ScalarOracle K) (P : Memory K → Prop) :
    Config K → ℕ → Config K → Prop where
  | refl (s) (hs : P s.state.memory) : MarkedRun mark p o P s 0 s
  | next {s t z : Config K} {c k : ℕ} (hs : P s.state.memory) (checked : CheckedEdge mark p s)
      (edge : oracleStep p o s=some (c,t)) (rest : MarkedRun mark p o P t k z) : MarkedRun mark p o P s (c+k) z

namespace MarkedRun

variable {mark : QueryMark K} {p : OracleProgram} {o : ScalarOracle K} {P Q : Memory K → Prop}
  {s t z : Config K} {k l : ℕ}

theorem forget (h : MarkedRun mark p o P s k t) : SafeRun p o P s k t := by
  induction h with
  | refl _ hs => exact .refl _ hs
  | next hs _ edge _ ih => exact .next hs edge ih

theorem start (h : MarkedRun mark p o P s k t) : P s.state.memory := h.forget.start

theorem finish (h : MarkedRun mark p o P s k t) : P t.state.memory := h.forget.finish

theorem append (h : MarkedRun mark p o P s k t) (g : MarkedRun mark p o P t l z) :
    MarkedRun mark p o P s (k+l) z := by
  induction h with
  | refl => simpa using g
  | next hs checked edge _ ih => simpa only [Nat.add_assoc] using MarkedRun.next hs checked edge (ih g)

theorem weaken (h : MarkedRun mark p o P s k t) (hq : ∀ m,P m → Q m) : MarkedRun mark p o Q s k t := by
  induction h with
  | refl z hz => exact .refl _ (hq _ hz)
  | next hs checked edge _ ih => exact .next (hq _ hs) checked edge ih

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem checked_core {c : Config K} {i : Instr} (fetch : p[c.state.pc]?=some (.core i)) : CheckedEdge mark p c := by
  intro a b d e h
  rw [fetch] at h
  cases h

private theorem live_before {p : Program} {x y : State K} (h : step p x=some y) : x.output=none := by
  cases tag : x.output with
  | none => rfl
  | some i => simp [step,tag] at h

private theorem live_initial {p : Program} {P : State K → Prop} {x y : State K} {k : ℕ}
    (h : Execution p P x k y) (hy : y.output=none) : x.output=none := by
  cases h with
  | done => exact hy
  | next _ he _ => exact live_before he

private theorem ordinary (o : ScalarOracle K) (hist : Contract.History K) {p : OracleProgram} {s t : State K}
    (h : step (Contraction.Machine.coreView p) s=some t) (ht : t.output=none) :
    (∃ i,p[s.pc]?=some (.core i)) ∧ oracleStep p o ⟨s,hist⟩=some (1,⟨t,hist⟩) := by
  have hs := live_before h
  cases fetch : p[s.pc]? with
  | none => simp [Contraction.Machine.coreView,step,hs,fetch] at h
  | some instr =>
    cases instr with
    | core i =>
      exact ⟨⟨i,rfl⟩,Contraction.Machine.core_instruction p o s t hist i fetch hs
        (by simpa [Contraction.Machine.coreView,step,hs,fetch] using h)⟩
    | query a b c d =>
      have eq : { s with output:=some 0 }=t := by simpa [Contraction.Machine.coreView,step,hs,fetch,execInstr] using h
      subst t; simp at ht

theorem lift {p : OracleProgram} (o : ScalarOracle K) (hist : Contract.History K) {s t : State K} {k : ℕ}
    (h : Execution (Contraction.Machine.coreView p) (fun z => P z.memory) s k t) (ht : t.output=none) :
    MarkedRun mark p o P ⟨s,hist⟩ k ⟨t,hist⟩ := by
  induction h with
  | done s hs => exact .refl _ hs
  | next hs edge tail ih =>
    obtain ⟨⟨i,fetch⟩,step⟩ := ordinary o hist edge (live_initial tail ht)
    simpa only [Nat.one_add] using MarkedRun.next hs (checked_core fetch) step (ih ht)

theorem ctrl (p : OracleProgram) (o : ScalarOracle K) (P : Memory K → Prop) (m : Memory K)
    (hist : Contract.History K) {i : Instr} {pc dst : ℕ} (hpc : p[pc]?=some (.core i))
    (hi : execInstr i (m.atPC pc)=some (m.atPC dst)) (hs : P m) :
    MarkedRun mark p o P ⟨m.atPC pc,hist⟩ 1 ⟨m.atPC dst,hist⟩ :=
  .next hs (checked_core hpc) (Contraction.Machine.core_instruction p o _ _ hist _ hpc rfl hi) (.refl _ hs)

theorem guard_run (p : OracleProgram) (o : ScalarOracle K) (P : Memory K → Prop) (m : Memory K)
    (hist : Contract.History K) (c : Cond) (pc yes no : ℕ) (hpc : p[pc]?=some (.core (c.instr yes no)))
    (hs : P m) : MarkedRun mark p o P ⟨m.atPC pc,hist⟩ 1 ⟨m.atPC (if c.test m then yes else no),hist⟩ := by
  apply ctrl p o P m hist hpc _ hs
  cases c with
  | scalarLT i j => by_cases cmp : m.data i < m.data j <;> simp [Memory.atPC,Cond.instr,Cond.test,execInstr,cmp]
  | addrLT i j => by_cases cmp : m.index i < m.index j <;> simp [Memory.atPC,Cond.instr,Cond.test,execInstr,cmp]

theorem jump_run (p : OracleProgram) (o : ScalarOracle K) (P : Memory K → Prop) (m : Memory K)
    (hist : Contract.History K) (pc dst : ℕ) (hpc : p[pc]?=some (.core (.jump dst))) (hs : P m) :
    MarkedRun mark p o P ⟨m.atPC pc,hist⟩ 1 ⟨m.atPC dst,hist⟩ := ctrl p o P m hist hpc rfl hs

end MarkedRun
end OracleSegments
end Geometry
end LinearProgramming
end Optimization
end OAI
