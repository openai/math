import OAI.Optimization.LinearProgramming.Geometry.OracleSegments
import OAI.Optimization.LinearProgramming.RAM.Loops

/-! Fixed control flow for the geometric label call, including the two terminal tags. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelControl

open RAM RAM.Block Contract OracleSegments

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- An internal address register holds the comparison constant. -/
def marker (m : Memory K) : Memory K := m.putIndex 6 1

def setMarker : Block := .op (.addrConst 6 1)

/-- Execute the Gram and Frank–Wolfe block only following a completed row prefix. -/
def continuation (after : Block) : Segment :=
  .seq (.core setMarker) (.branch (.addrLT 139 6) (.core after) (.core .skip))

theorem continue_success (after : Block) (o : ScalarOracle K) (P : Memory K → Prop)
    (m t : Memory K) (h : Contract.History K) (k : ℕ) (persist : P m)
    (status : m.index 139 = 0) (run : Eval P after (marker m) k t) :
    Runs (continuation after) o P m h (k+3) t h := by
  have put : Eval P setMarker m 1 (marker m) := Eval.op_addrConst _ _ _ persist run.safe_start
  have guard : (Cond.addrLT 139 6).test (marker m) = true := by simp [Cond.test,marker,status]
  simpa only [continuation,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    (Runs.core put o h).seq (Runs.branchTrue (b := .core .skip) guard (Runs.core run o h))

theorem continue_restart (after : Block) (o : ScalarOracle K) (P : Memory K → Prop)
    (m : Memory K) (h : Contract.History K) (persist : P m) (hs : P (marker m))
    (status : m.index 139=1) : Runs (continuation after) o P m h 2 (marker m) h := by
  have put : Eval P setMarker m 1 (marker m) := Eval.op_addrConst _ _ _ persist hs
  have guard : (Cond.addrLT 139 6).test (marker m) = false := by simp [Cond.test,marker,status]
  exact (Runs.core put o h).seq (Runs.branchFalse (a := .core after) guard (Runs.core (.skip hs) o h))

/-- Status zero returns a label and a positive status propagates a compressor restart. -/
def tag (m : Memory K) : ℕ := if m.index 139=0 then 0 else 1

/-- The final guard and both halt branches use absolute PCs in one fixed instruction list. -/
def suffix (pc : ℕ) : OracleProgram :=
  [.core (.branchAddrLT 139 6 (pc+1) (pc+2)), .core (.halt 0), .core (.halt 1)]

def ready (seg : Segment) : Segment := .seq seg (.core setMarker)

def taggedProgram (seg : Segment) : OracleProgram := (ready seg).emit 0 ++ suffix (ready seg).size

/-- Close any relocatable label segment as an actual halted scalar-oracle program. The
three extra instructions are one register write, one guard and the selected halt. -/
theorem taggedProgram_run {seg : Segment} {o : ScalarOracle K} {P : Memory K → Prop}
    {m t : Memory K} {h final : Contract.History K} {k : ℕ}
    (run : Runs seg o P m h k t final) (hs : P (marker t)) :
    let u := marker t
    let last := (ready seg).size+1+tag t
    SafeRun (taggedProgram seg) o P ⟨m.atPC 0,h⟩ (k+3)
      ⟨{ u.atPC last with output := some (tag t) },final⟩ := by
  let s := ready seg
  let p := taggedProgram seg
  let u := marker t
  have put : Eval P setMarker t 1 u := Eval.op_addrConst _ _ _ run.finish hs
  have both : Runs s o P m h (k+1) u final := run.seq (Runs.core put o final)
  have here : At p 0 (s.emit 0) := ⟨[],suffix s.size,rfl,rfl⟩
  have prefixRun := both p 0 here
  rw [Nat.zero_add] at prefixRun
  have word (j : ℕ) : p[s.size+j]? = (suffix s.size)[j]? := by
    change (s.emit 0 ++ suffix s.size)[s.size+j]? = _
    rw [List.getElem?_append_right (by rw [s.length_emit]; omega), s.length_emit]
    simp
  have guardIndex : p[s.size]? = some (.core (.branchAddrLT 139 6 (s.size+1) (s.size+2))) := by
    simpa [suffix] using word 0
  have guardAction : execInstr (.branchAddrLT 139 6 (s.size+1) (s.size+2)) (u.atPC s.size) =
      some (u.atPC (s.size+1+tag t)) := by
    by_cases hz : t.index 139=0
    · simp [execInstr,Memory.atPC,u,marker,tag,hz]
    · simp [execInstr,Memory.atPC,u,marker,tag,hz]
  have guard := Contraction.Machine.core_instruction p o (u.atPC s.size)
    (u.atPC (s.size+1+tag t)) final _ guardIndex rfl guardAction
  have haltIndex : p[s.size+1+tag t]? = some (.core (.halt (tag t))) := by
    by_cases hz : t.index 139=0
    · simpa [tag,hz,suffix] using word 1
    · simpa [tag,hz,suffix,Nat.add_assoc] using word 2
  have halt := Contraction.Machine.core_instruction p o (u.atPC (s.size+1+tag t))
    {u.atPC (s.size+1+tag t) with output := some (tag t)} final _ haltIndex rfl rfl
  exact prefixRun.append (.next hs guard (.next hs halt (.refl _ hs)))

end LabelControl
end Geometry
end LinearProgramming
end Optimization
end OAI
