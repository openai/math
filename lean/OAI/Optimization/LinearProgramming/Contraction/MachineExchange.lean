import OAI.Optimization.LinearProgramming.Contraction.MachineCore
import OAI.Optimization.LinearProgramming.FieldTransfer.Execution

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Contraction
namespace Machine

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.Contract OAI.Optimization.LinearProgramming.FieldTransfer

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The raw input is read from one contiguous block. -/
def registerPacket (s : State K) (src len : ℕ) : List K :=
  List.ofFn fun j : Fin (s.index len) => s.data (s.index src + j.val)

/-- Receive an answer in consecutive scalar registers and its actual length in the address bank. -/
def receivePacket (s : State K) (dst len : ℕ) (answer : List K) : State K :=
  { s with
    pc := s.pc + 1
    index := Function.update s.index len answer.length
    data := fun j => if s.index dst ≤ j then answer[j-s.index dst]?.getD (s.data j) else s.data j }

/-- Execute the genuine oracle exchange, including all scalar words crossing the boundary. -/
theorem query_exchange (p : OracleProgram) (o : ScalarOracle K) (s : State K) (past : Contract.History K)
    {src len dst size : ℕ} (hpc : p[s.pc]? = some (.query src len dst size)) (live : s.output = none) :
    let sent := registerPacket s src len
    let ans := o past sent
    oracleStep p o ⟨s,past⟩ = some (1+sent.length+ans.length,⟨receivePacket s dst size ans,(sent,ans)::past⟩) := by
  simp [oracleStep, live, hpc, registerPacket, receivePacket]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem receivePacket_entry (s : State K) (dst size : ℕ) (answer : List K) (i : ℕ) (value : K)
    (hval : answer[i]? = some value) :
    (receivePacket s dst size answer).data (s.index dst + i) = value := by
  simp [receivePacket,hval]

/-- An already checked exact ordinary computation supplies a counted segment of an oracle run. -/
theorem lift_exact {p : OracleProgram} {s t : State K} {d : ℕ} (o : ScalarOracle K) (hist : Contract.History K)
    (h : runExactly (coreView p) s d = some t) (ht : t.output = none) :
    OracleRun p o ⟨s,hist⟩ d ⟨t,hist⟩ := by
  obtain ⟨trace, htr, hlast⟩ := (runExactly_iff_trace d).1 h
  apply lift_execution o hist (P := fun _ => True) _ ht
  rw [← hlast]
  exact Execution.of_trace htr (fun _ => True.intro)

theorem core_instruction (p : OracleProgram) (o : ScalarOracle K) (s t : State K) (hist : Contract.History K)
    (i : Instr) (atPC : p[s.pc]? = some (.core i)) (live : s.output = none) (he : execInstr i s = some t) :
    oracleStep p o ⟨s,hist⟩ = some (1,⟨t,hist⟩) := by
  simp [oracleStep,live,atPC,he]

end Machine
end Contraction
end LinearProgramming
end Optimization
end OAI
