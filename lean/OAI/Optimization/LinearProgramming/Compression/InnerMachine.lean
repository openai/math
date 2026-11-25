import OAI.Optimization.LinearProgramming.Compression.InnerPhases

/-! One finite bit program implements generator commitment, the hit fast path, request
rounding and the graph/grid branch. The only asks are signed rows for the shared cache. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner

open OracleSpec ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit

private noncomputable def initialP : Procedure inputEncoding actionCode
    (fun x => routeEpoch x (Round.dispatch Driver.actualKernels (.inl (epochInput x)))) := by
  let dims := (first RoundingBudgets.inputsCode (prodCode boolCode Nat.bits)).comp readInputP
  let start := roundStartP.comp (RoundingBudgets.epochInputP.comp dims)
  exact routeEpochP.comp (readInputP.pair start)

private noncomputable def resumeEpochP : Procedure (prodCode (id : Word → Word) epochCarryCode) actionCode
    (fun x => routeEpoch x.2.1 (Round.dispatch Driver.actualKernels (.inr (x.1,x.2.2)))) := by
  let w := first (id : Word → Word) epochCarryCode
  let z := second (id : Word → Word) epochCarryCode
  let i := (first inputCode Driver.carryCode).comp z
  let k := (second inputCode Driver.carryCode).comp z
  exact routeEpochP.comp (i.pair (roundResumeP.comp (w.pair k)))

private noncomputable def resumeRequestP : Procedure (prodCode (id : Word → Word) requestCarryCode) actionCode
    (fun x => routeRequest x.2.1 (Round.dispatch Driver.actualKernels (.inr (x.1,x.2.2)))) := by
  let w := first (id : Word → Word) requestCarryCode
  let z := second (id : Word → Word) requestCarryCode
  let ctx := (first requestContextCode Driver.carryCode).comp z
  let k := (second requestContextCode Driver.carryCode).comp z
  exact routeRequestP.comp (ctx.pair (roundResumeP.comp (w.pair k)))

private noncomputable def resumeGraphP : Procedure (prodCode (id : Word → Word) graphCarryCode) actionCode
    (fun x => routeGraph x.2.1 (Graph.dispatch (.inr (x.1,x.2.2)))) := by
  let w := first (id : Word → Word) graphCarryCode
  let z := second (id : Word → Word) graphCarryCode
  let gamma := (first Projector.rowCode RequestTable.Dialogue.carryCode).comp z
  let k := (second Projector.rowCode RequestTable.Dialogue.carryCode).comp z
  exact routeGraphP.comp (gamma.pair (graphResumeP.comp (w.pair k)))

noncomputable def dispatchP : WordDialogue.ProcedureOf inputEncoding carryCode dispatch := by
  let right := Driver.casesWithP (default:RequestCarry) (default:GraphCarry) resumeRequestP resumeGraphP
  let rest := Driver.casesWithP (default:EpochCarry) (Sum.inr (default:GraphCarry) : RequestCarry ⊕ GraphCarry) resumeEpochP right
  let raw := sumCode inputEncoding (prodCode (id : Word → Word) carryCode)
  have core : Procedure raw actionCode dispatch := by
    refine (casesSum initialP rest).congrFun ?_
    rintro (x|⟨w,c|c|c⟩) <;> rfl
  have hi : WordDialogue.stateCode inputEncoding carryCode = raw := by
    funext x; rcases x with i|⟨w,c⟩
    · rfl
    · simp [WordDialogue.stateCode,raw,sumCode,prodCode,pairBits,quoteBits_eq_frame]
  have ho : WordDialogue.actionCode carryCode = actionCode := by
    funext x; rcases x with w|⟨w,c⟩
    · rfl
    · simp [WordDialogue.actionCode,actionCode,sumCode,prodCode,pairBits,quoteBits_eq_frame]
  unfold WordDialogue.ProcedureOf
  rw [hi,ho]
  exact core

/-- The full binary control transition table is independent of every dimension and matrix. -/
noncomputable def machine : BitProgram := WordDialogue.machine dispatchP

/-- A realized session executes in the published finite machine and produces the complete
tagged rational output. The clock counts the rounds, the finite dispatcher and all wire copies. -/
theorem machine_of_session (o : WordOracle) {n g rank : ℕ} {member : Bool} {L rounds : ℕ}
    {answer : Option ℚ} {history : Transcript}
    (hs : WordDialogue.Session inputEncoding carryCode dispatch o L (.inl ((n,g),member,rank)) []
      (outputWord answer) history rounds) :
    machine.ComputesWithin o (inputWord n g member rank) (rounds*(dispatchP.shared.bound.eval L+18*L+18)+3)
      (fun actual out => actual=history ∧ out=outputWord answer) :=
  WordDialogue.machine_computes dispatchP o hs

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
