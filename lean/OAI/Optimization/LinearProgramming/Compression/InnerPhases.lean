import OAI.Optimization.LinearProgramming.Compression.InnerControl
import OAI.Optimization.LinearProgramming.Lattice.BitRoundingMachine

/-! Polynomial bit-stack procedures for the three branches of the minor service. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner

open OracleSpec ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit

noncomputable def roundStartP : Procedure Driver.inputCode Round.actionCode
    (fun x => Round.dispatch Driver.actualKernels (.inl x)) :=
  (Round.dispatchP Driver.actualKernelCode).comp
    (Driver.Probe.leftP (prodCode (id : Word → Word) Driver.carryCode) (identity Driver.inputCode))

noncomputable def roundResumeP : Procedure (prodCode (id : Word → Word) Driver.carryCode) Round.actionCode
    (fun x => Round.dispatch Driver.actualKernels (.inr x)) :=
  (Round.dispatchP Driver.actualKernelCode).comp
    (Driver.Probe.rightP Driver.inputCode (identity (prodCode (id : Word → Word) Driver.carryCode)))

private theorem graphStateCode : WordDialogue.stateCode RequestTable.inputCode RequestTable.Dialogue.carryCode =
    sumCode RequestTable.inputCode (prodCode (id : Word → Word) RequestTable.Dialogue.carryCode) := by
  funext s
  rcases s with s|⟨w,c⟩ <;> simp [WordDialogue.stateCode,sumCode,prodCode,pairBits,quoteBits_eq_frame]

private noncomputable def graphRawP :
    Procedure (sumCode RequestTable.inputCode (prodCode (id : Word → Word) RequestTable.Dialogue.carryCode))
      Graph.actionCode Graph.dispatch := graphStateCode ▸ Graph.dispatchP

noncomputable def graphStartP : Procedure RequestTable.inputCode Graph.actionCode
    (fun x => Graph.dispatch (.inl x)) :=
  graphRawP.comp (Driver.Probe.leftP (prodCode (id : Word → Word) RequestTable.Dialogue.carryCode) (identity RequestTable.inputCode))

noncomputable def graphResumeP : Procedure (prodCode (id : Word → Word) RequestTable.Dialogue.carryCode) Graph.actionCode
    (fun x => Graph.dispatch (.inr x)) :=
  graphRawP.comp (Driver.Probe.rightP RequestTable.inputCode (identity (prodCode (id : Word → Word) RequestTable.Dialogue.carryCode)))

noncomputable def routeGraphP : Procedure (prodCode Projector.rowCode Graph.actionCode) actionCode
    (fun x => routeGraph x.1 x.2) := by
  let yes := Driver.Probe.leftP (prodCode (id : Word → Word) carryCode) affineResultP
  let qs := prodCode (id : Word → Word) RequestTable.Dialogue.carryCode
  let gamma := first Projector.rowCode qs
  let z := second Projector.rowCode qs
  let w := (first (id : Word → Word) RequestTable.Dialogue.carryCode).comp z
  let k := (second (id : Word → Word) RequestTable.Dialogue.carryCode).comp z
  let c := Driver.Probe.rightP epochCarryCode (Driver.Probe.rightP requestCarryCode (gamma.pair k))
  let ask := Driver.Probe.rightP (id : Word → Word) (w.pair c)
  refine (Driver.casesWithP (false,([]:Rats),(0:ℚ)) (([]:Word),default) yes ask).congrFun ?_
  rintro ⟨gamma,v|⟨w,k⟩⟩ <;> rfl

noncomputable def routeRequestP : Procedure (prodCode requestContextCode Round.actionCode) actionCode
    (fun x => routeRequest x.1 x.2) := by
  let c := first requestContextCode intRowCode
  let x := (first inputCode Projector.rowCode).comp c
  let gamma := (second inputCode Projector.rowCode).comp c
  let dims := (first RoundingBudgets.inputsCode (prodCode boolCode Nat.bits)).comp x
  let row := normalizeRowP.comp (second requestContextCode intRowCode)
  let st := graphStartP.comp ((RoundingBudgets.gridInputP.comp dims).pair row)
  let done := routeGraphP.comp (gamma.pair st)
  let qs := prodCode intRowCode Driver.carryCode
  let ctx := first requestContextCode qs
  let q := second requestContextCode qs
  let a := (first intRowCode Driver.carryCode).comp q
  let k := (second intRowCode Driver.carryCode).comp q
  let resume := Driver.Probe.rightP epochCarryCode (Driver.Probe.leftP graphCarryCode (ctx.pair k))
  let ask := Driver.Probe.rightP (id : Word → Word) ((Driver.signPacketP.comp a).pair resume)
  refine (Driver.casesWithP ([]:Ints) (([]:Ints),default) done ask).congrFun ?_
  rintro ⟨ctx,v|⟨a,k⟩⟩ <;> rfl

noncomputable def routeEpochP : Procedure (prodCode inputCode Round.actionCode) actionCode
    (fun x => routeEpoch x.1 x.2) := by
  let x := first inputCode intRowCode
  let gamma := normalizeRowP.comp (second inputCode intRowCode)
  let hdr := (second RoundingBudgets.inputsCode (prodCode boolCode Nat.bits)).comp x
  let member := (first boolCode Nat.bits).comp hdr
  let rank := (second boolCode Nat.bits).comp hdr
  let value := (listGet ratCode (0:ℚ)).comp (rank.pair gamma)
  let hit := Driver.Probe.leftP (prodCode (id : Word → Word) carryCode) (someWordP.comp value)
  let dims := (first RoundingBudgets.inputsCode (prodCode boolCode Nat.bits)).comp x
  let start := roundStartP.comp (RoundingBudgets.requestInputP.comp dims)
  let miss := routeRequestP.comp ((x.pair gamma).pair start)
  let done := conditional member hit miss
  let qs := prodCode intRowCode Driver.carryCode
  let ctx := first inputCode qs
  let q := second inputCode qs
  let a := (first intRowCode Driver.carryCode).comp q
  let k := (second intRowCode Driver.carryCode).comp q
  let resume := Driver.Probe.leftP (sumCode requestCarryCode graphCarryCode) (ctx.pair k)
  let ask := Driver.Probe.rightP (id : Word → Word) ((Driver.signPacketP.comp (padRowP.comp a)).pair resume)
  refine (Driver.casesWithP ([]:Ints) (([]:Ints),default) done ask).congrFun ?_
  rintro ⟨⟨⟨n,g⟩,b,r⟩,v|⟨a,k⟩⟩
  · cases b <;> rfl
  · rfl

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
