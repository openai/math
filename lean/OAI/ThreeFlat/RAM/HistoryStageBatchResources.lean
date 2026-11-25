import OAI.ThreeFlat.RAM.HistoryStageGenericLeafResources
import OAI.ThreeFlat.RAM.HistoryPartyBatchExec

namespace OAI
/-! # Static resources of the party batch -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section

def pairBase : HistoryPartyBatch.Layout := ⟨0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩

private def batchPrice (budget seed head cmdWork argWork result : ℕ) : ℕ :=
  10000 + budget + 4 * (seed + head + cmdWork + argWork + result)

def batchResources (checks : Bool) : ℕ :=
  batchPrice readyResources (HistoryPartyBatch.seedFormula pairBase checks).work
    (HistoryPartyHeader.formula checks).work HistoryBatchTape.rawCommand.work
    HistoryBatchTape.rawArguments.work (HistoryPartyBatch.resultWord pairBase).work

open private HistoryPartyBatchExec.Build.static_header_binds HistoryPartyBatchExec.Build.static_batch_binds
  from OAI.ThreeFlat.RAM.HistoryPartyBatchExec

open private price_transport from OAI.ThreeFlat.RAM.HistoryStageGenericLeafResources

private theorem batch_resource_sum {seed result header cmd args tape head cmdWork argWork budget : ℕ}
    (h : header ≤ head + 250) (commands : cmd ≤ cmdWork + 250) (arguments : args ≤ argWork + 250)
    (ready : tape ≤ budget) :
    ((11+4*seed+19+(11+4*header))+(18+4*cmd)) + ((18+4*args)+(tape+(18+4*result))) ≤
      batchPrice budget seed head cmdWork argWork result := by
  unfold batchPrice
  omega

set_option maxRecDepth 16000 in
private theorem seed_template_work (A B : HistoryPartyBatch.Layout) (checks : Bool) :
    (HistoryPartyBatch.seedFormula A checks).work = (HistoryPartyBatch.seedFormula B checks).work := rfl

private theorem result_template_work (A B : HistoryPartyBatch.Layout) :
    (HistoryPartyBatch.resultWord A).work = (HistoryPartyBatch.resultWord B).work := rfl

attribute [local irreducible] HistoryPartyBatch.seedFormula HistoryPartyBatch.resultWord
  HistoryPartyHeader.formula HistoryBatchTape.rawCommand HistoryBatchTape.rawArguments
  HistorySelectedOps.rows readyResources batchPrice

private theorem price_templates (budget seed seed' head cmd args result result' : ℕ)
    (hseed : seed = seed') (hresult : result = result') :
    batchPrice budget seed head cmd args result = batchPrice budget seed' head cmd args result' := by
  cases hseed
  cases hresult
  rfl

private theorem batch_resources_price (A : HistoryPartyBatch.Layout) (checks : Bool) :
    batchPrice readyResources (HistoryPartyBatch.seedFormula A checks).work (HistoryPartyHeader.formula checks).work
      HistoryBatchTape.rawCommand.work HistoryBatchTape.rawArguments.work (HistoryPartyBatch.resultWord A).work =
        batchResources checks := by
  unfold batchResources
  exact price_templates _ _ _ _ _ _ _ _ (seed_template_work A pairBase checks) (result_template_work A pairBase)

private theorem header_bound (W : ℕ) (A : HistoryPartyBatch.Layout) (checks : Bool) :
    (HistoryPartyBatch.actualHeader W A checks).binds ≤ (HistoryPartyHeader.formula checks).work + 250 := by
  rw [HistoryPartyBatchExec.Build.static_header_binds W 1 A pairBase checks, HistoryPartyBatch.actualHeader,
    Term.binds_instantiate, HeaderScan.binds_closed]
  apply Nat.add_le_add_left
  decide

private theorem job_bound (W : ℕ) (A : HistoryPartyBatch.Layout) (cmd : Bool) :
    (HistoryPartyBatch.batchTerm W A cmd).binds ≤
      (if cmd then HistoryBatchTape.rawCommand.work else HistoryBatchTape.rawArguments.work) + 250 := by
  rw [HistoryPartyBatchExec.Build.static_batch_binds W 1 A pairBase cmd]
  cases cmd <;> simp only [HistoryPartyBatch.batchTerm, Term.binds_instantiate, HeaderScan.binds_closed,
    Bool.false_eq_true, ite_false, ite_true]
  all_goals apply Nat.add_le_add_left; decide

private theorem batch_program_bound {W : ℕ} (seed result : Formula 1) (header cmd args : Term W 0 1)
    (dyadic tape : Procedure W) (seedBase batchBase : ℕ) (cursor : Word W) (head cmdWork argWork budget : ℕ)
    (dy : resources dyadic = 19) (h : header.binds ≤ head + 250) (c : cmd.binds ≤ cmdWork + 250)
    (a : args.binds ≤ argWork + 250) (ready : resources tape ≤ budget) :
    let boot := PhysicalInputPhases.writing (HeaderScan.closed seed) Fin.elim0 seedBase 37
    let headWrite := PhysicalInputPhases.writing header Fin.elim0 batchBase 26
    let commandScan := HeaderScan.procedure cursor 0 1 cmd
    let argScan := HeaderScan.procedure cursor 2 3 args
    let resultScan := HeaderScan.procedure cursor 6 7 (HeaderScan.closed result)
    resources ((((boot.seq dyadic).seq headWrite).seq commandScan).seq (argScan.seq (tape.seq resultScan))) ≤
      batchPrice budget seed.work head cmdWork argWork result.work := by
  simp only [resources_seq, resources_write, resources_scan, HeaderScan.binds_closed, dy, Nat.add_zero]
  exact batch_resource_sum h c a ready

private theorem native_batch_bound {W : ℕ} (A : HistoryPartyBatch.Layout) (checks : Bool) :
    resources (HistoryPartyBatch.procedure W A checks) ≤ batchPrice readyResources
      (HistoryPartyBatch.seedFormula A checks).work (HistoryPartyHeader.formula checks).work
      HistoryBatchTape.rawCommand.work HistoryBatchTape.rawArguments.work (HistoryPartyBatch.resultWord A).work := by
  unfold HistoryPartyBatch.procedure
  exact batch_program_bound (HistoryPartyBatch.seedFormula A checks) (HistoryPartyBatch.resultWord A)
    (HistoryPartyBatch.actualHeader W A checks) (HistoryPartyBatch.batchTerm W A true)
    (HistoryPartyBatch.batchTerm W A false) (HistoryPartyBatch.dyadic W A)
    (HistoryReadyTape.execute (HistorySelectedOps.rows (.literal (0 : Word W) : Term W 0 4) [])
      (Fin.last 0) (fun _ => ((A.seed+33 : ℕ) : Word W)))
    A.seed A.batch ((A.seed+28 : ℕ) : Word W) (HistoryPartyHeader.formula checks).work
    HistoryBatchTape.rawCommand.work HistoryBatchTape.rawArguments.work readyResources rfl
    (header_bound W A checks) (job_bound W A true) (job_bound W A false)
    (ready_resources (W := W) (fun _ : Fin 1 => ((A.seed+33 : ℕ) : Word W)))

theorem batch_resources {W : ℕ} (A : HistoryPartyBatch.Layout) (checks : Bool) :
    resources (HistoryPartyBatch.procedure W A checks) ≤ batchResources checks :=
  price_transport (resources (HistoryPartyBatch.procedure W A checks))
    (batchPrice readyResources (HistoryPartyBatch.seedFormula A checks).work (HistoryPartyHeader.formula checks).work
      HistoryBatchTape.rawCommand.work HistoryBatchTape.rawArguments.work (HistoryPartyBatch.resultWord A).work)
    (batchResources checks) (native_batch_bound A checks) (batch_resources_price A checks)


end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
