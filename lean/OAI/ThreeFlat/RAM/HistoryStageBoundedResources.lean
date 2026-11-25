import OAI.ThreeFlat.RAM.HistoryStageGenericLeafResources
import OAI.ThreeFlat.RAM.HistoryBoundedBody

namespace OAI
/-! # Static resources of the bounded join -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section

private def joinPrice (ready seed save commands arguments : ℕ) : ℕ :=
  10000+ready+4*(seed+save+commands+arguments)

noncomputable def joinResources (k : ℕ) :=
  let b : HistoryBoundedBody.Layout := ⟨0,0,0⟩
  joinPrice readyResources (HistoryBoundedBody.boot b).work (HistoryBoundedBody.result b k).work
    (HistoryBoundedJoin.formula k true).work (HistoryBoundedJoin.formula k false).work

private theorem bounded_scalar_cost (ready seed save cmd arg cmdWork argWork tape : ℕ)
    (commandCost : cmd ≤ cmdWork+250) (argumentCost : arg ≤ argWork+250) (tapeCost : tape ≤ ready) :
    (((11+4*seed+0)+(18+4*cmd))+(18+4*arg))+(tape+(18+4*save)) ≤
      joinPrice ready seed save cmdWork argWork := by
  unfold joinPrice
  omega

private theorem bounded_program_cost {W : ℕ} (origin : ℕ) (boot result : Formula 1)
    (commands arguments : Term W 0 1) (run : Procedure W)
    (ready seed save cmdWork argWork : ℕ)
    (bootCost : boot.work=seed) (saveCost : result.work=save)
    (cmdCost : commands.binds≤cmdWork+250) (argCost : arguments.binds≤argWork+250)
    (runCost : resources run≤ready) :
    let start := PhysicalInputPhases.writing (HeaderScan.closed boot) Fin.elim0 origin 9
    let cmd := HeaderScan.procedure (origin : Word W) 0 1 commands
    let arg := HeaderScan.procedure (origin : Word W) 2 3 arguments
    let finish := HeaderScan.procedure (origin : Word W) 4 5 (HeaderScan.closed result)
    resources (((start.seq cmd).seq arg).seq (run.seq finish)) ≤
      joinPrice ready seed save cmdWork argWork := by
  dsimp only
  simp only [resources_seq, resources_write, resources_scan, HeaderScan.binds_closed, bootCost, saveCost]
  exact bounded_scalar_cost ready seed save commands.binds arguments.binds cmdWork argWork
    (resources run) cmdCost argCost runCost

private theorem bounded_argument_cost {W : ℕ} (hub commands argument : Word W)
    (q : Bool) (i : Fin 13) :
    (if i=0 then Term.literal hub else if i=5 then
      Term.binary .sub (.result 0) (if q then Term.literal commands else (Term.literal argument).load)
      else Term.literal 0 : Term W 0 1).binds ≤ 3 := by
  by_cases first : i=0
  · rw [ite_eq_left first]
    exact (by decide : 1 ≤ 3)
  · rw [ite_eq_right first]
    by_cases offset : i=5
    · rw [ite_eq_left offset]
      cases q
      · exact (Nat.le_refl 3)
      · exact (by decide : 2 ≤ 3)
    · rw [ite_eq_right offset]
      exact (by decide : 1 ≤ 3)

private theorem bounded_instantiate_cost {W : ℕ} (f : Formula 13) (args : Fin 13 → Term W 0 1)
    (small : ∀ i, (args i).binds ≤ 3) :
    ((HeaderScan.closed f).instantiate args).binds ≤ f.work + 250 := by
  rw [Term.binds_instantiate, HeaderScan.binds_closed]
  apply Nat.add_le_add_left
  calc
    ∑ i, (args i).binds ≤ ∑ _i : Fin 13, (3 : ℕ) := Finset.sum_le_sum (fun i _ => small i)
    _ ≤ 250 := by norm_num

private theorem bounded_generator_cost (W : ℕ) (A : HistoryBoundedBody.Layout) (k : ℕ) (q : Bool) :
    (HistoryBoundedBody.generator W A k q).binds ≤ (HistoryBoundedJoin.formula k q).work + 250 := by
  unfold HistoryBoundedBody.generator
  exact bounded_instantiate_cost (HistoryBoundedJoin.formula k q) _
    (bounded_argument_cost (W:=W) (A.hub : Word W) (A.commands : Word W) ((A.hub+5 : ℕ) : Word W) q)

private theorem bounded_boot_cost (A B : HistoryBoundedBody.Layout) :
    (HistoryBoundedBody.boot A).work=(HistoryBoundedBody.boot B).work := rfl

attribute [local irreducible] resources joinPrice readyResources HistoryReadyTape.execute
  HistorySelectedOps.rows HistoryBoundedJoin.formula HistoryBoundedBody.generator
  HistoryBoundedBody.boot HistoryBoundedBody.result

set_option maxRecDepth 12000 in
theorem bounded_resources {W : ℕ} (A : HistoryBoundedBody.Layout) (k : ℕ) :
    resources (HistoryBoundedBody.procedure W A k)≤joinResources k := by
  let b : HistoryBoundedBody.Layout := ⟨0,0,0⟩
  let data := fun _ : Fin 1 => ((A.seed+7 : ℕ) : Word W)
  let run := HistoryReadyTape.execute
    (HistorySelectedOps.rows (.literal (0 : Word W) : Term W 0 4) []) (Fin.last 0) data
  unfold HistoryBoundedBody.procedure joinResources
  exact bounded_program_cost A.seed (HistoryBoundedBody.boot A) (HistoryBoundedBody.result A k)
    (HistoryBoundedBody.generator W A k true) (HistoryBoundedBody.generator W A k false) run
    readyResources (HistoryBoundedBody.boot b).work (HistoryBoundedBody.result b k).work
    (HistoryBoundedJoin.formula k true).work (HistoryBoundedJoin.formula k false).work
    (bounded_boot_cost A b) (HistoryBoundedBody.result_work A b k)
    (bounded_generator_cost W A k true) (bounded_generator_cost W A k false)
    (ready_resources data)


end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
