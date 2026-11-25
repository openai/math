import OAI.Hierarchy.DescentNamedOriginalArchive
import OAI.Hierarchy.DescentSeedLocalEnumeration

namespace OAI
/-! The original per-site seed order, transported through the physically named first world. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentKernelHistory DescentColonies Chronology Catalyst
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ} {k s z wire : ℕ}

private def renamed_order {P : Type} {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    (a : Archive W) (sites : Equiv.Perm W.graph.Site) (edges : Equiv.Perm W.graph.Edge)
    (order : DescentLocalArchiveOrder.Local a.bit) :
    DescentLocalArchiveOrder.Local (renamedArchive a sites edges).bit :=
  fun v => order (sites.symm v)

private structure OrderTransfer where
  source : Type
  destination : Type
  move : source → destination

private def orderTransfer {P : Type} {d : ℕ} {bits : P → ℕ}
    {W V : MarkedWorld F d P bits} {a : Archive W} (pkg : ArchiveTransport a V) :
    OrderTransfer where
  source := DescentLocalArchiveOrder.Local a.bit
  destination := DescentLocalArchiveOrder.Local pkg.data.bit
  move := pkg.carry (fun _ b => DescentLocalArchiveOrder.Local b.bit)

namespace Origin
variable {cp pins : ℕ} {X : Approximation F cp pins}
variable {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
    (o : Origin (G:=G) (q:=q) (fee:=ε) (z:=z) (wire:=wire) X c digits)

include o in
private def orderFor : OrderTransfer := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let origin ← Lean.Meta.getFVarFromUserName `o
      let pkg ← Lean.instantiateMVars (← Lean.Meta.mkAppM ``Origin.archivePackage #[origin])
      let args := pkg.getAppArgs
      let decl ← Lean.getConstInfo ``Origin.archivePackage
      let mut result := decl.type
      for _ in args do
        match result.consumeMData with
        | .forallE _ _ body _ => result := body
        | _ => throwError "unexpected archivePackage telescope"
      let transport := result.consumeMData
      unless transport.isAppOf ``ArchiveTransport && transport.getAppArgs.size == 8 do
        throwError "unexpected archivePackage result type"
      let params := transport.getAppArgs.map fun e => e.instantiateRev args
      -- ArchiveTransport a V has its archive before the target world. orderTransfer
      -- quantifies its target world before its source archive.
      let params := params.extract 0 6 ++ #[params[7]!, params[6]!, pkg]
      goal.assign (Lean.mkAppN (Lean.mkConst ``orderTransfer) params)

private def physicalOrder :
    DescentLocalArchiveOrder.Local
      (renamedArchive (Chronology.seedArchive X S.copies s c) (site o.raw) (edge o.raw)).bit :=
  renamed_order (Chronology.seedArchive X S.copies s c) (site o.raw) (edge o.raw)
    (DescentLocalArchiveOrder.seed X S.copies s c)

set_option maxHeartbeats 400000 in
private def orderInput : (orderFor o).source := physicalOrder o

def localNodes : (orderFor o).destination := (orderFor o).move (orderInput o)

end Origin

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
