import OAI.Hierarchy.TraceReceiverElectedCache

namespace OAI
/-! # One public replay budget for any execution of the same chosen tick -/

namespace Hierarchy.TraceReceiverElectedCache
open ThreeFlat Diagonal PhysicalStage NavigationPass HistoryContraction NavigationDirectory
open NativeNavigation NodePublication RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.HistoryNodeDirectory
open RAM.HistoryNodeDirectory.Selected RAM.HistoryStageBody.Physical RAM.HistoryInitialSeed
open HistoryStageSetup HistoryPartyBatchExec TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM GridThrough FactorPinIntervals
open GridRegisteredSetting HistorySelectedReceiverLoop TraceReceiverLeafSetup
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
variable {F : Type} [Field F] [Fintype F] {w pc regs slots S addr fuel axes : ℕ}
variable (I : RunData F (64*w) pc regs slots S addr fuel axes (w/2)) (l : GridNativeImage.Layout)
local notation "u" => TraceAdmission.receiverAge w
local notation "W" => (64*w)
local notation "B" => I.block
local notation "M" => I.machine
local notation "ft" => I.fit
local notation "hF" => I.field
local notation "st" => I.state
local notation "hk" => I.axesFit
local notation "d" => (axes+1)+(w/2)
local notation "G" => TraceStaticRow.gateTable hF (ft).width (ft).labels addr fuel st regs slots d
local notation "O" => (GridReceiverDirectory.archive I l).cursorSeedSites B hk (w/2) (1+(d+d)) (G).cells rfl rfl
local notation "a" => GridReceiverDirectory.archive I l
local notation "dn" => GridReceiverDirectory.native I l
local notation "stop" => finish (a).K (dn).stages (a).cursor
local notation "b" => (dn).node.banks
local notation "phase" => ((B).repeat I.passes).length
local notation "P" => GridReceiverBanks.pinPlan I l
local notation "C" => I.issuedCharges
local notation "r" => I.run
local notation "K" => (B).localCoefficient*(W+1)^3
local notation "peak" => (2^((3*u^10+4)/5):ℕ)
local notation "L" => TraceReceiverSeedWords.wordsLayout M ft hF st B hk
local notation "trees" => TraceReceiverSeedWords.forest M ft hF st B hk
local notation "J" => (TraceReceiverCofinalPrices.assembly I).steps
local notation "T" => (l.sideMinusOne+1)^(l.dimension+1)*l.copies
local notation "full" => (2^(axes+1):ℕ)
local notation "dim" => (l.dimension+1)
local notation "g" => GridPinArena.slab w
local notation "radix" => (20*(w+1)+2)^(dim+2)
local notation "table" => TraceReceiverTablesMount.output I
local notation "fees" => I.issuedUnit w l.degree l.stageRate l.rootRate

variable {geom : GridReceiverDirectory.ElectionRoom I l} {safe : GridNativeDispatch.WordRoom I}
    {z : I.trace} {sel : Fin (l.selectorCap+1)→Bool}
    {t : Fin ((l.sideMinusOne+1)^(l.dimension+1)*l.copies)} {input origin elected : Memory (64*w)}
    (j : TraceReceiverElectedJournal.Journal I l geom safe z sel t input origin elected)
    (Q : FactorPinIntervals.Layout (Cell (l.dimension+1) l.sideMinusOne×Fin l.copies) S (I.roots z.1) l.pinWidth)
local notation "last" => ((r).finalArchive z.1 C O j.path).1
local notation "total" => (last).first+(last).count
local notation "costs" => I.costs (GridNativeImage.resources I l) z.1 l.dimension l.sideMinusOne l.bank C fees
local notation "price" => (fun i : Fin (last).count => costs (i.cast j.card.symm))
local notation "owners" => (fun i : Fin (last).count => ((FactorAllocation.owner geom.teams_pos w price i).val:Word W))
local notation "chron" => (r).archiveDirectory z.1 C O j.path b (numeric j.saved) j.stored rfl (last).first (last).count rfl rfl
local notation "D" => TraceReceiverOwnerMount.directory chron owners (t.val:Word W)
local notation "node" => (r).archiveNode z.1 J L trees C O j.path rfl
local notation "ptr" => TraceReceiverOriginal.pin M ft hF st Q
local notation "val" => (fun i : Fin total=>NodeValue.ofSite (node i) ptr (streamAt u (O).layer.count i.val)
    (endsAt u (O).layer.count i.val))
local notation "entry" => TraceReceiverDescendantExecution.entry I (last).first (last).count P elected
local notation "arm" => (fun i : Fin total=>(B).nativeArmTime phase K b (numeric j.saved) i.val)

local notation "basePay" => TraceReceiverSeedWords.start M ft hF st B hk
local notation "pairs" => TraceReceiverSeedWords.pairs M ft hF st
local notation "scalarFee" => (B).nativeVisitFee phase K ((r).endLevel z.1 0)
local notation "args" => GridStructuralHeader.parameters B (axes+1) I.passes l.selectorCap M ft hF st 0 (gateBase I)

/-- Chronological node identity drops out of the physical ordinal tariff. -/
def rootWork (z : I.trace) (t : Fin T) : ℕ :=
  let rates:=I.costs (GridNativeImage.resources I l) z.1 l.dimension l.sideMinusOne l.bank C fees
  let selected:=FactorAllocation.factors w rates (List.finRange (I.roots z.1)) t
  let charge:=fun f : Fin (I.roots z.1)=>(r).chargeAt z.1 C basePay ((TraceAdmission.Resources.indexEquiv r z.1 rfl).symm f)
  let fee:=(B).nativeVisitFee phase K ((r).endLevel z.1 0)
  (selected.map fun f=>fee*charge f).sum

theorem work_eq : work I l j=rootWork I l z t := by
  let run (n : ℕ) (bound : I.roots z.1=n) :=
    let px:=fun i : Fin n=>costs (i.cast bound.symm)
    let here:=FactorAllocation.factors w px (List.finRange n) t
    (here.map fun i=> scalarFee*(r).chargeAt z.1 C basePay ((TraceAdmission.Resources.indexEquiv r z.1 bound).symm i)).sum
  have same (n : ℕ) (bound : I.roots z.1=n) : run n bound=run (I.roots z.1) rfl := by
    subst n;rfl
  exact same (last).count j.card

/-- This budget has no input-memory argument. Every ranked quantity occurs at its physical root. -/
def replay (z : I.trace) (t : Fin T) :=
  TraceReceiverDescendantExecution.cost I (dn).parameters.firstFinal (dn).parameters.roots P
    (17+24*((dn).parameters.firstFinal+(dn).parameters.roots)+rootWork I l z t)

def cache (geom : GridReceiverDirectory.ElectionRoom I l) (safe : GridNativeDispatch.WordRoom I)
    (z : I.trace) (sel : Fin (l.selectorCap+1)→Bool) (t : Fin T) (input origin : Memory W)
    (Q : Layout (Cell dim l.sideMinusOne×Fin l.copies) S (I.roots z.1) l.pinWidth)
    (before final : Memory W) : Prop :=
  ∃ j : TraceReceiverElectedJournal.Journal I l geom safe z sel t input origin before,
    published I l j Q final ∧
    TraceReceiverEntryTables.TableFrame w u (libraryWords B W) before (table before) ∧
    GridPinPublisher.PrefixOwners P (table before) ∧
    ((r).finalArchive z.1 C O j.path).1.first+((r).finalArchive z.1 C O j.path).1.count≤2^(3*w/5)

/-- Keep the path, source registers and actual durable readbacks together when the final
root kernel is subsequently invoked on this memory. -/
theorem «seal» (frame : TraceReceiverEntryTables.TableFrame w u (libraryWords B W) elected (table elected))
    (prefixOwners : GridPinPublisher.PrefixOwners P (table elected)) (bound : total≤2^(3*w/5))
    (body : (TraceReceiverDescendantExecution.program I l (dn).parameters.firstFinal (dn).parameters.roots P).Spec
      (·=elected) (fun _ final=>published I l j Q final)
      (TraceReceiverDescendantExecution.cost I (dn).parameters.firstFinal (dn).parameters.roots P
        (17+24*total+work I l j))) :
    (TraceReceiverDescendantExecution.program I l (dn).parameters.firstFinal (dn).parameters.roots P).Spec
      (·=elected) (fun _ final=>cache I l geom safe z sel t input origin Q elected final) (replay I l z t) := by
  apply body.mono (fun _ h=>h) (fun _ _ done=>⟨j,done,frame,prefixOwners,bound⟩)
  unfold replay
  rw [j.first,j.roots,work_eq I l j]

end
end Hierarchy.TraceReceiverElectedCache

end OAI
