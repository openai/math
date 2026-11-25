import OAI.Hierarchy.TraceReceiverDescendantExecution
import OAI.Hierarchy.TraceReceiverEntryFrame
import OAI.Hierarchy.TraceReceiverOwnerRegistered
import OAI.Hierarchy.TraceReceiverSelectedCache

namespace OAI
/-! # The complete chronological compiler on the receiver's own selected archive -/

namespace Hierarchy.TraceReceiverDescendantExecution
open ThreeFlat Diagonal PhysicalStage NavigationPass HistoryContraction
open TickWorkspace RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.HistoryStageBody.Physical
open RAM.HistoryNodeDirectory RAM.HistoryNodeDirectory.Selected RAM.HistoryPartyBatchExec
open Computability.VPVNP.BurstRAM PrivateRAM HistorySelectedReceiverLoop TraceReceiverRunCost
open GridRegisteredSetting TraceReceiverLeafSetup
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F Pins : Type} [Field F] [Fintype F] {w pc regs slots S baseAddr fuel axes : ℕ}
variable (D : RunData F (64*w) pc regs slots S baseAddr fuel axes (w/2)) (l : GridNativeImage.Layout)
variable {d depth : ℕ} {X : State d depth} (r : Run F X) (h : r.plan.History)
    (J : Run.WordSteps Pins r) (C : r.Charges) (L : X.Words Pins) (tree : Forest F L.ports.form)
    (ptr : (Σ x:X.Site, Fin (L.ext x))→ℕ) (O : X.ArchiveSites) (p : r.ArchivePath h C O)
    (zero : O.layer.first=0)
section Publication
set_option quotPrecheck false
local notation "W" => 64*w
local notation "u" => TraceAdmission.receiverAge w
local notation "B" => D.block
local notation "endRow" => (r.finalArchive h C O p).1
local notation "rootCount" => (endRow).count
local notation "first" => (endRow).first
local notation "total" => first+rootCount
local notation "A" => GridReceiverTickDirectory.banks w u
local notation "args" => GridStructuralHeader.parameters D.block (axes+1) D.passes l.selectorCap
  D.machine D.fit D.field D.state 0 (gateBase D)
local notation "nodes" => r.archiveNode h J L tree C O p zero
local notation "values" => (fun j : Fin total=>NodeValue.ofSite (nodes j) ptr
  (streamAt u O.layer.count j.val) (endsAt u O.layer.count j.val))

variable {T dim : ℕ} (ht : 0<T) (b : Banks) (saved reg assigned m : Memory (64*w))
    (stored : r.ArchiveRowsStored b (numeric saved) h C O p)
    (price : Fin (r.finalArchive h C O p).1.count→Fin dim→ℕ) (tick : Fin T) (steps fee : ℕ)
local notation "chron" => r.archiveDirectory h C O p b (numeric saved) stored zero first rootCount rfl rfl
local notation "owners" => (fun i : Fin rootCount=>((FactorAllocation.owner ht w price i).val:Word W))
local notation "dir" => TraceReceiverOwnerMount.directory chron owners (tick.val:Word W)
local notation "visit" => (B).nativeVisitCost steps fee b (numeric saved)
local notation "arm" => (fun j : Fin total=>(B).nativeArmTime steps fee b (numeric saved) j.val)

/-- Recover the guard from the genuine class/owner output, execute its reverse ancestor pass,
and use the charged word visits to publish every selected compiled node on this same memory. -/
theorem publish {pinCount priceUnit : ℕ} (P : GridPinPublisher.Plan)
    (textFit : SelfAdvice.textSize W pc slots≤w^2) (self : Fin (w^2)→Bool) (index : Word W)
    (sel : Fin (l.selectorCap+1)→Bool) (inBit : ℕ→Bool) (safe : ℕ)
    (headerFit : (GridReceiverHeader.header _ textFit self index args sel).length≤pinCount)
    (covered : 2+(GridReceiverHeader.header _ textFit self index args sel).length≤ safe)
    (read : ∀ i : Fin (GridReceiverHeader.header _ textFit self index args sel).length,
      inBit i.val=(GridReceiverHeader.header _ textFit self index args sel)[i.val])
    (frame : ∀ z,z< safe → m z=TickMountedPins.memory (w:=W) (fun j : Fin pinCount=>inBit j.val) z)
    (large : 7≤w) (depthFit : (axes+1)+w/2≤2*w+1) (small : templateSize D≤2^(w/100))
    (pinRoom : 2+pinCount≤ start w) (high : start w+libraryWords B W≤gateBase D)
    (room : start w+libraryWords B W<2^W)
    (ticks : P.ticks<2^W) (factors : P.factors<2^W) (lanes : P.lanes<2^W)
    (src : b.nodes=TickWorkspace.base u 44)
    (savedAt : ∀ a,TickWorkspace.base u 43≤a → a<TickWorkspace.base u 45 → reg a=saved a)
    (classed : GridSimulation.Assigned ht price reg assigned)
    (elected : GridReceiverTickDirectory.Ticked A (FactorAllocation.factors w price (List.finRange rootCount) tick)
      (tick.val:Word W) assigned m)
    (lower : 3*w≤u^10) (upper : u^10≤5*w) (wide : 128≤TickWorkspace.stride u) (past : 8*total≤TickWorkspace.stride u)
    (countFit : total≤2^(3*w/5)) (live : rootCount≤GridPinArena.slab w)
    (keep : ∀ a, TraceReceiverOwnerMount.Reads u first rootCount (A).owners ((A).scratch+1) a →
      sliced D P m a=m a)
    (tag : ((Fin 3→Bool)→F)→ℕ) (startCost pairs : X.Site→ℕ)
    (q : Fintype.card (r.plan.finish h).Site=rootCount) (numbered : r.FinalNumbered h C O p)
    (charged : O.Charged b (numeric saved) startCost pairs) (unit : 0<b.unitWork)
    (feeEnd : (B).nativeVisitFee steps fee (r.endLevel h 0)≤priceUnit)
    (priced : ∀ j : Fin total,Run.PricedAt b (numeric saved) fee steps (2^((3*u^10+4)/5)) j.val (nodes j))
    (age : 2≤u) (volumeRoom : 162≤RAM.HistoryStageBody.Physical.volume u) (scale : 2≤fee)
    (margin : 10*(steps+2)^2*fee≤b.unitWork) (tickFit : T≤2^W)
    (emitted : ∀ j : Fin total,∀ mem, Ledger u dir tag values (TickTerminalRoot.slotKeep u)
      (entry D first rootCount P m) j.val mem → picked dir j.val=true →
      Emitted («u»:=u) (bank D l) (leaf D) (families B (start w) W) dir values tag visit arm
        (fun j _=>arm j) j (bump (ownerData W u) mem)) :
    let tally:=fun i : Fin rootCount=>priceUnit*r.chargeAt h C startCost ((TraceAdmission.Resources.indexEquiv r h q).symm i)
    let selected:=FactorAllocation.factors w price (List.finRange rootCount) tick
    (program D l first rootCount P).Spec (·=m)
      (fun _ out=>Ledger u dir tag values (TickTerminalRoot.slotKeep u) (entry D first rootCount P m) total out)
      (cost D first rootCount P (17+24*total+(selected.map tally).sum)) := by
  intro tally selectedRoots
  obtain ⟨mounted,guard,length,_⟩ := TraceReceiverOwnerMount.registered_after r h C O p b
    saved reg assigned m stored zero rfl rfl src savedAt ht price tick classed elected
    (by omega) upper wide past live (sliced D P m) keep
  have geometry:=TraceReceiverRunRooms.native chron rfl owners (tick.val:Word W) (by omega) lower upper countFit
  intro machinePC machineRegs machineSlots machine
  refine execute D l (work:=17+24*total+(selectedRoots.map tally).sum) textFit self index sel inBit m safe headerFit covered read frame large depthFit small pinRoom
    high room ticks factors lanes mounted
    (fun out=>Ledger u dir tag values (TickTerminalRoot.slotKeep u) (entry D first rootCount P m) total out) ?_ machine
  intro loopPC loopRegs loopSlots loopMachine
  exact TraceReceiverSelectedCache.publish_at B r h J C L tree ptr O p zero ht w u b
    saved (entry D first rootCount P m) stored price tick steps fee (bank D l) (leaf D) (families B (start w) W)
    tag startCost pairs q numbered charged unit feeEnd priced age volumeRoom scale margin geometry tickFit
    guard length emitted loopMachine

end Publication

omit [Field F] [Fintype F] in
/-- Compose the final ledger's preservation with any of the established pre-loop memory frames. -/
theorem returned {W u n : ℕ} {dir : RAM.HistoryNodeDirectory.Selected.Directory W n} {tag : ((Fin 3→Bool)→F)→ℕ} {v : Fin n→NodeValue F}
    {initial entry final : Memory W} (published : Ledger u dir tag v (TickTerminalRoot.slotKeep u) entry n final)
    {addr : ℕ} (kept : TickTerminalRoot.slotKeep u addr) (before : entry addr=initial addr) :
    final addr=initial addr := (published.durable addr kept).trans before

end
end Hierarchy.TraceReceiverDescendantExecution

end OAI
