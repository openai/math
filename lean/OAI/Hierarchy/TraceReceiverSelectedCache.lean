import OAI.Hierarchy.TraceReceiverRootElectionCost
import OAI.Hierarchy.TraceReceiverRunRooms
import OAI.Hierarchy.HistorySelectedReached

namespace OAI
/-! # Native chronological publication of all actually elected compiled caches -/

namespace Hierarchy.TraceReceiverSelectedCache
open ThreeFlat Diagonal PhysicalStage NavigationPass HistoryContraction
open TickWorkspace RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.HistoryStageBody.Physical
open RAM.HistoryNodeDirectory RAM.HistoryNodeDirectory.Selected RAM.HistoryPartyBatchExec
open Computability.VPVNP.BurstRAM PrivateRAM HistorySelectedReceiverLoop TraceReceiverRunCost
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F Pins E : Type} [Field F] [Fintype F] {d l : ℕ} {A : State d l}
    (B : Block F) (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r) (C : r.Charges)
    (L : A.Words Pins) (tree : Forest F L.ports.form) (ptr : (Σ x:A.Site,Fin (L.ext x))→ℕ)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (zero : O.layer.first=0)
    {W T dim : ℕ} (ht : 0<T) (w u : ℕ) (b : Banks) (issued entry : Memory W)
    (stored : r.ArchiveRowsStored b (numeric issued) h C O p)
set_option quotPrecheck false
local notation "endLayer" => (r.finalArchive h C O p).1
local notation "n" => (endLayer).count
local notation "f" => (endLayer).first
local notation "total" => f+n
local notation "node" => r.archiveNode h J L tree C O p zero
local notation "seen" => numeric issued
local notation "chron" => r.archiveDirectory h C O p b seen stored zero f n rfl rfl
local notation "vals" => (fun j : Fin total=>NodeValue.ofSite (node j) ptr
  (streamAt u O.layer.count j.val) (endsAt u O.layer.count j.val))

variable (cost : Fin (r.finalArchive h C O p).1.count→Fin dim→ℕ)
    (tick : Fin T) (steps fee : ℕ)
local notation "owner" => (fun i : Fin n=>((FactorAllocation.owner ht w cost i).val:Word W))
local notation "dir" => TraceReceiverOwnerMount.directory chron owner (tick.val:Word W)
local notation "price" => B.nativeVisitCost steps fee b seen
local notation "arm" => (fun j : Fin total=>B.nativeArmTime steps fee b seen j.val)

/-- The only input specific to the currently visited node is its authentic
dispatch receipt. The running clock sums the actual assigned terminal factors
and includes the scan over every directory row. -/
theorem publish_at {priceUnit : ℕ} (bank : RAM.HistoryStageBody.Physical.Archive) (leaf : Procedure W) (fs : List Family)
    (tag : ((Fin 3→Bool)→F)→ℕ) (start pairs : A.Site→ℕ)
    (q : Fintype.card (r.plan.finish h).Site=n) (numbered : r.FinalNumbered h C O p)
    (charged : O.Charged b seen start pairs) (unit : 0<b.unitWork)
    (feeEnd : B.nativeVisitFee steps fee (r.endLevel h 0)≤priceUnit)
    (priced : ∀ j:Fin total,Run.PricedAt b seen fee steps (2^((3*u^10+4)/5)) j.val (node j))
    (wide : 2≤u) (volumeRoom : 162≤volume u) (scale : 2≤fee)
    (margin : 10*(steps+2)^2*fee≤b.unitWork)
    (geom : TraceReceiverRunRooms.Rooms u dir) (tickFit : T≤2^W)
    (mounted : Recorded (ownerData W u) dir entry)
    (length : (entry ((ownerData W u) 4).val).val+(entry ((ownerData W u) 5).val).val=total)
    (emitted : ∀j : Fin total,∀ m,Ledger u dir tag vals (TickTerminalRoot.slotKeep u) entry j.val m →
      picked dir j.val=true → Emitted (u:=u) bank leaf fs dir vals tag price arm (fun j _=>arm j) j
        (bump (ownerData W u) m)) :
    let tally:=fun i : Fin n=>priceUnit*r.chargeAt h C start ((TraceAdmission.Resources.indexEquiv r h q).symm i)
    let selectedRoots:=FactorAllocation.factors w cost (List.finRange n) tick
    (selected u bank leaf fs).Spec (·=entry)
      (fun _ out=>Ledger u dir tag vals (TickTerminalRoot.slotKeep u) entry total out)
      (17+24*total+(selectedRoots.map tally).sum) := by
  let tally:=fun i : Fin n=>priceUnit*r.chargeAt h C start ((TraceAdmission.Resources.indexEquiv r h q).symm i)
  have fits := fun j:Fin total=>
    TraceReceiverRunCost.sizes O.layer.count (node j) ptr b seen (priced j) wide volumeRoom scale margin
  have work (i:Fin n) : (∑j:{j:Fin total // (chron).root j=i.val},price j.val.val)≤tally i := by
    exact (archived_at B r h C O p b seen stored zero start pairs unit charged feeEnd i).trans_eq
      (congrArg (priceUnit*·) (registered_work r h C O p numbered start q i))
  have clock:=selected_sum ht w cost tick chron rfl (by have:=geom.room;omega) tickFit
    (fun j : Fin total=>price j.val) tally work
  apply HistorySelectedReceiverLoop.run (bank:=bank) (leaf:=leaf) (fs:=fs) (D:=dir) (values:=vals)
    (tag:=tag) («price»:=price) (seed:=arm) («arm»:=fun j _=>arm j) mounted length geom.room geom.different geom.counts geom.dirs geom.immutable
    (geom.aside vals fits) geom.wide geom.space geom.arena geom.cache geom.owners geom.persistent
    (fun j _=>fits j) emitted
  exact Nat.add_le_add_left clock _

theorem publish (bank : RAM.HistoryStageBody.Physical.Archive) (leaf : Procedure W) (fs : List Family)
    (tag : ((Fin 3→Bool)→F)→ℕ) (start pairs : A.Site→ℕ)
    (q : Fintype.card (r.plan.finish h).Site=n) (numbered : r.FinalNumbered h C O p)
    (charged : O.Charged b seen start pairs) (unit : 0<b.unitWork)
    (feeEnd : B.nativeVisitFee steps fee (r.endLevel h 0)≤b.unitWork)
    (priced : ∀ j:Fin total,Run.PricedAt b seen fee steps (2^((3*u^10+4)/5)) j.val (node j))
    (wide : 2≤u) (volumeRoom : 162≤volume u) (scale : 2≤fee)
    (margin : 10*(steps+2)^2*fee≤b.unitWork)
    (geom : TraceReceiverRunRooms.Rooms u dir) (tickFit : T≤2^W)
    (mounted : Recorded (ownerData W u) dir entry)
    (length : (entry ((ownerData W u) 4).val).val+(entry ((ownerData W u) 5).val).val=total)
    (emitted : ∀j : Fin total,∀ m,Ledger u dir tag vals (TickTerminalRoot.slotKeep u) entry j.val m →
      picked dir j.val=true → Emitted (u:=u) bank leaf fs dir vals tag price arm (fun j _=>arm j) j
        (bump (ownerData W u) m)) :
    let tally:=fun i : Fin n=>b.unitWork*r.chargeAt h C start ((TraceAdmission.Resources.indexEquiv r h q).symm i)
    let selectedRoots:=FactorAllocation.factors w cost (List.finRange n) tick
    (selected u bank leaf fs).Spec (·=entry)
      (fun _ out=>Ledger u dir tag vals (TickTerminalRoot.slotKeep u) entry total out)
      (17+24*total+(selectedRoots.map tally).sum) :=
  publish_at B r h J C L tree ptr O p zero ht w u b issued entry stored cost tick steps fee
    bank leaf fs tag start pairs q numbered charged unit feeEnd priced wide volumeRoom scale margin
    geom tickFit mounted length emitted

end
end Hierarchy.TraceReceiverSelectedCache

end OAI
