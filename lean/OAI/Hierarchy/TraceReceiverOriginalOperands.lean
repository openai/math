import OAI.Hierarchy.HistorySelectedLeafBuild
import OAI.Hierarchy.TraceReceiverSeedForestReads
import OAI.Hierarchy.HistorySelectedPairWidths

namespace OAI
/-! # Actual leaf operands for the selected history of the original verifier -/

namespace Hierarchy.TraceReceiverOriginal
open ThreeFlat Diagonal Diagonal.TickWorkspace Diagonal.HistoryContraction
open Diagonal.PhysicalStage Diagonal.NavigationPass Diagonal.TraceBitHeader
open RAM RAM.HistoryInitialSeed RAM.HistoryStageBody.Physical RAM.HistoryNodeDirectory
open RAM.HistoryNodeDirectory.Selected RAM.NavigationNodeRows RAM.TraceBucketAtom RAM.HistoryPartyBatchExec
open RAM.HistoryStageSetup
open Computability.VPVNP.BurstRAM PrivateRAM GridThrough HistorySelectedSeed TraceReceiverSeedWords
open scoped Fin.CommRing
noncomputable section

variable {F : Type} [Field F] [Fintype F] {W u pc regs slots S base k low fuel c n bnd : ℕ}
    (M : Machine W pc regs slots) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F≤2^W) (st : Word W) (B : Block F) (hk : 2≤k+1)
    (v : PairedCursor.Site (k+1)) (raw dict masks gateBase : ℕ)
set_option quotPrecheck false
local notation "depth" => (k+1)+low
local notation "G" => TraceStaticRow.gateTable hF t.width t.labels base fuel st regs slots depth
local notation "N" => TraceBitHeader.network hF t.width t.labels base st t.header t.time regs slots depth
local notation "ids" => gateBase+FixedTraceImage.count G
local notation "ROM" => (⟨raw,(N).cells,ids+(G).cells⟩ : TraceRawLookup.Layout)
local notation "shape" => bucketShape (q:=k) (low:=low) (S:=S) (f:=fuel) hF t.width t.labels base st
    regs slots B.cursorCopies raw dict masks ids
local notation "Y" => initial u shape
local notation "U" => width M t hF st
local notation "L" => wordsLayout M t hF st B hk
local notation "T" => forest M t hF st B hk
local notation "work" => start M t hF st B hk v
local notation "count" => pairs M t hF st v

def pin {axes n q d factors : ℕ} (Q : FactorPinIntervals.Layout (Cell axes n×Fin q) S factors d)
    (e : Σ x:PairedCursor.Site (k+1),Fin (U x)) : ℕ :=
  2+(Q.slot (source M t hF st e.1 e.2)).val

variable {axes side q d factors : ℕ} (Q : FactorPinIntervals.Layout (Cell axes side×Fin q) S factors d)
    (a : Diagonal.NavigationPass.Archive) (rank : Fin a.initialSites) (b : Banks)
    (rest : Fin 1→Word W) (j : Fin n) (D : Directory W n)
    (values : Fin n→NodeValue F) (warm prev issued : Memory W)
local notation "z" => archivedSite a rank (U v)
local notation "entry" => bump (ownerData W u) prev
local notation "curNode" => Run.nodeOfSite L T (fun x i=>(⟨x,i⟩ : Σ y:PairedCursor.Site (k+1), Fin (U y))) v

/-- This provides the operand used by chronological dispatch at an original
site. Its virtual network and input pointers come from the original verifier,
the native interval scan, and the actual compact header. -/
def operands (owner : ℕ→Fin factors) (origin : ∀i:Fin S,Q.origin i=owner (i.val/(2*2^low)))
    (room : d≤2^W) (even : Even S)
    (live : Ledger u D tableId values (TickTerminalRoot.slotKeep u) warm j.val prev)
    (number : j.val=a.cursor.node+rank.val) (early : j.val<c)
    (lane : (z).lane=(finFunctionFinEquiv v.2).val) (time : (z).stage=v.1.val)
    (mounted : DirectoryRow b a.seedLayer rank warm) (nodes : b.nodes=TickWorkspace.base u 44)
    (unit : 0<b.unitWork) (charge : warm (b.charges+2*j.val+1)=(count:Word W))
    (bill : archiveColumn b (numeric issued) j.val 0=b.unitWork*work) (smallWork : 4*work≤volume u)
    (kernel : ∀ col : Fin 5,warm (a.initialRecords+5*rank.val+col.val)=
      ((![(a.seed),rank.val,0,rank.val%a.remainingLanes,rank.val/a.remainingLanes] : Fin 5→ℕ) col : Word W))
    (guard : warm (b.nodes+8*j.val)=0)
    (kernelHigh : TickWorkspace.base u 19≤a.initialRecords) (word : TickWorkspace.base u 19<2^W)
    (nodeFit : TickWorkspace.base u 44+8*j.val+7<2^W) (kernelFit : a.initialRecords+5*rank.val+4<2^W)
    (laneFit : (z).lane<2^W) (stageFit : (z).stage<2^W)
    (volumeRoom : 2≤volume u) (scratch : volume u+42≤ TickWorkspace.stride u)
    (stream : TickWorkspace.base u 12+(j.val+1)*(volume u)^2≤TickWorkspace.base u 13)
    (results : TickWorkspace.base u 13+8*j.val+8≤TickWorkspace.base u 14) (bins : 4*(z).lane+4≤ TickWorkspace.stride u)
    (value : values j=NodeValue.ofSite (curNode) (pin M t hF st Q)
      (streamAt u c j.val) (endsAt u c j.val))
    (offset : ∀ h : 0<U v,warm (TickWorkspace.base u 5+4*(finFunctionFinEquiv v.2).val+3)=
      ((Q.slot (source M t hF st v ⟨0,h⟩)).val:Word W))
    (image : HistorySelectedSeedDecode.Installed (q:=k) (low:=low) (S:=S) (f:=fuel)
      hF t.width t.labels base st t.header t.time regs slots t.grid raw dict masks gateBase hF entry)
    (size : HistorySelectedSeedDecode.Fits (q:=k) (low:=low) (S:=S) (f:=fuel) (b:=bnd) (W:=W)
      hF t.width t.labels base st t.header t.time regs slots B.cursorCopies raw dict masks gateBase)
    (template : Protected Y z gateBase (TraceReceiverTemplate.count G))
    (dictionary : Protected Y z dict (2^depth)) (mask : Protected Y z masks (1+(depth+depth))) :
    Operands shape ROM rest tableId entry values j b (numeric issued) u c := by
  have forestData:=TraceReceiverSeedForestReads.forest_receipt M t hF st B hk v raw dict masks gateBase
    Y z rest entry image size template dictionary mask rfl lane laneFit time stageFit rfl
  obtain ⟨arity,rows,hidden,rawRows⟩:=forestData
  obtain ⟨alive,ports,billed⟩:=seed_budget M t hF st B hk v
  have pos : 0 < TickWorkspace.stride u := by unfold TickWorkspace.stride; positivity
  have ctrl : TickWorkspace.base u 18<2^W :=
    (Nat.mul_le_mul_right _ (by decide : 19≤20)).trans_lt word
  have s5:=apart (u:=u) (by decide : 5<12)
  have kept : entry (TickWorkspace.base u 5+4*(finFunctionFinEquiv v.2).val+3)=
      warm (TickWorkspace.base u 5+4*(finFunctionFinEquiv v.2).val+3) := by
    apply NativeNavigation.bumped_kept live ctrl pos _ (.inl ?_)
    rw [lane] at bins
    omega
  apply buildOriginal a rank (curNode) (U v) shape ROM rest tableId (pin M t hF st Q)
    j D values warm prev issued b live number early mounted nodes count work unit charge
    (HistorySelectedPairWidths.exact_seed M t hF st even v) bill (by omega) billed ports smallWork kernel guard
    kernelHigh word nodeFit kernelFit laneFit stageFit volumeRoom scratch stream results bins value rfl
  · intro i
    change 2+(Q.slot (source M t hF st v i)).val=2+(entry (TickWorkspace.base u 5+4*(z).lane+3)).val+i.val
    rw [lane]
    exact source_pointer M t hF st Q owner origin v entry (TickWorkspace.base u 5) room
      (fun h=>kept.trans (offset h)) i
  · exact arity
  · exact rows
  · exact hidden
  · exact rawRows

end
end Hierarchy.TraceReceiverOriginal

end OAI
