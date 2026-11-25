import OAI.Hierarchy.TraceReceiverOriginalFrame
import OAI.Hierarchy.TraceReceiverWarmEntry

namespace OAI
/-! # Genuine seed case of chronological cache dispatch on a registered receiver -/

namespace Hierarchy.TraceReceiverOriginal
open ThreeFlat Diagonal NavigationPass RAM PhysicalStage HistoryContraction
open Diagonal.TraceBitHeader TickWorkspace LaneCursor
open RAM.HistoryInitialSeed RAM.HistoryNodeDirectory RAM.HistoryNodeDirectory.Selected
open RAM.HistoryStageBody.Physical RAM.NavigationNodeRows RAM.TraceBucketAtom RAM.HistoryPartyBatchExec
open Computability.VPVNP.BurstRAM PrivateRAM GridThrough FactorPinIntervals TraceReceiverSeedWords HistorySelectedSeed
open scoped Fin.CommRing
noncomputable section

variable {F : Type} [Field F] [Fintype F] {W u pc regs slots S base k low fuel bnd : ℕ}
    (M : Machine W pc regs slots) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F≤2^W) (st : Word W) (B : Block F) (hk : 2≤k+1)
    (raw dict masks gateBase : ℕ)
set_option quotPrecheck false
local notation "depth" => (k+1)+low
local notation "G" => TraceStaticRow.gateTable hF t.width t.labels base fuel st regs slots depth
local notation "N" => TraceBitHeader.network hF t.width t.labels base st t.header t.time regs slots depth
local notation "ids" => gateBase+FixedTraceImage.count G
local notation "shape" => bucketShape (q:=k) (low:=low) (S:=S) (f:=fuel) hF t.width t.labels base st
    regs slots B.cursorCopies raw dict masks ids
local notation "ROM" => (⟨raw,(N).cells,ids+(G).cells⟩ : TraceRawLookup.Layout)
local notation "Y" => initial u shape
local notation "off" => 1+(depth+depth)
local notation "X" => B.cursorState hk low off (G).cells
local notation "L" => wordsLayout M t hF st B hk
local notation "T" => forest M t hF st B hk
local notation "U" => width M t hF st
local notation "work" => start M t hF st B hk
local notation "paired" => pairs M t hF st
local notation "ins" => HistorySelectedSeedDecode.Installed (q:=k) (low:=low) (S:=S) (f:=fuel)
    hF t.width t.labels base st t.header t.time regs slots t.grid raw dict masks gateBase hF

variable {axes side q d factors : ℕ} (Q : FactorPinIntervals.Layout (Cell axes side×Fin q) S factors d)
    (a : NavigationPass.Archive) (ax : k+1=a.axes) (lanes : a.remainingLanes=2^(k+1))
local notation "O" => a.cursorSeedSites B hk low off (G).cells ax lanes
variable (r : Run F (B.cursorState hk low (1+(((k+1)+low)+((k+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base fuel st regs slots ((k+1)+low)).cells))
    (h : r.plan.History) (J : Run.WordSteps (Fin S→Bool) r) (C : r.Charges)
    (p : r.ArchivePath h C (a.cursorSeedSites B hk low (1+(((k+1)+low)+((k+1)+low)))
      (TraceStaticRow.gateTable hF t.width t.labels base fuel st regs slots ((k+1)+low)).cells ax lanes))
    (zero : a.cursor.node=0)
local notation "total" => (r.finalArchive h C O p).1.first+(r.finalArchive h C O p).1.count
local notation "selectedNode" => r.archiveNode h J L T C O p zero
local notation "V" => volume u
local notation "vals" => (fun j : Fin total=>NodeValue.ofSite (selectedNode j) (pin M t hF st Q)
    (streamAt u (O).layer.count j.val) (endsAt u (O).layer.count j.val))
local notation "xs" => r.archiveList h C O p a.seedData
local notation "seedNode" => Run.nodeOfSite L T (fun x i=>(⟨x,i⟩ : Σ y:PairedCursor.Site (k+1),Fin (U y)))

include zero

/-- All site-specific premises of the native seed arm, including its work
and pin counts, are obtained from the same selected typed archive. The
remaining sizes are common bounds for the whole allocated receiver. -/
theorem original {K levels peak : ℕ} (b : Banks) (mid issued warm : Memory W)
    (rest : Fin 1→Word W) (D : Directory W total)
    (owner : ℕ→Fin factors) (origin : ∀i:Fin S,Q.origin i=owner (i.val/(2*2^low)))
    (pinFit : d≤2^W) (even : Even S) (unit : 0<b.unitWork)
    (charged : (O).Charged b (numeric issued) work paired)
    (published : NativeNavigation.WarmSources u b xs mid issued warm)
    (nodeBase : b.nodes=TickWorkspace.base u 44) (chargeBase : b.charges=TickWorkspace.base u 43)
    (priced : ∀j:Fin total,Run.PricedAt b (numeric issued) K levels peak j.val (selectedNode j))
    (cap : 4*peak≤V)
    (savedKernel : ∀ i : Fin a.initialSites,∀ c : Fin 5,warm (a.initialRecords+5*i.val+c.val)=
      ((![(a.seed),i.val,0,i.val%a.remainingLanes,i.val/a.remainingLanes] : Fin 5→ℕ) c : Word W))
    (kernelHigh : TickWorkspace.base u 19≤a.initialRecords)
    (kernelsFit : a.initialRecords+5*a.initialSites<2^W) (chart : TickWorkspace.base u 45<2^W)
    (room : 4≤V) (scratch : V+42≤ TickWorkspace.stride u) (nodes : total≤V^2) (dirFit : 8*total≤ TickWorkspace.stride u)
    (laneRoom : 4*(2^(k+1))≤ TickWorkspace.stride u) (axisRoom : k+1≤2^W) (lanesFit : 2^(k+1)≤2^W)
    (gateHi : TickWorkspace.base u 19≤gateBase) (dictHi : TickWorkspace.base u 19≤dict)
    (masksHi : TickWorkspace.base u 19≤ masks) (romReady : ins warm)
    (fit : HistorySelectedSeedDecode.Fits (q:=k) (low:=low) (S:=S) (f:=fuel) (b:=bnd) (W:=W)
      hF t.width t.labels base st t.header t.time regs slots B.cursorCopies raw dict masks gateBase)
    (offset : ∀ v : PairedCursor.Site (k+1),∀ h : 0<U v,
      warm (TickWorkspace.base u 5+4*(finFunctionFinEquiv v.2).val+3)=
        ((Q.slot (source M t hF st v ⟨0,h⟩)).val:Word W))
    (v : PairedCursor.Site (k+1)) (j : Fin total) (prev : Memory W) (num : j.val=(O).id v)
    (leaf : selectedNode j=seedNode v)
    (reached : Ledger u D tableId vals (TickTerminalRoot.slotKeep u) warm j.val prev) :
    Nonempty (Operands shape ROM rest tableId (bump (ownerData W u) prev) vals j b (numeric issued) u
      (O).layer.count) := by
  let rank:=(O).ord v
  let z:=archivedSite a rank (U v)
  obtain ⟨index,lane,time⟩:=cursor_fields a B hk low off (G).cells ax lanes v (U v)
  have pos : 0< TickWorkspace.stride u:=by unfold TickWorkspace.stride;positivity
  have dir44:=apart (u:=u) (by decide : 44<45)
  have dir19:=apart (u:=u) (by decide : 19<45)
  have dir18:=apart (u:=u) (by decide : 18<19)
  have bound:=j.isLt
  have absolute : j.val=a.cursor.node+rank.val:=num
  have first : a.cursor.node=0:=zero
  have early : j.val<(O).layer.count:=by rw [absolute,first,zero_add];exact rank.isLt
  obtain ⟨dir,kind,cash,bill⟩:=archive_row a B hk low off (G).cells ax lanes v r h C p b mid issued warm
    work paired charged published chargeBase (by rw [←num];omega)
  have billed : archiveColumn b (numeric issued) j.val 0=b.unitWork*(work v) := by simpa only [num] using bill
  have small:=work_room (priced j) unit billed cap
  have s43 : warm (b.charges+2*j.val+1)=((paired v):Word W):=by simpa only [num] using cash
  have s44 : warm (b.nodes+8*j.val)=0:=by simpa only [num] using kind
  have spans:=selected_rooms j room nodes
  have src:=installed_at_entry M t hF st raw dict masks gateBase reached (by omega) romReady gateHi dictHi masksHi
  obtain ⟨ar,ports,treeCost⟩:=seed_budget M t hF st B hk v
  have leafRows : 4*z.rows Y≤V := by
    have dims:=TraceReceiverSeedForestReads.forest_dimensions M t hF st B hk v raw dict masks gateBase
      Y z rfl lane time rfl
    have cells := dims.2.1
    rw [Tree.compiled_rows] at cells
    have le:(T v).rows≤(T v).resources:=by unfold Tree.resources Stage.treeWork;omega
    omega
  have ext : (U v)≤V:=by
    change (U v)+(L).ports.halfBits v≤2*(work v) at ports
    omega
  have selectedIndex : z.index=j.val := index.trans num.symm
  have high {addr count : ℕ} (ha : TickWorkspace.base u 19≤addr) : Protected Y z addr count:=by
    apply protect_above shape z count ha (by omega) scratch leafRows ext
    · rw [selectedIndex]; exact spans.1
    · rw [selectedIndex]; exact spans.2
  refine ⟨operands M t hF st B hk v raw dict masks gateBase Q a rank b rest j D vals warm prev issued owner
    origin pinFit even reached absolute early lane time dir nodeBase unit s43 billed small (savedKernel rank)
    s44 kernelHigh (by omega) (by omega) (by
      have rowBound : rank.val < a.initialSites := rank.isLt
      exact (show a.initialRecords + 5 * rank.val + 4 < a.initialRecords + 5 * a.initialSites by
        omega).trans kernelsFit) ?_ ?_ (by omega) scratch spans.1 spans.2
    ?_ ?_ (offset v) src fit (high gateHi) (high dictHi) (high masksHi)⟩
  · rw [lane]; exact (finFunctionFinEquiv v.2).isLt.trans_le lanesFit
  · rw [time]; exact v.1.isLt.trans_le axisRoom
  · rw [lane];have := (finFunctionFinEquiv v.2).isLt;omega
  · rw [leaf]
    rfl

end
end Hierarchy.TraceReceiverOriginal

end OAI
