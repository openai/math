import OAI.Hierarchy.TraceReceiverElectedReplay
import OAI.Hierarchy.TraceReceiverSelectedRows
import OAI.Hierarchy.TraceReceiverCachedDimensions
import OAI.Hierarchy.TraceReceiverRootRetain

namespace OAI
/-! # Actual selected S13 and S12 cache in the terminal receiver -/
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
private theorem occurrence_cast {w costDimensions tickCount sourceCount targetCount : ℕ}
    (bound : sourceCount = targetCount) (m : Fin sourceCount → Fin costDimensions → ℕ)
    (f : Fin sourceCount) (t : Fin tickCount)
    (present : f ∈ FactorAllocation.factors w m (List.finRange sourceCount) t) :
    f.cast bound ∈ FactorAllocation.factors w (fun i : Fin targetCount => m (i.cast bound.symm))
      (List.finRange targetCount) t := by
  subst targetCount
  exact present

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

/-- Both independent native executions assign this factor the same physical
terminal ordinal. The one chronological S44 index addressed by S17 is therefore
the one whose compiled network evaluates this factor. -/
theorem selected_index (f : Fin (I.roots z.1)) :
    ((r).archivePlanIndex z.1 C O j.path ((I.ordinal z.1).symm f)).val=(last).first+f.val := by
  change (last).first+(((r).finalArchive z.1 C O j.path).2 (((r).finalSite z.1).symm ((I.ordinal z.1).symm f))).val=_
  rw [j.numbered,←(r).terminalOrderEquiv_val]
  exact congrArg ((last).first+·) (congrArg Fin.val ((I.ordinal z.1).apply_symm_apply f))

def selectedValue (f : Fin (I.roots z.1)) : NodeValue F :=
  val ((r).archivePlanIndex z.1 C O j.path ((I.ordinal z.1).symm f))

theorem selected_record (afterDesc restored : Memory W) (done : published I l j Q afterDesc)
    (f : Fin (I.roots z.1)) (chosen : f∈FactorAllocation.factors w costs (List.finRange (I.roots z.1)) t)
    (word : total<2^W) (large : 162≤HistoryStageBody.Physical.volume u) (size : total≤HistoryStageBody.Physical.volume u)
    (rows : 4*(selectedValue I l j Q f).net.cells≤HistoryStageBody.Physical.volume u)
    (ports : (selectedValue I l j Q f).external≤HistoryStageBody.Physical.volume u)
    (frame : ∀ address<TickWorkspace.base u 17,restored address=afterDesc address) :
    (selectedValue I l j Q f).Cached HistoryRefreshEmitter.tag u ((last).first+f.val) restored := by
  let i:=(r).archivePlanIndex z.1 C O j.path ((I.ordinal z.1).symm f)
  let v:=selectedValue I l j Q f
  let idx:=(last).first+f.val
  have si : i.val=idx:=selected_index I l j f
  have ord : i=(⟨(last).first+(f.cast j.card).val,Nat.add_lt_add_left (f.cast j.card).isLt (last).first⟩:Fin total):=
    Fin.ext si
  have present:=occurrence_cast j.card costs f t chosen
  have selected : v.Cached HistoryRefreshEmitter.tag u idx afterDesc := by
    have got := TraceFactorReceiver.Gather.selected_published chron rfl geom.teams_pos price t val
      HistoryRefreshEmitter.tag (TickTerminalRoot.slotKeep u) entry afterDesc word geom.ticks.le done (f.cast j.card) present
    change (val i).Cached _ _ _ _
    rw [ord]
    exact got
  apply NodeValue.Cached.retain v HistoryRefreshEmitter.tag selected
  intro address used
  apply frame
  have idxRoom : idx<HistoryStageBody.Physical.volume u:=si ▸ (i.isLt.trans_le size)
  have before:=TickWorkspace.apart («u»:=u) (by decide : 12<13)
  have later:=TickWorkspace.apart («u»:=u) (by decide : 13<17)
  have span:=address_limits (seedCount:=(O).layer.count) (i:=idx) large rows ports
  let V:=HistoryStageBody.Physical.volume u
  obtain ⟨header,cube⟩:=TraceReceiverRootRetain.slot_room large
  have step:=Nat.mul_le_mul_right (V^2) (show idx+1≤V by omega)
  have lim : (idx+1)*V^2≤TickWorkspace.stride u:=by
    change (idx+1)*V^2≤V^4
    change V^3≤V^4 at cube
    nlinarith only [step,cube]
  have atS : v.stream=streamAt u (O).layer.count idx:=by change streamAt _ _ i.val=_;rw [si]
  have atE : v.ext=endsAt u (O).layer.count idx:=by change endsAt _ _ i.val=_;rw [si]
  have stream_end : v.stream + 4*v.net.cells ≤ v.ext := by
    rw [atS, atE]
    exact span.2.1
  have extent_end : v.ext + v.external ≤ TickWorkspace.base u 17 := by
    rw [atE]
    exact span.2.2.trans ((Nat.add_le_add_left lim _).trans
      (before.trans ((Nat.le_add_right _ _).trans later)))
  change ((TickWorkspace.base u 13+8*idx≤address ∧ address<TickWorkspace.base u 13+8*idx+6) ∨
    (v.stream≤address ∧ address<v.stream+4*v.net.cells) ∨ (v.ext≤address ∧ address<v.ext+v.external)) at used
  rcases used with h|h|h
  · omega
  · exact h.2.trans_le (stream_end.trans ((Nat.le_add_right _ _).trans extent_end))
  · exact h.2.trans_le extent_end

theorem selected_network (f : Fin (I.roots z.1)) :
    let root:=(I.ordinal z.1).symm f
    let assembled:=(r).plan.assemble z.1 ((r).wordAssembly J L) trees
    (selectedValue I l j Q f).pins=assembled.1.width root ∧
      HEq (selectedValue I l j Q f).net ((assembled.2 root).compile) :=
  (r).archivePlanNetwork z.1 J L trees C O j.path rfl ((I.ordinal z.1).symm f)

/-- Read the dimension budget from the exact physical tree used by this
elected archive, at the tick compiler's registered factor ordinal. -/
theorem selected_budget (f : Fin (I.roots z.1)) (degree stageRate rootRate : ℕ)
    (paid : I.issuedTreeWork z.1 degree stageRate rootRate f≤
      I.work z.1 I.issuedCharges (I.issuedUnit w degree stageRate rootRate) f)
    (small : I.work z.1 I.issuedCharges (I.issuedUnit w degree stageRate rootRate) f≤2^(3*w/5)) :
    let v:=selectedValue I l j Q f
    v.net.cells+v.net.internal+v.pins≤2^(3*w/5) := by
  obtain ⟨arity,net⟩:=selected_network I l j Q f
  exact (I.cached_dimensions_pay z.1 f w degree stageRate rootRate
    (selectedValue I l j Q f) arity net paid).trans small

end
end Hierarchy.TraceReceiverElectedCache

end OAI
