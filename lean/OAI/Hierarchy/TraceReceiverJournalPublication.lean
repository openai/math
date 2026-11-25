import OAI.Hierarchy.TraceReceiverJournalMemory
import OAI.Hierarchy.TraceReceiverJournalWires
import OAI.Hierarchy.TraceReceiverFramedRoot
import OAI.Hierarchy.TraceReceiverGridWindow

namespace OAI
/-! # The authentic static root receipt at the elected receiver image -/

namespace Hierarchy.TraceReceiverJournalMemory
open ThreeFlat Diagonal PhysicalStage NavigationPass HistoryContraction NavigationDirectory
open NativeNavigation NodePublication RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.HistoryNodeDirectory
open RAM.HistoryNodeDirectory.Selected RAM.HistoryStageBody.Physical RAM.HistoryInitialSeed
open HistoryStageSetup HistoryPartyBatchExec TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM GridThrough FactorPinIntervals
open TraceReceiverElectedCache GridRegisteredSetting HistorySelectedReceiverLoop TraceReceiverLeafSetup
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
    {z : I.trace} {sel : Fin (l.selectorCap+1)→Bool} {t : Fin ((l.sideMinusOne+1)^(l.dimension+1)*l.copies)} {input origin elected : Memory (64*w)}
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

local notation "ids" => FactorAllocation.factors w costs (List.finRange (I.roots z.1)) t
local notation "selector" => GridReceiverTickDirectory.banks w u
local notation "tables" => TraceReceiverTablesMount.output I elected
local notation "finalSites" => (r).endSites z.1 C O j.path
local notation "oldPages" => (fun pos : ℕ=>(TickWorkspace.base u 20≤pos ∧ pos<TickWorkspace.base u 38) ∨
  (TickWorkspace.base u 43≤pos ∧ pos<TickWorkspace.base u 45))

open RAM.TickTerminalRoot
local notation "x" => (a).terminal (dn).stages (dn).edges W
local notation "X" => ((r).terminalLayer z.1).state
local notation "V" => HistoryStageBody.Physical.volume u
local notation "sector" => GridReceiverBanks.base w
local notation "value" => selectedValue I l j Q
local notation "site" => I.terminalSite z.1

/-- The physical archive's equivalence names this same factor by its S17
ordinal, including when other factors precede it in the S44 chronology. -/
theorem chosenOrdinal (f : Fin (I.roots z.1)) :
    (finalSites).id (site f)=(last).first+f.val ∧ ((finalSites).ord (site f)).val=f.val := by
  have layer:=(r).endSites_layer z.1 C O j.path
  have num:=selected_index I l j f
  rw [(r).archivePlanIndex_physical] at num
  have id : (finalSites).id (site f)=(last).first+f.val :=num
  refine ⟨id,?_⟩
  change (finalSites).layer.first+((finalSites).ord (site f)).val=(last).first+f.val at id
  rw [congrArg (fun row => row.first) layer] at id
  exact Nat.add_left_cancel id

theorem physical_width (f : Fin (I.roots z.1)) :
    (value f).external=(I.terminalWords z.1).ext (site f) ∧
      (value f).pins=(I.terminalWords z.1).ports.form.width (site f) := by
  let root:=(I.ordinal z.1).symm f
  have width : (node ((r).archivePlanIndex z.1 C O j.path root)).arity=
      ((r).endWords z.1 J L).ports.form.width ((r).physicalTerminal z.1 root) := by
    rw [(r).archivePlanIndex_physical,(r).archiveLastNode];rfl
  exact ⟨((r).archivePlanExternal z.1 J L trees C O j.path rfl root).1,width⟩

/-- The native selected degree is the fixed block's terminal degree through
any number of refresh and shrink stages. -/
theorem terminal_degree (h : (r).plan.History) : ((r).terminalLayer h).degree=2^((B).exponent 0) := by
  have e : axes+1=((B).repeat I.passes).charge+(axes+1-((B).repeat I.passes).charge) := by
    rw [(B).charge_repeat]
    have := I.passesFit
    omega
  exact (B).terminalDegree_onLanes _ e h

theorem degree_room (ok : TraceReceiverInstalledScalars.Ready I l j) (bounded : 2^((B).exponent 0)≤u) :
    2*((r).terminalLayer z.1).degree≤V := by
  have pos := ok.age
  have square : u*u≤u^10 := by
    simpa only [pow_two] using (Nat.pow_le_pow_right (by omega : 1≤u) (by decide : 2≤10))
  have twice : 2*u≤u*u := Nat.mul_le_mul_right u (by omega)
  have slack : u+1≤u^10 := by omega
  have power : 2*2^u≤V := by
    change 2*2^u≤2^(u^10)
    rw [Nat.mul_comm,←pow_succ];exact Nat.pow_le_pow_right (by decide) slack
  rw [terminal_degree I]
  exact (Nat.mul_le_mul_left 2 (bounded.trans (Nat.le_of_lt Nat.lt_two_pow_self))).trans power

/-- The lower archive stops strictly before the high temporary mount,
including when the class-major S17 roster is empty. -/
theorem margins (ok : TraceReceiverInstalledScalars.Ready I l j) :
    TickWorkspace.base u 45≤ sector-16 ∧ (stop).heap≤ sector-16 := by
  have bounds:=TraceReceiverLeafSetup.archive_bounds I l (by have:=ok.big;omega) ok.held
  have ⟨_,upper⟩:=TraceAdmission.receiverAge_chart w ok.big
  have sep:=TraceReceiverOwnerMount.sector geom.pos upper
  have wide:=(owner_room I l j ok).fixed
  have heap : (stop).heap≤TickWorkspace.base u 38:=bounds.2.1
  change (46*TickWorkspace.stride u≤30*GridDescription.sector w-16) ∧ _≤30*GridDescription.sector w-16
  change (stop).heap≤39*TickWorkspace.stride u at heap
  constructor <;> omega

theorem first_word (ok : TraceReceiverInstalledScalars.Ready I l j) (afterDesc restored : Memory W)
    (done : published I l j Q afterDesc)
    (second : GridReceiverTickDirectory.Ticked selector ids (t.val:Word W) afterDesc restored) :
    restored (GridReceiverBanks.tasks w).first=((finalSites).layer.first:Word W) := by
  rw [(r).endSites_layer];exact (descriptor I l j Q ok afterDesc restored done second).1

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3200000 in
/-- All the memory observations in this root use the single actual second
election image. Its raw widths come from the identical j.mid that produced
the stored prefix, and its native S13 node uses the selected Ledger. -/
theorem publication (ok : TraceReceiverInstalledScalars.Ready I l j) (afterDesc restored : Memory W)
    (done : published I l j Q afterDesc)
    (second : GridReceiverTickDirectory.Ticked selector ids (t.val:Word W) afterDesc restored)
    (R : GridPinArena.Scalars W P S full radix g) (bitsFit : S≤g)
    (tableFrame : TraceReceiverEntryTables.TableFrame w u (libraryWords B W) elected tables)
    (ownersRead : GridPinPublisher.PrefixOwners P tables)
    (terminals : (a).TerminalRoom (dn).stages (dn).edges W)
    (selectorRoom : GridSelector.Room (r).plan (GridNativeDispatch.actualTable I safe).codes
      (GridPhysicalSelector.bits r) l.selectorCap)
    (paid : ∀ f,I.issuedTreeWork z.1 l.degree l.stageRate l.rootRate f≤I.work z.1 C fees f)
    (degree : 2*((r).terminalLayer z.1).degree≤V)
    {suffix : ℕ} (suffixIn : suffix≤l.pinWidth) (i : Fin (ids).length) :
    TraceReceiverRootRetain.Publication u sector l.pinWidth suffix (O).layer.count
      (TickWorkspace.base u 20) (stop).heap restored j.mid X (I.terminalWords z.1) finalSites (site (ids[i.val]))
      (value (ids[i.val])) HistoryRefreshEmitter.tag b x i (fun k=>(value (ids[k.val])).net.cells) := by
  let f:=ids[i.val]
  have mem : f∈ids:=List.getElem_mem i.isLt
  have layer:=(r).endSites_layer z.1 C O j.path
  have coord:=chosenOrdinal I l j f
  have ⟨low,upper⟩:=TraceAdmission.receiverAge_chart w ok.big
  have big:=ok.big
  have wide:=(owner_room I l j ok).fixed
  have ⟨sectorLo,sectorWord,sectorGap⟩:=TraceFactorReceiver.Gather.grid_window (by omega : 7≤w) upper
  have bounds:=TraceReceiverLeafSetup.archive_bounds I l (by omega) ok.held
  have heap : (stop).heap≤TickWorkspace.base u 38:=bounds.2.1
  have large : 162≤V:=by
    change 162≤2^(u^10)
    exact (show 162≤2^8 by decide).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have totalRoom : total≤V:=ok.bound.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have smallWord : total<2^W:=ok.bound.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  have idsLength : (ids).length≤I.roots z.1:=by simpa using (FactorAllocation.factors_nodup geom.teams_pos w costs t).length_le_card
  have rootCount:=j.card
  have each (g₀ : Fin (I.roots z.1)) := selected_budget I l j Q g₀ l.degree l.stageRate l.rootRate
    (paid g₀) (ok.paid g₀)
  have four : 4*2^(3*w/5)≤V:=by
    change 4*2^(3*w/5)≤2^(u^10)
    rw [show 4*2^(3*w/5)=2^(2+3*w/5) from (pow_add 2 2 (3*w/5)).symm]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have rows (a₀ : Fin (I.roots z.1)) : 4*(value a₀).net.cells≤V:=
    (Nat.mul_le_mul_left 4 (show (value a₀).net.cells≤2^(3*w/5) by have:=each a₀;omega)).trans four
  have pinPay:=each f
  have pinCap : (value f).pins≤V:=by omega
  have width:=physical_width I l j Q f
  have extCap : (value f).external≤V:=by
    rw [width.1]
    exact (Nat.le_add_right _ ((I.terminalWords z.1).ports.halfBits (site f))).trans (width.2.symm.le.trans pinCap)
  have prior := archived I l j Q ok afterDesc restored done second R bitsFit tableFrame ownersRead
  have wires:=TraceReceiverElectedJournal.Journal.wires I l geom safe z sel t input origin elected j ok.big terminals selectorRoom
  have doc:=descriptor I l j Q ok afterDesc restored done second
  have bankNodes : (b).nodes=TickWorkspace.base u 44:=rfl
  have bankCharges : (b).charges=TickWorkspace.base u 43:=rfl
  have s43:=TickWorkspace.apart («u»:=u) (by decide : 43<44)
  have frozen:=j.cache.warm_at (archive_chronological r z.1 C O j.path (a).seedData)
    (by rw [bankCharges]) (by rw [bankNodes];omega)
    (fun a₀ lo hi=>(prior a₀ (Or.inr ⟨lo,hi⟩)).trans (j.savedAt a₀ lo hi))
  obtain ⟨q,inside,finalLayer⟩:=final_mem r z.1 C O j.path (a).seedData
  have atLayer : q.layer=(finalSites).layer:=finalLayer.trans layer.symm
  have directory : ∀ k : Fin (finalSites).layer.count,DirectoryRow b (finalSites).layer k restored := by
    rw [←atLayer];exact frozen.directory q inside
  have posted:=TraceReceiverTerminalHalves.posted_registered I l j ok
  have fit : f.val<2^W:=by have:=f.isLt;omega
  have externalRead:=selected_record I l j Q afterDesc restored done f mem smallWord large totalRoom (rows f) extCap
    (fun pos lo=>restore I l j ok afterDesc restored second pos (Or.inl lo))
  have firstFit : (last).first<2^W:=by omega
  have nodeFit : TickWorkspace.base u 44<2^W:=by
    have:=TickWorkspace.apart («u»:=u) (by decide : 44<45);omega
  refine {
    «sector» := sectorLo.le
    sectorFit := by omega
    large := large
    nodesFit := by rw [layer]; exact totalRoom
    count := by omega
    records := fun k => rows _
    degree := degree
    pinLimit := pinCap
    word := by
      have lowPin := ok.inputRoom
      change 2+l.pinWidth ≤ TickWorkspace.base u 38 at lowPin
      have := TickWorkspace.apart («u» := u) (by decide : 38<45)
      omega
    suffixIn := suffixIn
    heapStart := TickWorkspace.apart (by decide : 18<20)
    heapEnd := by have := margins I l j ok; omega
    wireStart := wires.start
    wireEnd := by have bound := wires.stop; change _ ≤ sector-16 at bound; omega
    wireFit := wires.bounds
    edgeCount := wires.edges
    widths := wires.widths
    wireCapacity := wires.capacity
    emitted := ?_
    picked := ?_
    first := ?_
    nodePointer := ?_
    nodeBank := bankNodes
    chargeBank := bankCharges
    directory := directory _
    posted := ?_
    cache := ?_
    external := width.1
    localPins := width.2
    stream := ?_
    endpoints := ?_
    rowCount := rfl }
  · intro e
    have hi:=e.isLt
    have lo:=wires.archiveStart
    have large:=wires.beforeLibrary
    exact (prior _ (Or.inl (by constructor <;> omega))).trans (wires.emitted ⟨e.val,by omega⟩)
  · change (restored ((selector).roots+i.val)).val=_
    rw [second.roots i,Fin.val_cast_of_lt fit];exact coord.2.symm
  · change (restored (TickPhysicalABI.directory u 3)).val=_
    rw [doc.1,Fin.val_cast_of_lt firstFit,layer]
  · change (restored (TickPhysicalABI.directory u 3+1)).val=_
    rw [doc.2,Fin.val_cast_of_lt nodeFit,bankNodes]
  · exact posted.transfer (fun pos hp=>congrArg Fin.val (prior pos (Or.inl ⟨hp.1,hp.2.trans_le heap⟩)))
      (fun _ hp=>hp)
  · rw [coord.1];exact externalRead
  · change streamAt u (O).layer.count ((r).archivePlanIndex z.1 C O j.path _).val=_
    rw [selected_index,coord.1]
  · change endsAt u (O).layer.count ((r).archivePlanIndex z.1 C O j.path _).val=_
    rw [selected_index,coord.1]

end
end Hierarchy.TraceReceiverJournalMemory

end OAI
