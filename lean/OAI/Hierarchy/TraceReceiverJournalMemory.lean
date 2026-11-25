import OAI.Hierarchy.TraceReceiverElectedRoot
import OAI.Hierarchy.TraceReceiverTerminalHalves
import OAI.Hierarchy.GridReceiverDirectoryRestore
import OAI.Hierarchy.TraceReceiverWarmSources

namespace OAI
/-! # The physical archive and descriptor through both receiver elections -/

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
    {z : I.trace} {sel : Fin (l.selectorCap+1)→Bool} {t : Fin ((l.sideMinusOne+1)^(l.dimension+1)*l.copies)}
    {input origin elected : Memory (64*w)}
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
local notation "args" => GridStructuralHeader.parameters B (axes+1) I.passes l.selectorCap M ft hF st 0 (gateBase I)
local notation "finalSites" => (r).endSites z.1 C O j.path
local notation "oldPages" => (fun pos : ℕ=>(TickWorkspace.base u 20≤pos ∧ pos<TickWorkspace.base u 38) ∨
  (TickWorkspace.base u 43≤pos ∧ pos<TickWorkspace.base u 45))


/-- The loaded S38/gate tables really preserve the requested window and the
prefix-owner inputs. Both observations are produced by the existing table
loader on this very elected memory. -/
theorem mounted_tables (ok : TraceReceiverInstalledScalars.Ready I l j)
    (R : GridPinArena.Scalars W P S full radix g)
    (small : GridPinArena.Small w P S full ((dn).stages.length*full) radix)
    (source : ∀ k,Q.origin k=I.origin z.1 k)
    (textFit : SelfAdvice.textSize W pc slots≤w^2) (self : Fin (w^2)→Bool) (inBit : ℕ→Bool)
    (header : (GridReceiverHeader.header _ textFit self (t.val:Word W) args sel).length≤l.pinWidth)
    (read : ∀ k : Fin (GridReceiverHeader.header _ textFit self (t.val:Word W) args sel).length,
      inBit k.val=(GridReceiverHeader.header _ textFit self (t.val:Word W) args sel)[k.val])
    (frame : ∀ addr,addr<2+l.pinWidth → elected addr=TickMountedPins.memory (w:=W) (fun k : Fin l.pinWidth=>inBit k.val) addr) :
    TraceReceiverEntryTables.TableFrame w u (libraryWords B W) elected tables ∧
      GridPinPublisher.PrefixOwners P tables := by
  have big:=ok.big
  obtain ⟨_,_,_,_,fr⟩:=TraceReceiverTablesMount.run I l textFit self (t.val:Word W) sel inBit elected
    (2+l.pinWidth) header (by omega) read frame (by omega) ok.depthFit ok.smallTemplate ok.inputRoom ok.high ok.room
  have src:=GridReceiverIntervalInputs.from_prefix I l geom ok.big z sel safe j.histories t j.assigned j.ticked Q source
  obtain ⟨_,upper⟩:=TraceAdmission.receiverAge_chart w ok.big
  have scale:=(GridPinArena.scales w geom.pos).1
  have capacity:=small.full
  have staged:=small.staged
  have current:=GridReceiverIntervalInputs.keep_window I l geom z Q src (fun k lo hi=>by
    apply TraceReceiverEntryTables.window fr geom.pos upper ok.librarySize k lo (by omega))
  exact ⟨fr,current.prefix (show I.roots z.1=(P).factor.items from j.count) rfl R.ticksFit R.itemsFit R.within⟩

omit [Fintype F] in
/-- The final typed layer is represented by an actual row of the same ordered
archive list passed to the S43/S44 publisher. -/
theorem final_mem {k lanes : ℕ} {X : State k lanes} (R : Run F X) (history : R.plan.History)
    (charge : R.Charges) (sites : X.ArchiveSites) (path : R.ArchivePath history charge sites)
    (data : LayerData sites.layer) :
    ∃ row∈R.archiveList history charge sites path data,row.layer=(R.finalArchive history charge sites path).1 := by
  induction R with
  | done X => exact ⟨_,List.mem_cons_self ..,rfl⟩
  | step step next ih =>
    obtain ⟨row,mem,eqn⟩:=ih history.1 (Run.tailHistory step next history) (charge.2 history.1)
      path.1.sites path.2 path.1.data
    exact ⟨row,List.mem_cons_of_mem _ mem,eqn⟩

theorem owner_room (ok : TraceReceiverInstalledScalars.Ready I l j) :
    TraceReceiverOwnerMount.Room W u (last).first (last).count (selector).owners ((selector).scratch+1) := by
  have ⟨lower,upper⟩:=TraceAdmission.receiverAge_chart w ok.big
  exact TraceReceiverOwnerMount.native_room geom.pos (by omega : 3*w≤u^10) upper ok.bound

/-- The second S17 election leaves ordinary low words and the archived
interval above S19 through S45 intact. -/
theorem restore (ok : TraceReceiverInstalledScalars.Ready I l j) (afterDesc restored : Memory W)
    (renamed : GridReceiverTickDirectory.Ticked selector ids (t.val:Word W) afterDesc restored)
    (a₀ : ℕ) (band : a₀<TickWorkspace.base u 17 ∨ (TickWorkspace.base u 19≤a₀ ∧ a₀<TickWorkspace.base u 45)) :
    restored a₀=afterDesc a₀ := by
  have ⟨_,upper⟩:=TraceAdmission.receiverAge_chart w ok.big
  have wide:=(owner_room I l j ok).fixed
  have scale:=TraceReceiverOwnerMount.sector geom.pos upper
  have room : GridReceiverTickDirectory.Room selector W (2+SelfAdvice.textSize W pc slots)
      (I.roots z.1) (radix*I.roots z.1) := by rw [j.count];exact geom.room
  apply GridReceiverDirectoryRestore.rebuild_frame geom.pos upper (by omega) geom.teams_pos costs t _ room renamed
  rcases band with low|⟨lo,hi⟩
  · exact Or.inl low
  · exact Or.inr (Or.inl ⟨lo,by change a₀<46*TickWorkspace.stride u at hi;omega⟩)

/-- The S11 final offset and S44 pointer installed by the six-phase owner
program are retained by the selected Ledger and the second election. -/
theorem descriptor (ok : TraceReceiverInstalledScalars.Ready I l j) (afterDesc restored : Memory W)
    (done : published I l j Q afterDesc)
    (renamed : GridReceiverTickDirectory.Ticked selector ids (t.val:Word W) afterDesc restored) :
    restored (TickPhysicalABI.directory u 3)=((last).first:Word W) ∧
      restored (TickPhysicalABI.directory u 3+1)=(TickWorkspace.base u 44:Word W) := by
  have wide:=(owner_room I l j ok).fixed
  have below:=TickWorkspace.apart («u»:=u) (by decide : 11<12)
  have low:=TickWorkspace.apart («u»:=u) (by decide : 12<17)
  have same (k : Fin 2) : restored (TickPhysicalABI.directory u 3+k.val)=entry (TickPhysicalABI.directory u 3+k.val) := by
    have col:=k.isLt
    have fit : TickPhysicalABI.directory u 3+k.val<TickWorkspace.base u 12 := by
      change TickWorkspace.base u 11+3*(TickWorkspace.stride u/4)+k.val<TickWorkspace.base u 12
      omega
    exact (restore I l j ok afterDesc restored renamed _ (Or.inl (by omega))).trans
      (done.durable _ (Or.inl fit))
  have head:=TraceReceiverOwnerMount.output_descriptor (owner_room I l j ok) (TraceReceiverDescendantExecution.sliced I P elected)
  exact ⟨(same 0).trans head.1,(same 1).trans head.2⟩

/-- Across both class-major elections and the owner/descendant execution, all
used half records and every S43/S44 archival word retain their registration values. -/
theorem archived (ok : TraceReceiverInstalledScalars.Ready I l j) (afterDesc restored : Memory W)
    (done : published I l j Q afterDesc)
    (renamed : GridReceiverTickDirectory.Ticked selector ids (t.val:Word W) afterDesc restored)
    (R : GridPinArena.Scalars W P S full radix g) (bitsFit : S≤g)
    (tableFrame : TraceReceiverEntryTables.TableFrame w u (libraryWords B W) elected tables)
    (ownersRead : GridPinPublisher.PrefixOwners P tables) (a₀ : ℕ) (band : oldPages a₀) :
    restored a₀=j.reg a₀ := by
  have ⟨lower,upper⟩:=TraceAdmission.receiverAge_chart w ok.big
  have area:=owner_room I l j ok
  have wide:=area.fixed
  have bounds:=area.nodes
  have idx := j.card
  have length : (ids).length≤I.roots z.1 := by
    simpa using (FactorAllocation.factors_nodup geom.teams_pos w costs t).length_le_card
  have s17:=TickWorkspace.apart («u»:=u) (by decide : 17<20)
  have s18:=TickWorkspace.apart («u»:=u) (by decide : 18<20)
  have s19:=TickWorkspace.apart («u»:=u) (by decide : 19<20)
  have s20:=TickWorkspace.apart («u»:=u) (by decide : 20<43)
  have s38:=TickWorkspace.apart («u»:=u) (by decide : 38<45)
  have chart:=TraceReceiverOwnerMount.sector geom.pos upper
  change (TickWorkspace.base u 20≤a₀ ∧ a₀<TickWorkspace.base u 38) ∨
    (TickWorkspace.base u 43≤a₀ ∧ a₀<TickWorkspace.base u 45) at band
  have live : TickWorkspace.base u 19≤a₀ ∧ a₀<TickWorkspace.base u 45 := by omega
  have entryAt : entry a₀=elected a₀ := TraceReceiverEntryTables.original R area (by have:=ok.big;omega)
    lower upper bitsFit ok.librarySize tableFrame ownersRead a₀ (Or.inr band)
  have old := GridReceiverTickDirectory.outside_receiver geom.teams_pos costs t j.assigned j.ticked a₀
    (by have high:=live.2;change a₀<46*TickWorkspace.stride u at high;omega) (Or.inr (by omega)) (Or.inr (by omega))
  exact (restore I l j ok afterDesc restored renamed a₀ (Or.inr live)).trans
    ((done.durable a₀ (Or.inr live.1)).trans (entryAt.trans old))


end
end Hierarchy.TraceReceiverJournalMemory

end OAI
