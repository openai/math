import OAI.Hierarchy.TraceReceiverDescendantVisits
import OAI.Hierarchy.TraceReceiverDescendantCache
import OAI.Hierarchy.GridReceiverIntervalInputs

namespace OAI
/-! # Returning the native cache and its own chronological journal from a chosen tick -/

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
private theorem assigned_cast {w d T a b : ℕ} {ht : 0<T} (h : a=b)
    (p : Fin a→Fin d→ℕ) {m n : Memory (64*w)} (a₀ : GridSimulation.Assigned ht p m n) :
    GridSimulation.Assigned ht (fun i : Fin b=>p (i.cast h.symm)) m n := by subst b;exact a₀

private theorem ticked_cast {W w d T a b : ℕ} (h : a=b) (p : Fin a→Fin d→ℕ)
    (A : GridReceiverTickDirectory.Banks) (t : Fin T) {m n : Memory W}
    (a₀ : GridReceiverTickDirectory.Ticked A (FactorAllocation.factors w p (List.finRange a) t)
      (t.val:Word W) m n) :
    GridReceiverTickDirectory.Ticked A (FactorAllocation.factors w (fun i : Fin b=>p (i.cast h.symm))
      (List.finRange b) t) (t.val:Word W) m n := by subst b;exact a₀

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

def work :=
  let roots:=FactorAllocation.factors w price (List.finRange (last).count) t
  (roots.map fun i=> scalarFee*(r).chargeAt z.1 C basePay ((TraceAdmission.Resources.indexEquiv r z.1 j.card).symm i)).sum

def published (final : Memory W) : Prop :=
  Ledger u D HistoryRefreshEmitter.tag val (TickTerminalRoot.slotKeep u) entry total final

set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
/-- The actual six-stage source, starting with the elected output and ending with a compiled
cache whose path, archive, elected root ordinals, hidden wires and external inputs are fixed by j. -/
theorem publish (aligned : W=16*u^10) (big : 64^10≤w) (depthFit : d≤2*w+1)
    (bound : total≤2^(3*w/5)) (held : (stop).heap≤(a).control+64) (metadata : (a).metadataEnd≤(a).cursor.heap)
    (rev : State.HalfRows O (fun i=>(a).initialRecords ≤ i ∧ i<(a).metadataEnd) (numeric origin))
    (seed : ∀ i : Fin (a).initialSites,∀ c : Fin 5,origin ((a).initialRecords+5*i.val+c.val)=
      ((![(a).seed,i.val,0,i.val%(a).remainingLanes,i.val/(a).remainingLanes] : Fin 5→ℕ) c : Word W))
    (R : GridPinArena.Scalars W P S full radix g) (small : GridPinArena.Small w P S full ((dn).stages.length*full) radix)
    (source : ∀ i,Q.origin i=I.origin z.1 i)
    (dispatch : ∀ f,GridTicks.index (Q.owner f)=FactorAllocation.owner geom.teams_pos w costs f)
    (order : ∀ s,Q.rows s=FactorAllocation.factors w costs (List.finRange _) (GridTicks.index s))
    (lens : ∀ s,(Q.header s).length=(P).headerSize)
    (textFit : SelfAdvice.textSize W pc slots≤w^2) (self : Fin (w^2)→Bool) (inBit : ℕ→Bool)
    (header : (GridReceiverHeader.header _ textFit self (t.val:Word W) args sel).length≤l.pinWidth)
    (read : ∀ i : Fin (GridReceiverHeader.header _ textFit self (t.val:Word W) args sel).length,
      inBit i.val=(GridReceiverHeader.header _ textFit self (t.val:Word W) args sel)[i.val])
    (inputFrame : ∀ x,x<2+l.pinWidth→elected x=TickMountedPins.memory (w:=W) (fun i : Fin l.pinWidth=>inBit i.val) x)
    (smallTemplate : templateSize I≤2^(w/100)) (inputRoom : 2+l.pinWidth≤ start w)
    (librarySize : libraryWords B W≤ TickWorkspace.stride u) (high : start w+libraryWords B W≤gateBase I)
    (room : start w+libraryWords B W<2^W)
    (rawFit : HistorySelectedSeedDecode.Fits (q:=axes) (low:=w/2) (S:=S) (f:=fuel) («b»:=4*w+2) («W»:=W)
      hF (ft).width (ft).labels addr st (ft).header (ft).time regs slots (B).cursorCopies 0 (dict I) (masks I) (gateBase I))
    (even : Even S) (age : 40≤u) (fixed : (B).archiveConstant (B).localCoefficient≤u)
    (shrink : ∀ i : Fin ((B).shrink.more.length+1),((B).shrink.block ((B).shrink.row i)).bitCap≤volume u)
    (refresh : ∀ i : Fin ((B).refresh.last+1),((B).refresh.block i).bitCap≤volume u)
    (unit : 0<fees) (paid : ∀ i,I.work z.1 C fees i≤2^(3*w/5))
    (allowance : (B).archiveUnit u (B).localCoefficient l.degree≤fees)
    (margin : 10*(phase+2)^2*K≤fees) (alphabet : (a).K<2^W) :
    (TraceReceiverDescendantExecution.program I l (dn).parameters.firstFinal (dn).parameters.roots P).Spec
      (·=elected) (fun _ final=>published I l j Q final)
      (TraceReceiverDescendantExecution.cost I (dn).parameters.firstFinal (dn).parameters.roots P
        (17+24*total+work I l j)) := by
  have large : 7≤w := (by decide : 7≤64^10).trans big
  obtain ⟨lower,upper⟩:=TraceAdmission.receiverAge_chart w big
  have ⟨wide,past,live⟩:=TraceReceiverOwnerMount.directory_fits geom.pos (by omega : 3*w≤u^10) bound
  have ⟨_,_,image,library,fr⟩:=TraceReceiverTablesMount.run I l textFit self (t.val:Word W) sel inBit elected
    (2+l.pinWidth) header (by omega) read inputFrame large depthFit smallTemplate inputRoom high room
  have src:=GridReceiverIntervalInputs.from_prefix I l geom big z sel safe j.histories t j.assigned j.ticked Q source
  have scale:=(GridPinArena.scales w geom.pos).1
  have capacity:=small.full
  have staged:=small.staged
  have current:=GridReceiverIntervalInputs.keep_window I l geom z Q src (fun i lo hi=>by
    apply TraceReceiverEntryTables.window fr geom.pos upper librarySize i lo (by omega))
  have «prefix»:=current.prefix (show I.roots z.1=(P).factor.items from j.count) rfl R.ticksFit R.itemsFit R.within
  have offset:=TraceReceiverElectedIntervals.offsets I l geom safe z sel t input origin elected j.elected Q big
    source dispatch order lens R small librarySize fr
  have visit:=TraceReceiverDescendantVisits.visits I l j Q aligned big depthFit bound held metadata rev seed
    R small «prefix» source offset librarySize image library fr rawFit R.pinsFit.le even age fixed
    shrink refresh unit paid allowance margin alphabet
  have auth:=TraceReceiverEntryTables.after_interval_reads R (by omega) lower upper small.bits librarySize
    past live fr «prefix»
  have costScale : 2≤K := by
    exact (TraceDistribution.Physical.fresh_price_scale B u).trans_eq
      (congrArg (fun n : ℕ => (B).localCoefficient * (n+1)^3) aligned.symm)
  have volumeRoom : 162≤volume u := by
    change 162≤2^(u^10)
    have e : 8≤u^10 := (show 8≤u by omega).trans (Nat.le_self_pow (by decide) _)
    exact (by decide : 162≤2^8).trans (Nat.pow_le_pow_right (by decide) e)
  have compiler : (TraceReceiverDescendantExecution.program I l (last).first (last).count P).Spec
      (·=elected) (fun _ final => published I l j Q final)
      (TraceReceiverDescendantExecution.cost I (last).first (last).count P
        (17+24*total+work I l j)) := TraceReceiverDescendantExecution.publish I l r z.1 J C L trees ptr O j.path rfl geom.teams_pos b
    j.saved j.reg j.classified elected j.stored price t phase K (priceUnit:=scalarFee) P textFit self (t.val:Word W)
    sel inBit (2+l.pinWidth) header (by omega) read inputFrame large depthFit smallTemplate inputRoom high room
    R.ticksFit R.factorsFit R.lanesFit rfl j.savedAt (assigned_cast j.card costs j.assigned)
    (ticked_cast j.card costs _ t j.ticked) (by omega) upper wide past bound live auth
    HistoryRefreshEmitter.tag basePay pairs j.card j.numbered j.charged unit le_rfl visit.1 (by omega) volumeRoom
    costScale margin R.ticksFit.le visit.2
  rw [←j.first,←j.roots]
  exact @compiler

end
end Hierarchy.TraceReceiverElectedCache

end OAI
