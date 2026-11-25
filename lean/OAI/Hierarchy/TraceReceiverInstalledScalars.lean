import OAI.Hierarchy.TraceReceiverDescendantVisits
import OAI.Hierarchy.TraceReceiverOriginalSeed
import OAI.Hierarchy.TraceReceiverSeedFits
import OAI.Hierarchy.TraceReceiverCopyAdmission
import OAI.Hierarchy.GridChosenReceiverInstalledPrefix
import OAI.Hierarchy.GridChosenReceiverTariff

namespace OAI
/-! # Scalar admission on a calibrated installed grid and its own journal -/

namespace Hierarchy.TraceReceiverInstalledScalars
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
local notation "last" => ((r).finalArchive z.1 C O j.path).1
local notation "total" => (last).first+(last).count

/-- Scalar room and the genuine initial rows for the selected branch, at its actual receiver word width. -/
structure Ready : Prop where
  aligned : W=16*u^10
  big : 64^10≤w
  depthFit : d≤2*w+1
  bound : total≤2^(3*w/5)
  held : (stop).heap≤(a).control+64
  metadata : (a).metadataEnd≤(a).cursor.heap
  rev : State.HalfRows O (fun i=>(a).initialRecords≤ i ∧ i<(a).metadataEnd) (numeric origin)
  seed : ∀ i : Fin (a).initialSites,∀ c : Fin 5,origin ((a).initialRecords+5*i.val+c.val)=
    ((![ (a).seed,i.val,0,i.val%(a).remainingLanes,i.val/(a).remainingLanes] : Fin 5→ℕ) c : Word W)
  smallTemplate : templateSize I≤2^(w/100)
  inputRoom : 2+l.pinWidth≤ start w
  librarySize : libraryWords B W≤ TickWorkspace.stride u
  high : start w+libraryWords B W≤gateBase I
  room : start w+libraryWords B W<2^W
  rawFit : HistorySelectedSeedDecode.Fits (q:=axes) (low:=w/2) (S:=S) (f:=fuel) («b»:=4*w+2) («W»:=W)
    hF (ft).width (ft).labels addr st (ft).header (ft).time regs slots (B).cursorCopies 0 (dict I) (masks I) (gateBase I)
  even : Even S
  age : 40≤u
  fixed : (B).archiveConstant (B).localCoefficient≤u
  shrink : ∀ i : Fin ((B).shrink.more.length+1),((B).shrink.block ((B).shrink.row i)).bitCap≤volume u
  refresh : ∀ i : Fin ((B).refresh.last+1),((B).refresh.block i).bitCap≤volume u
  unit : 0<fees
  paid : ∀ i,I.work z.1 C fees i≤2^(3*w/5)
  allowance : (B).archiveUnit u (B).localCoefficient l.degree≤fees
  margin : 10*(phase+2)^2*K≤fees
  alphabet : (a).K<2^W

end
end Hierarchy.TraceReceiverInstalledScalars

namespace Hierarchy.TraceReceiverInstalledScalars
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.PhysicalProcedure RAM.HistoryStageBody.Physical TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM
open GridScale GridInstalledEvaluator GridThrough GridRegisteredSetting GridReceiverDirectory
open TraceAdmission TraceDistribution TraceReceiverLeafSetup Filter
open scoped Classical Fin.CommRing Topology
noncomputable section
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [Fintype F] {Q : ℕ→ℕ} {loss : ℕ→ℝ}

private theorem scale_room {ages runs : ℕ→ℕ} (scale : Scale ages runs) (n : ℕ) :
    ∀ᶠ w : ℕ in atTop,ages w≤2*w ∧ (n+1)*runs w≤w := by
  have top:=(tendsto_order.mp scale.cap).2 (2:ℝ) (by norm_num)
  have part:=(tendsto_order.mp scale.blocks).2 (1/((n:ℝ)+1)) (by positivity)
  filter_upwards [top,part,eventually_ge_atTop 1] with w t p large
  have pos : 0<(w:ℝ) := by exact_mod_cast (by omega : 0<w)
  have a:=(div_lt_iff₀ pos).mp t
  have b:=(div_lt_div_iff₀ pos (show (0:ℝ)<n+1 by positivity)).mp p
  constructor
  · exact_mod_cast a.le
  · have : ((n:ℝ)+1)*(runs w:ℝ)≤(w:ℝ) := by linarith [mul_comm ((n:ℝ)+1) (runs w:ℝ)]
    exact_mod_cast this

private theorem even_size {w : ℕ} (even : Even w) (e b n c : ℕ) :
    Even (e*2+w^2+b*w^2+(n+c)*(64*w)) := by
  obtain ⟨k,rfl⟩:=even
  exact ⟨e+2*k^2+b*(2*k^2)+(n+c)*(64*k),by ring⟩

section
variable (B : Block F) (m A : ℕ)
open GridChosenReceiver

set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
/-- Simultaneously on the actual output of every elected trace of the installed grid,
at every sufficiently large aligned age. The numerical calibration uses the fixed block,
its true repetition count and the independent raw dimensions of the evaluator. -/
theorem ready {ages runs : ℕ→ℕ} (scale : Scale ages runs) :
    ∀ᶠ w : ℕ in atTop,Even w → 64*w=16*(receiverAge w)^10 →
    ∀ (v : TickSelection F (m+1) A w Q loss) (I : Installed B m A w (degree B) (stageRate B) rootRate v)
      {tariff power : ℕ} (R : GridInstalledFit.Receipt B m A w (degree B) (stageRate B) rootRate v I tariff power),
      I.axes+1=ages w+1-w/2 → I.D.passes=runs w →
      let A0 := GridInstalledEvaluator.layout m A w (overhead Q loss w) v.copies (degree B) (stageRate B) rootRate
      let capacity := GridDescription.capacity w
      let gate := 26*GridDescription.sector w
      ∀ (geom : ElectionRoom I.D A0) (recv : Machine (64*w) capacity capacity capacity)
        (safe : GridNativeDispatch.WordRoom I.D) (z : I.D.trace)
        (x : GridDiagonal.Pins (Fin (GridControllerSimGeometry.railCount m A0.sideMinusOne A0.bank)))
        (c : Cell (m+1) A0.sideMinusOne) (j : Fin v.copies) (elected : Memory (64*w)),
        let valid := GridNativeDispatch.selectorRoom I.D A0 R.table R.selector safe
        let sel := InputWindow I.D A0 z safe valid
        let raw := streamInput I recv 0 gate R.text (R.rooms recv 0 gate).choose
          (fun i => (v.replacement.width_le_size i).trans v.size_le)
          (GridNativeDispatch.actualTable I.D safe).codes valid z x c j
        ∀ hist : TraceReceiverElectedJournal.Journal I.D A0 geom safe z sel (GridTicks.index (c,j))
          (shifted A0 w raw) (original I.D A0 sel raw) elected,
          Ready I.D A0 hist := by
  filter_upwards [TraceReceiverOriginalSeed.geometry B scale,
    TraceAdmission.eventual_receiver_node_count B scale,TraceReceiverCofinalPrices.registered_fixed B,
    TraceReceiverCofinalPrices.registered_tariff B (degree B) (stageRate B) rootRate,
    TraceReceiverSeedInstalled.eventually_fits F B.cursorCopies,
    TraceReceiverTablesMount.admission B,TraceReceiverLibraryMount.sector_room B,
    scale_room scale B.levels,eventually_ge_atTop (64^10+1024)] with
      w actualSeed count tileFee tariff rawFit tables sectors sizes large
  intro even aligned v I hiddenRate hiddenPower R axis passes A0 capacity gate geom recv safe z x c j elected valid sel raw hist
  let tab:=GridNativeDispatch.actualTable I.D safe
  let machine:=(R.rooms recv 0 gate).choose
  let ps:=GridNativeDispatch.params I.D A0 0 gate
  let head:=GridRegisteredPublication.headers (m:=m) (n:=A0.sideMinusOne) (q:=v.copies) I.D
    ps recv sel R.text (c,j)
  let tick:=GridTicks.index (c,j)
  let a:=archive I.D A0
  let dn:=native I.D A0
  let phases:=(I.D.block.repeat I.D.passes).length
  let issued:=I.D.issuedUnit w (degree B) (stageRate B) rootRate
  have pos:=geom.pos
  have big : 64^10≤w:=by omega
  have cpu : GridDescription.capacity w ≤ 64*w := (Nat.div_le_self w 1024).trans (by omega)
  have depthFit : (I.axes+1)+w/2≤2*w+1 := by have:=sizes.1;omega
  have levels : phases ≤ w := by
    rw [show phases = (I.D.block.levels+1)*I.D.passes from I.D.block.length_repeat _, I.block_eq, passes]
    exact sizes.2
  have actualCap:=((R.rooms recv 0 gate).choose_spec sel z).1
  have paid (i) : I.D.work z.1 I.D.issuedCharges issued i≤2^(3*w/5) :=
    ((machine sel z).work_bound i).trans_eq actualCap
  have cf : 0<I.D.block.localCoefficient := by unfold PhysicalStage.Block.localCoefficient;omega
  have tariffPos (age depth setup maps n c : ℕ) (hc : 0 < c) :
      0 < TraceDistribution.FactorWork.archiveTariff age depth setup maps n c := by
    have price : 0 < 10025 + 1016*depth + setup + maps :=
      Nat.add_pos_left (Nat.add_pos_left (Nat.add_pos_left (by decide : 0 < 10025) _) _) _
    exact Nat.mul_pos price (Nat.mul_pos (Nat.succ_pos (2*n))
      (Nat.mul_pos hc (Nat.pow_pos (Nat.succ_pos (16*age^10)))))
  have unit : 0 < issued :=
    tariffPos w (4+phases) (TraceFactorReceiver.Gather.setupPrice phases (stageRate B))
      (TraceFactorReceiver.Gather.mapPrice (degree B) rootRate) phases I.D.block.localCoefficient cf
  have ⟨age,fixed,shrink,refresh⟩:=tileFee (receiverAge w) aligned
  have ⟨allowance,margin⟩:=tariff I.D I.block_eq (receiverAge w) phases aligned levels
  rw [←I.block_eq] at fixed shrink refresh
  have allowed : I.D.block.archiveUnit (receiverAge w) I.D.block.localCoefficient (degree B) ≤ issued := by
    simpa only [issued,I.block_eq] using allowance
  have reserved : 10*(phases+2)^2*(I.D.block.localCoefficient*(64*w+1)^3)≤ issued := by
    simpa only [issued,I.block_eq,aligned] using margin
  rw [←I.block_eq] at sectors rawFit
  have decoder:=rawFit I.D.machine I.D.fit I.D.field I.D.state cpu cpu cpu depthFit
  have pinBits : A0.pinWidth≤2^w := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have prep:=tables I.D I.block_eq cpu cpu cpu depthFit
    (pinBits.trans (Nat.pow_le_pow_right (by decide) (by omega : w≤16*w)))
  have read := stream_header I recv 0 gate R.text machine
    (fun i => (v.replacement.width_le_size i).trans v.size_le) tab.codes valid z x c j
  have headerLength : head.length ≤ A0.pinWidth := read.1
  have ws : 2^w≤ stride (receiverAge w) := by
    change 2^w≤(2^((receiverAge w)^10))^4
    rw [←pow_mul]
    have lower:=receiverAge_lower w
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have sourceRoom : 2+head.length≤a.seed := by
    change 2+head.length≤21*stride (receiverAge w)
    have fits (length span : ℕ) (h : length ≤ span) (pos : 0 < span) :
        2+length ≤ 21*span := by omega
    exact fits _ _ (headerLength.trans (pinBits.trans ws)) ((Nat.two_pow_pos w).trans_le ws)
  have count' := count
  rw [←I.block_eq,←passes] at count' actualSeed
  have rowCount:=count' (I.axes+1) axis I.D.passesFit a.K a.cursor a.seedLayer rfl rfl rfl hist.stagePost
  have seed:=actualSeed I.D.axesFit axis cpu cpu cpu I.D.machine I.D.fit I.D.field I.D.state I.D.passesFit
    A0 z.1 sel R.text (GridDescription.code (q:=w^2) recv I.D.machine) (tick.val:Word (64*w)) raw
    headerLength sourceRoom read.2 R.fits.cut unit paid
  have inputEven : Even I.inputSize := by
    rw [I.input_eq]
    apply even_size even
  exact ⟨aligned,big,depthFit,rowCount,seed.1,seed.2.1,seed.2.2.2.1,seed.2.2.2.2,prep.2.1,
    prep.2.2.1,sectors.1,prep.2.2.2.1,prep.2.2.2.2,decoder,inputEven,age,fixed,shrink,refresh,unit,
    paid,allowed,reserved,seed.2.2.1⟩

end
end
end Hierarchy.TraceReceiverInstalledScalars

end OAI
