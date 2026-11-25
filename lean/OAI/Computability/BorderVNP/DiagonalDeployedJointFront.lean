import OAI.Computability.BorderVNP.DiagonalFrozenPublishedPin
import OAI.Computability.BorderVNP.DiagonalDeployedFrozenBoots
import OAI.Computability.BorderVNP.DiagonalDeployedFrameClock
import OAI.Computability.BorderVNP.DiagonalJointCalibratedClocks

/-! # Local front clocks of the native frozen boot dictionary -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Branch Cover Packing Packing.DeckGrid CellEntries ExternalSew ExternalSew.RowTrace
open VPVNP BurstRAM VerifierNetwork ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open TeamContraction TeamContraction.ProcessorSlots RoutingISA RoutingISA.Pins RoutingISA.Transmission
open GeometryAdvice GeometryFrameEncoding PackedHistoryCircuit TeamScales MvPolynomial
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins
open scoped Classical BigOperators

set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {paid : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField paid aux q k s ord} {chart : AdvisedBranch C}
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r rw pinWidth pc a link ec axes d : ℕ}
    (reader : ChosenReader chart (R+1) r rw rw rw pinWidth) (physical : UniversalMachine.Program)
    (P : TeamOpcode.Program pc 64 32 8) (S : SiteData R r 64 32 rw a)
    (fit : fitsWith physical 64 32 r rw a R link (k+1) ec)
local notation3 (prettyPrint := false) "indexWidth" => (pairedTableParameters (k+1) s+2)*pinWidth
local notation3 (prettyPrint := false) "tail" => setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a)

variable {gridOrder : Fin (GridHosts.tileCount axes d) ≃ (Fin axes → Deck (d+2))}
    (W : WiredWitness (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1)
        (k:=k) (a:=setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a))
        physical fit ((pairedTableParameters (k+1) s+2)*pinWidth)) (Fin.last k) D axes d gridOrder
        (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (pos : (Fin axes → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {ns ne np : ℕ}
    (sites : (W.routedFine pos).Site ↪ Fin ns) (edges : (W.routedFine pos).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1)
      (k:=k) (a:=setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a)) physical fit
      ((pairedTableParameters (k+1) s+2)*pinWidth))) ↪ Fin np)
    (copies bundles headerFactor : ℕ)
    (L : Routing.WireLayout (R+1) r link) {reserve o field : ℕ}
    (t : Table (Fin reserve ⊕ Fin 0) o field) (task : SignedTaskArena.Layout) (exteriorBudget : ℕ)

open Packing.RoutingOutputs CubeHeaderInstall
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.LabelIndex Cube.MeanChoice Crossing Packing CellAddresses
open CellAddressPhysical CellAddressCircuit RoutingISA.Evaluator LocalRow TeamContraction.JointHeader CompactMachine
open ScheduleClock CellMacro.Generator TeamContraction.ProcessorSlots.BootedPinStart

set_option maxHeartbeats 4800000 in
set_option maxRecDepth 9500 in
/-- Charge every team of this prefix of the boot dictionary selected by running
the deployed signed site. The real row writers calibrate the common route. -/
theorem ChosenReader.deployed_joint_prefix_early :
    let tiles := GridHosts.tileCount axes d
    let capacity := seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
    let desc := seedDescriptionWidth (k+1) r axes d (headerFactor*logWidth r (k+1)) (BottomGridBank.bodyBudget capacity)
    let A₀ := reader.startupArenaWith (n:=k+1) (reg:=64) physical a link L.header
    let dir := freeDirectory R r (StartupArena.literal A₀) link tiles
      (GridHosts.inputBlockWidth r (k+1) axes d) (bundles*tiles) desc
    let gap := 7*(Directory.Layout.candidates dir)
    let fresh := StartupArena.next A₀+gap
    let origin := Allocation.dest fresh reserve (Table.size t) o field
    let routed := routingExtension (signedBudgetWords rw exteriorBudget)
      dir origin task.cube.cables task.cube.cells
    let places := fun u : Fin (R+1) => reader.frozenTaskPlacement task A₀ u routed
    let pinned := fun u : Fin (R+1) => CubeHeaderInstall.pinFields (places u).extension
      (Allocation.stop fresh reserve (Table.size t) o field rw) task.cube.header.d (task.cube.n+1)
      (task.cube.h*task.cube.b) task.cube.header.blocks reserve
      (BorderVNP.Cube.Physical.declarationCap task.cube.n task.cube.header.d task.cube.header.blocks task.cube.b task.cube.h task.cube.s)
    let off := StartupArena.literal A₀/4
    let ell := GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve (Table.size t) o field*rw) r
    let sitePlace := fun u : Fin (R+1) => ReaderPlacement.inArena A₀
      (places u).valuation (places u).entry (places u).totals (Allocation.fields (pinned u) fresh reserve (Table.size t) o field off ell)
    let deployed := reader.deployedFrozenSites physical P S fit W pos sites edges ports
      copies bundles headerFactor L t task exteriorBudget
    let slot₀ := adviceOffsetWith physical r 32 64 rw (k+1)
    let packet₀ := fun u : Fin (R+1) => reader.packetAt (sitePlace u)
    let op₀ := fun u : Fin (R+1) => (A₀).operands u slot₀ (packet₀ u)
    let args := fun u : Fin (R+1) => (A₀).unitAddresses slot₀ (packet₀ u)
    let machine := wiringWith physical P deployed indexWidth link (k+1) ec fit
    let pub := (deployed).publicWords
    let registers := (deployed).registers
    let ar := task.cube
    let ctl := controlsBase origin (ar).cables (ar).cells (dir).entries ((dir).teams*(dir).sites)
    let tabs := bases origin (ar).cables (ar).cells (dir).entries
    ∀ (profile : List Bool) (claims : List (List Bool)) (pad : ℕ) (word : Broadcast (ar).n (ar).header.d (ar).header.cap)
    {dim nSites nPorts wordDepth portWidth bitWidth : ℕ} {Port σ : Type} [Fintype Port] [Fintype σ] {bits : Port → ℕ}
    (N : Network dim Port bits) (cell : N.Site → Fin (ar).cells) (amount : N.Site → ℕ)
    (siteID : N.Site ↪ Fin nSites) (edgeID : N.Edge ↪ Fin (ar).cables) (portID : Port ↪ Fin nPorts)
    (F : Fields nSites (ar).cables nPorts (ar).cells wordDepth portWidth bitWidth σ) {z : σ → Bool}
    (original : Fin (dir).entries ↪ N.Site) (live : (Fin (dir).teams × Fin (dir).sites) ↪ Port)
    (_liveWidth : ∀ l, bits (live l)=(dir).block) (_bounds : dir.DestinationBounds)
    (fixed : Routing.Block (R+1)),
    let first := freeStartWith physical r 32 64 rw (k+1)
    let stripe := Allocation.stripe fresh reserve t.size o field off ell
    let bf := fun i : Fin (R+1) => machine.transferFrame i (args i).header (args i).dst
    let loc := fun i : Fin (R+1) => machine.pinLayout i (args i).ibase (args i).hbase (args i).starbase
    ∀ (regions : JointRoom dir first a (signedBootStripe first) stripe)
      (copiesFit : reader.packetBitCount≤r) (memFit : A₀.next<2^rw) (hw : 0<rw) (three : 2<R+1)
      (hdr : 0<L.header) (cap : L.header≤r*link) (bootClock : ∀ u, packetUnitBudget (args u).advice.count rw
        (bf u) (loc u)≤S.limit.val) (col : Fin indexWidth → Bool) (extWire : {v // PositiveExterior machine args col rw v}),
      let selected := reader.deployedFrozenSites_boots physical P S fit W pos sites edges ports
        copies bundles headerFactor L t task exteriorBudget fixed regions copiesFit memFit hw three hdr cap bootClock
      let crew := selected.2.choose col extWire
      ∀ tuple : PinStart.JointPrefix task.id (fun i => (crew i).start),
      let rr := NativeDemands.rows N cell edgeID portID dir original live task.p.privateGap
      let cpu := fun i : Fin (R+1) => machine.processorFields i col extWire.val (args i).ibase (args i).hbase (args i).starbase
      let sub := fun i : Fin (R+1) => (tuple i).1
      let pinRun := fun i : Fin (R+1) => (crew i).pins (tuple i).1
      let used := fun i : Fin (R+1) => (crew i).used+traceCost (pinRun i).val.1
      let lib := fun i : Fin (R+1) => install SparseExterior.driver (k+1) (crew i).start.routines
      let init := fun i : Fin (R+1) => processorMemory (cpu i) rw
      let Full := fun i : Fin (R+1) => Returns (withStartup pinGeometry) (pub i) (lib i) (registers i) (init i)
      let header := padded (spelling (profile++DeclarationBits.spelling word) claims) pad
      let axis := Fin.ofNat (ar.n+1) (readCode (ar.n+1) word.1)
      let geoCost := GeometryAdviceRate.ticks t.size reserve o field rw
      let cost := fun i : Fin (R+1) => jointBudget (packet₀ i).bits.length rw+(bf i).readTicks+2+
        ((pinSetup.slots+17*(op₀ i).layout.count+1)+geoCost)
      let vst := fun i : Fin (R+1) => PinStart.visits task.id (fun j => (crew j).start) (tuple i)
      ∀ (_net : Represents N cell amount siteID edgeID portID F z) (_ids : ∀ c,(F.cells c).val=c.val)
    (_wireFit : ∀ c, guessedSize N cell c+siteSize N cell c amount+suppliedSize N cell c<2^bitWidth)
    (_hk : portWidth≤bitWidth) (_hb : bitWidth≤rw) (_positive : 0<ar.cells)
    (_privateTail : dir.entries*dir.description≤dir.teams*dir.processors*(dir.literal/2))
    (_shape : profile.length=reserve) (_length : header.length=L.header)
    (_ends : ctl+28≤ar.header.header)
    (_words : Directory.ISA.wordBound (Directory.ISA.placementBound dir tabs.privatePairs tabs.livePairs ar.cellStride)<2^rw)
    (_teamCount : ar.teams=R+1) (_processors : 0<r)
    (_guard : SelectedRawWriterRoom ar dir rw exteriorBudget A₀.next reserve t.size o field)
    (_sparse : ExternalSew.intercellWidth N cell≤2*dir.teams*exteriorBudget)
    {α ξ : ℝ} (_table : RouteTableInputs ar dir α ξ (k+1) rw A₀.frame link)
    (_fixedBudget : exteriorBudget=TeamScales.exterior ξ r (k+1))
    (_lit : A₀.literal≤TeamScales.literal α (k+1)) (_headerRoom : (L.header:ℝ)≤r*((k+1:ℕ):ℝ)^(24/25:ℝ))
    (_bound : CoreAt α ξ (k+1)) (budget : PhaseCharges)
    (_window : ∀ after : ℕ → ℕ, let lab := LabelIndex.layout A₀.frame after
      lab.cells=ar.cells → lab.cableCount=ar.cables → lab.deliveryCount=rr.length → lab.labels=ar.alphabet →
      2048*(exteriorBudget+(R+1+1)^3+(rr.length+ar.header.d.choose 2)+r+1)≤budget.core ∧
        geoCost+beforeDirectory (R+1) dir.sites dir.entries+
          rawScheduleTicks ar A₀.frame A₀.broadcastBase axis.val R rr.length after≤budget.before)
    (_decoded : ∀ i : Fin (R+1), ∃ (dest : ℕ) (values : Fin o → ℕ) (ret : (Full i)),
      ProfilePaths (withStartup pinGeometry) (crew i).start.guessWidth (pub i) (lib i) (registers i)
        (init i) True (cost i) dest values
        (BootResidence (F:=(cpu i)) A₀ i slot₀ (packet₀ i) (bf i) (args i).advice (pub i) (lib i)
          header (init i) (registers i)) ∧
      ret.val.1.flatMap TeamRAM.Event.choices=List.ofFn (sub i) ∧
      PublishedPin task dir N cell edgeID portID original live A₀ i slot₀ (packet₀ i) origin task.p.privateGap (bf i)
        header (cpu i) (pub i) (lib i) (sub i) (pinRun i).val.2.1 (pinRun i).val.2.2 ret.val.2.1 ret.val.2.2
          (used i) (traceCost ret.val.1) ∧
      Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) z origin (readings ret.val.2.2) ∧
      ∀ j : Fin 37, readings ret.val.2.2 (ctl+j.val)=task.controls j.val),
    ∀ u, (crew u).used+traceCost (pinRun u).val.1+traceCost (vst u).profile.val.1+
      traceCost (vst u).routing.val.1≤budget.core+budget.before := by
  intro tiles capacity desc A₀ dir gap fresh origin routed places pinned off ell sitePlace deployed
    slot₀ packet₀ op₀ args machine pub registers ar ctl tabs profile claims pad word dim nSites nPorts wordDepth portWidth
    bitWidth Port σ _ _ bits N cell amount siteID edgeID portID F z original live liveWidth bounds fixed first stripe bf loc
    regions copiesFit memFit hw three hdr cap bootClock col extWire selected crew tuple rr cpu sub pinRun used lib init
    Full header axis geoCost cost vst net ids wireFit hk hb positive privateTail shape length ends words teamCount
    processors guard sparse α ξ table fixedBudget lit headerRoom bound budget window decoded
  classical
  let query := Fintype.card (Board.Physical (pairedTableParameters (k+1) s) pinWidth rw (paid.Entry ⊕ ι))
  let guesses := Fintype.card (Guess (Fin (pairedTableParameters (k+1) s)) reader.gridRank (Nat.clog 2 C.p+1) (Nat.clog 2 C.p))
  let ordinary := SignedTaskArena.withOrdinary S (fun _ => task) A₀
    (fun _ => origin) (fun _ => 0) (fun _ => query) (fun _ => guesses) (fun _ => reader.gates)
  let extensions := fun u : Fin (R+1) => Allocation.fields (pinned u) fresh reserve t.size o field off ell
  have fitted (i : Fin (R+1)) : (op₀ i).Fits rw := by
    have h := reader.arena_fitsWith physical P ordinary fit (fun v => (places v).valuation)
      (fun v => (places v).entry) (fun v => (places v).totals) extensions L i hdr copiesFit memFit
    have op := reader.siteOperands_arenaWith physical P ordinary fit (fun v => (places v).valuation)
      (fun v => (places v).entry) (fun v => (places v).totals) extensions L i
    exact (congrArg (fun b : PacketOperands => b.Fits rw) op).mp h.1
  have block : 0<dir.block := by
    change 0<blockWidth (r*(k+1)) tiles
    have vp : 0<tiles := Fintype.card_pos
    apply Nat.pos_of_ne_zero
    intro zero
    have volume := (ceilDiv_le_iff_le_mul vp).mp zero.le
    have volumePos := Nat.mul_pos processors (Nat.succ_pos k)
    simp at volume
    omega
  let raw := SignedTaskArena.rawAddress A₀ ar.header.profile ar.n ar.header.d ar.header.cap
  let rcv := NativeDemands.receiver N cell edgeID portID dir original live task.p.privateGap bounds
  choose dest values ret paths digits pubRun image controls using decoded
  have choice := fun u => reader.deployedFrozenSites_profile_charge physical P S fit W pos sites edges ports copies
    bundles headerFactor L t task exteriorBudget u col extWire.val (crew u) (paths u) (sub u) (ret u) (digits u)
  choose dictionary spells dictAt costFit using choice
  have received := fun u => reader.deployedFrozenSites_pin_writer physical P S fit W pos sites edges ports copies bundles
    headerFactor L t task exteriorBudget profile claims pad word N cell amount siteID edgeID portID F original live liveWidth
    bounds task.id crew tuple u net ids wireFit hk hb positive privateTail (pf:=cpu u) (ad:=(args u).advice) (dictionary u) (spells u) (ret u) (digits u)
    ((paths u).memory (ret u) (sub u) (digits u)) (pubRun u) (image u) (controls u)
    shape length (fitted u) ends words teamCount processors guard sparse table
  choose epoch published mid scan atEpoch atPub empty paid scanAt scanCost sources inputSize pointers slotted rawInput
    rowPlacement writer dims using fun u => (received u).2.2.2
  let writer₀ := (slotted 0).some
  have budgetFits : exteriorBudget<2^rw := by
    calc exteriorBudget ≤ 1000000*exteriorBudget := Nat.le_mul_of_pos_left _ (by decide)
         _ ≤ 1000000*exteriorBudget*(R+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos R)
         _ < 2^rw := guard.scaled
  have originFit (i : Fin (R+1)) : (pub i 0).val=A₀.frame := by
    have pubAt := (reader.deployedFrozenSites_publication physical P S fit W pos sites edges ports copies bundles
      headerFactor L t task exteriorBudget i budgetFits).1
    exact (congrArg Fin.val (congrFun pubAt 0)).trans ((op₀ i).frameBase_word _ (fitted i))
  have pinRoom (u : Fin (R+1)) : A₀.frame+13<(args u).ibase ∧ (args u).ibase+(loc u).count≤ar.header.header := by
    change A₀.frame+13<A₀.ibase ∧ A₀.hbase≤ar.header.header
    refine ⟨?_,(Nat.le_add_right _ A₀.count).trans ((Nat.le_add_right A₀.next _).trans writer₀.rawEnd)⟩
    unfold StartupArena.ibase StartupArena.broadcastBase StartupArena.dense
    omega
  have fitsClock (u : Fin (R+1)) := window (readings (scan u).val.2.2) (dims u).1 (dims u).2.1
    (dims u).2.2.1 (dims u).2.2.2
  let rowPriv := NativeDemands.privatePair N cell edgeID portID dir original live task.p.privateGap
  let rowLive := NativeDemands.livePair N cell edgeID portID dir original live task.p.privateGap
  let sizes := fun i : Fin rr.length => (rr[i.val]'i.isLt).width
  let label := meanPackedLabel N cell rcv sizes (List.finRange ar.cells) ar.n ar.header.d (Nat.zero_lt_of_lt guard.two)
  let previous := routingExtension (task.extension raw 0 rw (signedBudgetWords rw exteriorBudget)) dir origin ar.cables ar.cells
  have localClock : ∀ u, ProfileClock (ar:=ar) task.id crew tuple u L.header reader.packetBitCount geoCost
      (deliveryScanTicks dir.entries (R+1) dir.sites) (scan u).val.2 budget := joint_calibrated_clocks (ar:=ar) (G:=machine) (pub:=pub) (reg:=registers) (args:=args)
    (D:=dir) (pp:=rowPriv) (lp:=rowLive) (frame:=A₀.frame) (hdr:=L.header) (α:=α) (ξ:=ξ)
    (atWriter:=fun i => (scan i).val.2) task.id crew tuple word label rcv epoch published empty scanAt (fun i => (writer i).some)
    table originFit (fun _ => rfl) (fun i => pointers i _) sources inputSize pinRoom (fun i => (selected.1 i).1.physical)
    writer₀ (atPub 0) rfl rfl rfl lit headerRoom previous fresh t.size o field off ell ctl profile claims pad (fixedBudget ▸ rawInput 0)
    (received 0).2.1 (fixedBudget ▸ (received 0).2.2.1) (NativeDemands.receiver_val N cell edgeID portID dir original live task.p.privateGap bounds) processors (Nat.le_refl 2) block budget reader.packetBitCount
    geoCost bound (fixedBudget ▸ (fitsClock 0).1) (fun i => (fitsClock i).2)
  intro u
  have count := reader.packetAt_length (sitePlace u)
  have operands := reader.deployedFrozenSites_frontOperands physical P S fit W pos sites edges ports copies bundles headerFactor
    L t task exteriorBudget u
  apply localClock u (dictionary u) (scan u) operands.2.2.1 (operands.2.1.trans_eq count) copiesFit (spells u)
  · change traceCost ((dictionary u) (sub u)).val.1 ≤ jointBudget reader.packetBitCount rw+(bf u).readTicks+2+
        (pinSetup.slots+17*((bf u).processors*(bf u).literal)+1)+geoCost
    rw [dictAt u,←count]
    exact costFit u
  · rfl
  · exact scanCost u

end Diagonal

end BorderVNP
end Computability
end OAI
