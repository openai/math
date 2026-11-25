import OAI.Computability.BorderVNP.DiagonalFrozenRawWriter
import OAI.Computability.BorderVNP.DiagonalFrozenReturnInputs
import OAI.Computability.BorderVNP.DiagonalReturnedWriterScan

/-! # The returned directory writer on an equal sewn-network layout -/

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
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.Tally Cube.LabelIndex Cube.MeanChoice Crossing Packing CellAddresses
open Directory.PrivateBank CellAddressPhysical CellAddressCircuit RoutingISA.Evaluator LocalRow TeamContraction.JointHeader CompactMachine

set_option maxHeartbeats 2400000 in
/-- The actual installed boot keeps its original site, pin and register type
when the geometry proof obtains its cell and edge counts from the sewn
network. Equality of the two layouts identifies the writer receipts. -/
theorem ChosenReader.deployedFrozenSites_returned_writer (geometry : SignedTaskArena.Layout) (same : geometry=task) :
    let tiles := GridHosts.tileCount axes d
    let capacity := seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
    let desc := seedDescriptionWidth (k+1) r axes d (headerFactor*logWidth r (k+1)) (BottomGridBank.bodyBudget capacity)
    let A₀ := reader.startupArenaWith (n:=k+1) (reg:=64) physical a link L.header
    let dir := freeDirectory R r (StartupArena.literal A₀) link tiles
      (GridHosts.inputBlockWidth r (k+1) axes d) (bundles*tiles) desc
    let gap := 7*(Directory.Layout.candidates dir)
    let fresh := StartupArena.next A₀+gap
    let origin := Allocation.dest fresh reserve (Table.size t) o field
    let query := Fintype.card (Board.Physical (pairedTableParameters (k+1) s) pinWidth rw (paid.Entry ⊕ ι))
    let guesses := Fintype.card (Guess (Fin (pairedTableParameters (k+1) s)) reader.gridRank
      (Nat.clog 2 C.p+1) (Nat.clog 2 C.p))
    let _ordinary := SignedTaskArena.withOrdinary S (fun _ => task) A₀
      (fun _ => origin) (fun _ => 0) (fun _ => query) (fun _ => guesses) (fun _ => reader.gates)
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
    let ar := geometry.cube
    let raw := SignedTaskArena.rawAddress A₀ (ar).header.profile (ar).n (ar).header.d (ar).header.cap
    let ctl := controlsBase origin (ar).cables (ar).cells (dir).entries ((dir).teams*(dir).sites)
    let tabs := bases origin (ar).cables (ar).cells (dir).entries
    ∀ (profile : List Bool) (claims : List (List Bool)) (pad : ℕ) (word : Broadcast (ar).n (ar).header.d (ar).header.cap)
    {dim nSites nPorts wordDepth portWidth bitWidth : ℕ} {Port σ : Type} [Fintype Port] [Fintype σ] {bits : Port → ℕ}
    (N : Network dim Port bits) (cell : N.Site → Fin (ar).cells) (amount : N.Site → ℕ)
    (siteID : N.Site ↪ Fin nSites) (edgeID : N.Edge ↪ Fin (ar).cables) (portID : Port ↪ Fin nPorts)
    (F : Fields nSites (ar).cables nPorts (ar).cells wordDepth portWidth bitWidth σ) {z : σ → Bool}
    (original : Fin (dir).entries ↪ N.Site) (live : (Fin (dir).teams × Fin (dir).sites) ↪ Port)
    (_liveWidth : ∀ l, bits (live l)=(dir).block) (bounds : dir.DestinationBounds)
    {col : Fin indexWidth → Bool} {extWire : Exterior R r link → Bool}
    (u : Fin (R+1)) (node : BootedPinStart SparseExterior.driver machine pub registers args col extWire u)
    (sub : Fin node.start.guessWidth → Bool),
    let dataGap := geometry.p.privateGap
    let rr := NativeDemands.rows N cell edgeID portID dir original live dataGap
    let rcv := NativeDemands.receiver N cell edgeID portID dir original live dataGap bounds
    let sz := fun i : Fin (rr).length => (rr)[i.val].width
    let rowPriv := NativeDemands.privatePair N cell edgeID portID dir original live dataGap
    let rowLive := NativeDemands.livePair N cell edgeID portID dir original live dataGap
    let f₀ := (machine).transferFrame u ((args) u).header ((args) u).dst
    let subRun := node.pins sub
    let used := node.used+traceCost (subRun).val.1
    let mac := install SparseExterior.driver (k+1) (TeamSiteEvents.macros (w:=rw) (siteLibrary SparseExterior.driver) (nativeClock (k+1)))
    let init := processorMemory
      ((machine).processorFields u col extWire ((args) u).ibase ((args) u).hbase ((args) u).starbase) rw
    let Full := Returns (withStartup pinGeometry) ((pub) u) mac ((registers) u) init
    let header := padded (spelling (profile++DeclarationBits.spelling word) claims) pad
    let axis := Fin.ofNat ((ar).n+1) (readCode ((ar).n+1) word.1)
    let decl := Prod.mk axis (fun (p : Sym2 (Fin (ar).header.d)) (j : Fin ((ar).n+1)) =>
      readCode ((ar).header.cap+1) (word.2 p j))
    let supply := Sum.elim (fun z : SuppliedWord N cell => z.1) (id : Fin geometry.cube.cells → Fin geometry.cube.cells)
    let sWidth := Sum.elim (supplyWidth N cell) (fun _ : Fin geometry.cube.cells => dataGap)
    let sId := reserveID (C := geometry.cube.cells) (suppliedID N cell edgeID portID)
    let host := Sum.elim supply (cell ∘ original)
    let key := numbered sId
    let sizes := Sum.elim sWidth (fun _ : Fin (dir).entries => (dir).description)
    let previous := routingExtension (geometry.extension raw u.val rw (signedBudgetWords rw exteriorBudget)) dir origin (ar).cables (ar).cells
    ∀ (_net : Represents N cell amount siteID edgeID portID F z) (_ids : ∀ c,(F.cells c).val=c.val)
    (_wireFit : ∀ c, guessedSize N cell c+siteSize N cell c amount+suppliedSize N cell c<2^bitWidth)
    (_hk : portWidth≤bitWidth) (_hb : bitWidth≤rw) (_positive : 0<(ar).cells)
    (_privateTail : (dir).entries*(dir).description≤(dir).teams*(dir).processors*((dir).literal/2))
    {pf : Pins.ProcessorFields (op₀ u).layout} {ad : AdviceLayout}
    (paths : (Fin node.start.guessWidth → Bool) ≃ Full)
    (_spells : ∀ v,(paths v).val.1.flatMap TeamRAM.Event.choices=List.ofFn v)
    (ret : Full) (_digits : ret.val.1.flatMap TeamRAM.Event.choices=List.ofFn sub)
    (_kept : BootResidence (F:=pf) A₀ u slot₀ (packet₀ u) f₀ ad ((pub) u) mac header init ((registers) u) sub ret.val.2.2)
    (_published : PublishedPin geometry dir N cell edgeID portID original live A₀ u slot₀ (packet₀ u) origin dataGap f₀ header pf
      ((pub) u) mac sub (subRun).val.2.1 (subRun).val.2.2 ret.val.2.1 ret.val.2.2 used (traceCost ret.val.1))
    (_img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) z origin (readings ret.val.2.2))
    (_controls : ∀ j : Fin 37, readings ret.val.2.2 (ctl+j.val)=geometry.controls j.val)
    (_shape : profile.length=reserve) (_length : (header).length=L.header) (_fitted : (op₀ u).Fits rw)
    (_ends : ctl+28≤(ar).header.header)
    (_words : Directory.ISA.wordBound (Directory.ISA.placementBound dir (tabs).privatePairs (tabs).livePairs (ar).cellStride)<2^rw)
    (_teamCount : (ar).teams=R+1) (_processors : 0<r)
    (guard : SelectedRawWriterRoom ar dir rw exteriorBudget (A₀).next reserve (Table.size t) o field)
    (_sparse : ExternalSew.intercellWidth N cell≤2*(dir).teams*exteriorBudget)
    {α ξ : ℝ} (_table : RouteTableInputs ar dir α ξ (k+1) rw (A₀).frame link),
    let label := meanPackedLabel N cell rcv sz (List.finRange (ar).cells) (ar).n (ar).header.d (Nat.zero_lt_of_lt guard.two)
    let mass := declarationWeight (ar).header.blocks (ar).b (ar).K (ar).h decl label rcv sz
    let group := fun j : Fin (ar).header.d => TeamNative.owner R mass j.val
    let owner := fun c : ℕ => if h:c<(ar).cells then group (label ⟨c,h⟩ axis) else 0
    ReturnedWriterScan ar dir rr rowPriv rowLive pf f₀ (Pins.extendGuess sub) ((pub) u) mac
      (paths sub) ret subRun.val.2.1 subRun.val.2.2 used (A₀).frame (A₀).next host key sizes
      previous fresh (Table.size t) o field off ell ctl profile claims pad word exteriorBudget
      N cell rcv sz label decl group owner := by
  cases same
  intro tiles capacity desc A₀ dir gap fresh origin query guesses ordinary routed places pinned off ell sitePlace deployed slot₀ packet₀ op₀ args machine pub registers ar raw ctl tabs
    profile claims pad word dim nSites nPorts wordDepth portWidth bitWidth Port σ _ _ bits
    N cell amount siteID edgeID portID F z original live liveWidth bounds col extWire u node sub
  have result := reader.deployedFrozenSites_raw_writer physical P S fit W pos sites edges ports
    copies bundles headerFactor L t task exteriorBudget profile claims pad word N cell amount siteID edgeID
    portID F (z:=z) original live liveWidth bounds u node sub
  rw [←node.installed_routines_at] at result
  exact result

end Diagonal

end BorderVNP
end Computability
end OAI
