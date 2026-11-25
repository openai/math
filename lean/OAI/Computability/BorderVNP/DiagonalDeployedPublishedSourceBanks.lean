import OAI.Computability.BorderVNP.DiagonalDeployedOwnedBanks
import OAI.Computability.BorderVNP.DiagonalPublishedOriginalCut

/-! # Protected reader fields from the deployed positive site’s published pin -/

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
local notation "indexWidth" => (pairedTableParameters (k+1) s+2)*pinWidth
local notation "tail" => setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a)

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

local notation "tiles" => GridHosts.tileCount axes d
local notation "capacity" => seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
local notation "desc" => seedDescriptionWidth (k+1) r axes d (headerFactor*logWidth r (k+1)) (BottomGridBank.bodyBudget capacity)
local notation3 (prettyPrint := false) "A₀" => reader.startupArenaWith (n:=k+1) (reg:=64) physical a link L.header
local notation "dir" => freeDirectory R r (StartupArena.literal A₀) link tiles
  (GridHosts.inputBlockWidth r (k+1) axes d) (bundles*tiles) desc
local notation "gap" => 7*(Directory.Layout.candidates dir)
local notation "fresh" => StartupArena.next A₀+gap
local notation "origin" => Allocation.dest fresh reserve (Table.size t) o field
local notation "query" => Fintype.card (Board.Physical (pairedTableParameters (k+1) s) pinWidth rw (paid.Entry ⊕ ι))
local notation "guesses" => Fintype.card (Guess (Fin (pairedTableParameters (k+1) s)) reader.gridRank
  (Nat.clog 2 C.p+1) (Nat.clog 2 C.p))
local notation3 (prettyPrint := false) "ordinary" => SignedTaskArena.withOrdinary S (fun _ => task) A₀
  (fun _ => origin) (fun _ => 0) (fun _ => query) (fun _ => guesses) (fun _ => reader.gates)
local notation3 (prettyPrint := false) "routed" => routingExtension (signedBudgetWords rw exteriorBudget)
  dir origin task.cube.cables task.cube.cells
local notation3 (prettyPrint := false) "places" u => reader.frozenTaskPlacement task A₀ u routed
local notation3 (prettyPrint := false) "pinned" u => CubeHeaderInstall.pinFields (places u).extension
  (Allocation.stop fresh reserve (Table.size t) o field rw) task.cube.header.d (task.cube.n+1)
  (task.cube.h*task.cube.b) task.cube.header.blocks reserve
  (BorderVNP.Cube.Physical.declarationCap task.cube.n task.cube.header.d task.cube.header.blocks task.cube.b task.cube.h task.cube.s)
local notation "first" => freeStartWith physical r 32 64 rw (k+1)

open SignedTaskArena Routing RoutingISA.Evaluator JointHeader BorderVNP.Cube RoutingISA.CompactMachine

local notation3 (prettyPrint := false) "geomOff" => StartupArena.literal A₀/4
local notation3 (prettyPrint := false) "stripeWidth" => GeometryAdviceRate.stripeWidth
  (GeometryOutput.packetCount reserve (Table.size t) o field*rw) r
local notation3 (prettyPrint := false) "geom" => Allocation.stripe fresh reserve (Table.size t) o field geomOff stripeWidth
local notation3 (prettyPrint := false) "geometryBits" => fun _ : Fin (R+1) =>
  GeometryAdvice.serialized (GeometryAdvice.packet (w:=rw) fresh (Allocation.packed fresh reserve (Table.size t) o field rw)
    t (fun i => StartupArena.broadcastBase A₀+1+Fin.val i))
local notation3 (prettyPrint := false) "strings" => W.seedLiteralMatrix pos (ParseTable.signedLiteralCode ord) sites edges ports
  copies bundles (headerFactor*logWidth r (k+1))
local notation3 (prettyPrint := false) "deployed" => reader.deployedFrozenSites physical P S fit W pos sites edges ports
  copies bundles headerFactor L t task exteriorBudget
local notation3 (prettyPrint := false) "extra" u => Allocation.fields (pinned u) fresh reserve (Table.size t) o field geomOff stripeWidth
local notation3 (prettyPrint := false) "payload" u => reader.packetAt (ReaderPlacement.inArena A₀
  (places u).valuation (places u).entry (places u).totals (extra u))
local notation3 (prettyPrint := false) "signedRaw" => rawAddress A₀ task.cube.header.profile task.cube.n task.cube.header.d
  task.cube.header.cap

open Physical Scatter Scatter.Assignment TeamRows Diagonal.Layout DiagonalTallyPacketEmit

set_option maxHeartbeats 3400000
set_option maxRecDepth 8500

/-- Every original positive team's reached source has the boot's true reader
and subtotal header. The independently returned directory also supplies the
signed pointer array. All three observations use the stored publication of the
installed site and its actual protected low memory. -/
theorem ChosenReader.deployed_published_source_banks
    (fixed : Routing.Block (R+1)) (regions : JointRoom dir first a (signedBootStripe first) geom)
    (copiesFit : reader.packetBitCount ≤ r) (ceiling : (A₀).next < 2^rw) (hw : 0<rw)
    (teams : task.cube.teams=R+1) (teamFit : R+1<2^rw) (secondary : (A₀).next ≤ task.cube.header.header)
    (endFits : task.endAddress rw query guesses reader.gates < 2^rw) :
    let T := deployed
    let G := wiringWith physical P T indexWidth link (k+1) ec fit
    let off := adviceOffsetWith physical r 32 64 rw (k+1)
    let args := fun u => (A₀).unitAddresses off (payload u)
    let frame := fun u => G.transferFrame u (args u).header (args u).dst
    let loc := fun u => G.pinLayout u (args u).ibase (args u).hbase (args u).starbase
    (∀ u, (args u).Fitted G u (payload u) (T.publicWords u) off ∧
      packetUnitBudget (args u).advice.count rw (frame u) (loc u) ≤ T.limit.val) →
    ∀ (pin : Fin indexWidth → Bool) (x : {z // PositiveExterior G args pin rw z})
      (B : (i : Fin (R+1)) → BootedPinStart SparseExterior.driver G T.publicWords T.registers args pin x.val i)
      (active : (i : Fin (R+1)) → (B i).start.Prefix task.id) (u : Fin (R+1))
      (p : PositiveFields task.cube.header.profile task.cube.n task.cube.header.d task.cube.header.cap
        task.cube.teams task.dim rw), p.bits=observed L x.val fixed →
      BootedPinStart.PublishedSourceReadback task B active u A₀ p origin
        (6+3*reader.gates+query) indexWidth := by
  intro T G off args frame loc ready pin x B active u p header
  have start := reader.deployed_boot_reader physical P S fit W pos sites edges ports copies bundles headerFactor L t task
    exteriorBudget fixed regions copiesFit ceiling hw teams teamFit secondary endFits ready pin x u (B u)
  have seed := (start.2.2.2 p header).1
  have size : (A₀).header=PositiveFields.width task.cube.header.profile task.cube.n task.cube.header.d
      task.cube.header.cap task.cube.teams task.dim rw :=
    (observed_length L x.val fixed).symm.trans ((congrArg List.length header).symm.trans p.bits_length)
  have positive : 0<L.header := by rw [show L.header=(A₀).header from rfl,size]; unfold PositiveFields.width; omega
  have bounds := reader.chosen_packet_pin_bounds physical P T fit (fun i => (places i).valuation)
    (fun i => (places i).entry) (fun i => (places i).totals) (fun i => extra i) L u positive copiesFit ceiling
  let op := reader.siteOperandsWith physical P ordinary (fun i => ReaderPlacement.inArena A₀
    (places i).valuation (places i).entry (places i).totals (extra i)) fit L.header u
  have fitsAll := reader.arena_fitsWith physical P ordinary fit (fun i => (places i).valuation)
    (fun i => (places i).entry) (fun i => (places i).totals) (fun i => extra i) L u positive copiesFit ceiling
  have atFrame : (T.publicWords u 0).val=(A₀).frame := op.frameBase_word ((ordinary).publicWords u) fitsAll.1
  have ge : (A₀).next≤origin := by unfold Allocation.dest Allocation.temp; omega
  intro wire₀ hdr₀ len₀ pub₀ op₀ regs₀ mem₀ who F sourceAt proto amount route owned
  exact BootedPinStart.publishedReadbackFromBoot task B active u A₀ p origin (6+3*reader.gates+query) indexWidth
    bounds.2.2.2.2.2.2 bounds.2.2.2.2.2.1 rfl rfl atFrame size seed ge secondary F sourceAt owned

end Diagonal

end BorderVNP
end Computability
end OAI
