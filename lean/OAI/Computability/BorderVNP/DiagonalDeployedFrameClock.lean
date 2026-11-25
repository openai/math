import OAI.Computability.BorderVNP.DiagonalDeployedFrozenFront
import OAI.Computability.BorderVNP.DiagonalWriterProfileClock

/-! # The admitted profile clock on the deployed signed verifier -/

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


local notation "off" => StartupArena.literal A₀/4
local notation "ell" => GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve (Table.size t) o field*rw) r
local notation3 (prettyPrint := false) "sitePlace" => fun u : Fin (R+1) => ReaderPlacement.inArena A₀
  (places u).valuation (places u).entry (places u).totals (Allocation.fields (pinned u) fresh reserve (Table.size t) o field off ell)
local notation3 (prettyPrint := false) "deployed" => reader.deployedFrozenSites physical P S fit W pos sites edges ports
  copies bundles headerFactor L t task exteriorBudget

open RoutingISA.Evaluator RoutingISA.CompactMachine CellMacro.Generator ScheduleClock

/-- Discharge the geometry part of the returned frame's clock with the very
profile return and directory scan on the installed signed verifier. -/
theorem ChosenReader.deployedFrozenSites_early (u : Fin (R+1)) (pin : Fin indexWidth → Bool)
    (ext : Exterior R r link → Bool) (copiesFit : reader.packetBitCount≤r) :
    let G := wiringWith physical P deployed indexWidth link (k+1) ec fit
    let pack := fun j : Fin (R+1) => reader.packetAt (sitePlace j)
    let slot := adviceOffsetWith physical r 32 64 rw (k+1)
    let args := fun j => (A₀).unitAddresses slot (pack j)
    let op := reader.siteOperandsWith physical P ordinary sitePlace fit L.header u
    let f := G.transferFrame u L.header (A₀).broadcastBase
    let F := G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase
    let init := processorMemory F rw
    let pub := (deployed).publicWords u
    let bank := (deployed).registers u
    let count := (pack u).bits.length
    let geometry := GeometryAdviceRate.ticks t.size reserve o field rw
    let cost := jointBudget count rw+f.readTicks+2+((pinSetup.slots+17*op.layout.count+1)+geometry)
    ∀ (B : ∀ j, BootedPinStart SparseExterior.driver G (deployed).publicWords (deployed).registers args pin ext j)
      (joint : PinStart.JointPrefix task.id (fun j => (B j).start)),
      let mac := install SparseExterior.driver (k+1) (B u).start.routines
      let visit := PinStart.visits task.id (fun j => (B j).start) (joint u)
      ∀ {dest scanTicks : ℕ} {values : Fin o → ℕ} {resident : (Fin (B u).start.guessWidth → Bool) → Memory rw → Prop}
        {scheduled : Bank rw × Memory rw} {budget : PhaseCharges},
        BootedPinStart.ProfileClock (ar:=task.cube) task.id B joint u L.header count geometry scanTicks scheduled budget →
        ProfilePaths (withStartup pinGeometry) (B u).start.guessWidth pub mac bank init True cost dest values resident →
        ∀ (ret : Returns (withStartup pinGeometry) pub mac bank init)
          (scan : Returns (.seq PrivatePlacement.program Directory.ISA.program) pub mac ret.val.2.1 ret.val.2.2),
          ret.val.1.flatMap TeamRAM.Event.choices=List.ofFn (joint u).1 →
          scan.val.2=scheduled → traceCost scan.val.1 ≤ scanTicks →
          (B u).used+traceCost ((B u).pins (joint u).1).val.1+traceCost visit.profile.val.1+
            traceCost visit.routing.val.1≤budget.core+budget.before := by
  intro G pack slot args op f F init pub bank count geometry cost B joint mac visit dest scanTicks values resident
    scheduled budget front paths ret scan spelled finished time
  obtain ⟨profile,spelling,same,charge⟩ := reader.deployedFrozenSites_profile_charge physical P S fit W pos sites edges
    ports copies bundles headerFactor L t task exteriorBudget u pin ext (B u) paths (joint u).1 ret spelled
  subst ret
  have operands := reader.deployedFrozenSites_frontOperands physical P S fit W pos sites edges ports copies bundles
    headerFactor L t task exteriorBudget u
  exact front profile scan operands.2.2.1 operands.2.1 (operands.1.trans_le copiesFit) spelling charge finished time

end Diagonal

end BorderVNP
end Computability
end OAI
