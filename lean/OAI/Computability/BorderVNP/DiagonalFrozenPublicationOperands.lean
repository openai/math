import OAI.Computability.BorderVNP.DiagonalFrozenSignedDeployment
import OAI.Computability.BorderVNP.CubeRoutePinnedFrame

/-! # The actual ordinary, extended and budget fields at a deployed signed profile -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM TeamContraction.ProcessorSlots Packing.RoutingOutputs PackedHistoryCircuit

/-- The ordinary task bank installs its complete route bank, demand-base
operand, and three initial geometry fields at the addresses used by the
signed native pin publisher. -/
theorem Layout.ordinary_routed {w : ℕ} (task : Layout) (a : StartupArena)
    (origin plan entry query gates : ℕ) (old : Arg → Word w) :
    let ordinary := task.ordinary a origin plan entry query gates old
    ordinary=core (withDemandBase (task.routeBank a.frame ordinary) a.next) origin task.cube.cables task.cube.cells := by
  intro ordinary
  funext j
  fin_cases j <;> rfl

end RoutingISA.SignedTaskArena

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


local notation "off" => StartupArena.literal A₀/4
local notation "ell" => GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve (Table.size t) o field*rw) r
local notation3 (prettyPrint := false) "sitePlace" => fun u : Fin (R+1) => ReaderPlacement.inArena A₀
  (places u).valuation (places u).entry (places u).totals (Allocation.fields (pinned u) fresh reserve (Table.size t) o field off ell)
local notation3 (prettyPrint := false) "deployed" => reader.deployedFrozenSites physical P S fit W pos sites edges ports
  copies bundles headerFactor L t task exteriorBudget

open Packing.RoutingOutputs CubeHeaderInstall

/-- Every real processor starts its signed publisher with the seven-word
demand destination and profile controls in the actual public argument bank.
Its stored budget is the same integral bound tested by the team scheduler. -/
theorem ChosenReader.deployedFrozenSites_publication (u : Fin (R+1)) (Xfit : exteriorBudget<2^rw) :
    let slot := adviceOffsetWith physical r 32 64 rw (k+1)
    let packet := reader.packetAt (sitePlace u)
    let B := (A₀).operands u slot packet
    let raw := SignedTaskArena.rawAddress A₀ task.cube.header.profile task.cube.n task.cube.header.d task.cube.header.cap
    let G := wiringWith physical P deployed indexWidth link (k+1) ec fit
    let args := (A₀).unitAddresses slot packet
    let f := G.transferFrame u args.header args.dst
    (deployed).publicWords u=B.bank (core (withDemandBase (task.routeBank (A₀).frame ((ordinary).publicWords u)) (A₀).next)
      origin task.cube.cables task.cube.cells) ∧
    packet.extension=signedProfileExtension task (signedBudgetWords rw exteriorBudget) dir origin task.cube.cables
      task.cube.cells raw u.val rw fresh reserve (Table.size t) o field off ell ∧
    (routingExtension (task.extension raw u.val rw (signedBudgetWords rw exteriorBudget)) dir origin task.cube.cables task.cube.cells 0).val=exteriorBudget ∧
    (dir).teams=B.layout.teams ∧ (dir).processors=B.layout.processors ∧ (dir).literal=B.layout.literal ∧ (dir).link=B.layout.link ∧
    f.dst=(A₀).broadcastBase ∧ f.teams=R+1 := by
  intro slot packet B raw G args f
  refine ⟨?_,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change (reader.siteOperandsWith physical P ordinary sitePlace fit L.header u).bank ((ordinary).publicWords u)=_
    have op := reader.siteOperands_arenaWith physical P ordinary fit
      (fun v => (places v).valuation) (fun v => (places v).entry) (fun v => (places v).totals)
      (fun v => Allocation.fields (pinned v) fresh reserve (Table.size t) o field off ell) L u
    rw [op]
    exact congrArg B.bank (task.ordinary_routed A₀ origin 0 query guesses reader.gates (S.publicWords u))
  · apply reader.deployedFrozenSites_fields
  · exact signedBudgetWords_routed task dir raw u.val rw origin task.cube.cables task.cube.cells exteriorBudget Xfit

end Diagonal

end BorderVNP
end Computability
end OAI
