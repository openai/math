import OAI.Computability.BorderVNP.DiagonalFrozenSignedTask
import OAI.Computability.BorderVNP.DiagonalFrozenSignedLiteral
import OAI.Computability.BorderVNP.DiagonalSignedGeometryPacket
import OAI.Computability.BorderVNP.DiagonalSignedDeploymentBase
import OAI.Computability.BorderVNP.DiagonalSignedProfilePlacement

/-! # One installed signed site table for all exterior assignments and pins -/

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

/-- Word zero of the previous extended header carries the exterior traffic limit
that each team's integral scheduling guard actually tests. -/
def signedBudgetWords (w X : ℕ) (j : Fin 81) : Word w :=
  if j=0 then TeamTapeInputEmit.word w X else 0

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

/-- Install the actual original verifier, reserved gate table and seven-word demand stream.
The task's own scalar, valuation and result banks determine every reader address.
One copy of this site table serves every pin and every public profile at this length. -/
noncomputable def ChosenReader.deployedFrozenSites : SiteData R r 64 32 rw a :=
  reader.frozenSignedData physical P ordinary fit W pos sites edges ports copies bundles headerFactor
    (fun u => (places u).valuation) (fun u => (places u).entry) (fun u => (places u).totals)
    (fun u => pinned u) L t (signedBootStripe first) (fun _ => []) gap

/-- A different per-history route layout with the same fixed broadcast length gives
the same deployed site table, ordinary operands, reference positions and program. -/
theorem ChosenReader.deployedFrozenSites_header (later : Routing.WireLayout (R+1) r link) (same : L.header=later.header) :
    reader.deployedFrozenSites physical P S fit W pos sites edges ports copies bundles headerFactor L t task exteriorBudget =
    reader.deployedFrozenSites physical P S fit W pos sites edges ports copies bundles headerFactor later t task exteriorBudget := by
  unfold ChosenReader.deployedFrozenSites
  cases L
  cases later
  cases same
  rfl

/-- With all three real overlays the transmitted extended frame is the signed
routing publisher's own full array, including the descriptor, count and cube fields. -/
theorem ChosenReader.deployedFrozenSites_fields (u : Fin (R+1)) :
    let off := (A₀).literal/4
    let ell := GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve (Table.size t) o field*rw) r
    let raw := SignedTaskArena.rawAddress A₀ task.cube.header.profile task.cube.n task.cube.header.d task.cube.header.cap
    Allocation.fields (pinned u) fresh reserve (Table.size t) o field off ell =
      signedProfileExtension task (signedBudgetWords rw exteriorBudget) dir origin task.cube.cables task.cube.cells raw u.val rw
        fresh reserve (Table.size t) o field off ell := by
  intro off ell raw
  exact signed_geometry_packet task (signedBudgetWords rw exteriorBudget) dir origin task.cube.cables task.cube.cells raw u.val rw
    fresh reserve (Table.size t) o field off ell

/-- The scheduling guard reads the chosen limit through both the signed and
routing overlays. The processor can represent the entire exterior budget. -/
theorem signedBudgetWords_routed {w : ℕ} (task : SignedTaskArena.Layout) (directory : Directory.Layout)
    (raw team subtotal src cables cells X : ℕ) (fit : X<2^w) :
    (routingExtension (task.extension raw team subtotal (signedBudgetWords w X)) directory src cables cells 0).val = X := by
  change X % 2^w % 2^w = X
  rw [Nat.mod_eq_of_lt fit,Nat.mod_eq_of_lt fit]

end Diagonal

end BorderVNP
end Computability
end OAI
