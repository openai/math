import OAI.Computability.BorderVNP.DiagonalFrozenSignedDeployment

/-! # The actual signed verifier body at its receiving team -/

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

set_option quotPrecheck false
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

local notation "H₀" => headerFactor*logWidth r (k+1)
local notation "bodyCap" => BottomGridBank.bodyBudget capacity
local notation "off" => (A₀).literal/4
local notation "ell" => GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve (Table.size t) o field*rw) r
local notation "st" => Allocation.stripe fresh reserve (Table.size t) o field off ell
local notation3 (prettyPrint := false) "installed" => reader.deployedFrozenSites physical P S fit W pos sites edges ports
  copies bundles headerFactor L t task exteriorBudget
local notation3 (prettyPrint := false) "wired" => wiringWith physical P installed indexWidth link (k+1) ec fit
local notation3 (prettyPrint := false) "factors" => W.seedLiteralFactors pos (ParseTable.signedLiteralCode ord)
  sites edges ports copies bundles

open CellPacketGeometry.History.Native CellSparse.Packet Packing.Inherited Packing.CellAddresses
open Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.BottomReports DiagonalTallyCellReports

variable {siteCap edgeCap portCap levels keyWidth liveCount gx : ℕ} {Port X O : Type}
    [Fintype Port] [Fintype X] {pw : Port → ℕ}
    (N : Network D Port pw) (cell : N.Site → Fin task.cube.cells) (state : N.Site → Site)
    (sid : N.Site ↪ Fin siteCap) (edgeID : N.Edge ↪ Fin edgeCap) (portID : Port ↪ Fin portCap)
    (F : Fields siteCap edgeCap portCap task.cube.cells levels keyWidth rw X) (x : X → Bool)
    (boxes : Fin siteCap → List (Source.Box O)) (idRow : Fin (bundles*GridHosts.tileCount axes d) → Fin siteCap)
    (host : Fin (bundles*GridHosts.tileCount axes d) → N.Site) (live : Fin liveCount → Port)
    (digits : ℕ) (before placed : ℕ → ℕ)
local notation3 (prettyPrint := false) "pl" => RoutingOutputs.privateLayout (A₀).frame origin edgeCap task.cube.cells
  (bundles*tiles) desc ((k+1)^2)
local notation3 (prettyPrint := false) "sourceWord" j => ParseBatchSort.value (fun bit =>
  (SignedFields.frame F boxes idRow task.cube.cellBank task.cube.cellStride ((k+1)^2) desc gx digits).eval x (.inr j,bit))

/-- On the installed signed reader, every occupied report entry authenticates
the meaningful header and body bytes of the original verifier at the numeric
address in its emitted descriptor. This is a statement on the delivered
team history, prior to any private call or passing test. -/
theorem ChosenReader.deployedFrozenSites_originalBody (pin : Fin indexWidth → Bool) (wire : Exterior R r link → Bool)
    (lp : ℕ → ℕ × ℕ) (owner : ℕ → Fin (R+1)) (runs : Fin (R+1) → TeamHistory rw) (ib hb sb : Fin (R+1) → ℕ)
    (represented : Represents N cell (fun v => (state v).size) sid edgeID portID F x)
    (codes : ∀ c, (F.cells c).val=c.val)
    (sizeFit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c<2^rw)
    (hostRows : ∀ j, idRow j = sid (host j))
    (picture : RoutingOutputs.Image F (sid ∘ host) (portID ∘ live) x origin before)
    (placement : (pl).Image before (bundles*tiles) placed) (placeFit : (pl).Fits rw before)
    (delivery : ReturnedDelivery wired pin wire L dir (Directory.ISA.placement placed (pl).raw) lp owner task.cube.cellBank task.cube.cellStride runs
      (fun u => Wiring.pinLayout wired u (ib u) (hb u) (sb u)))
    (room : JointRoom dir (freeStartWith physical r 32 64 rw (k+1)) a (signedBootStripe first) st)
    (tailPos : 0 < (dir).literal/2) (short : desc ≤ (dir).literal/2)
    (totalPositions : (bundles*tiles)*desc ≤ (R+1)*r*((dir).literal/2))
    (j : Fin (bundles*tiles))
    (address : CellPacketGeometry.History.opaquePointer (fun c => task.cube.cellBank+c*task.cube.cellStride) (fun c => before ((pl).supplied+c))
      ((pl).owner before) ((k+1)^2) desc j < 2^rw)
    (layout : ReportLayout) (headerWidth : layout.fieldWidth=H₀) (bodyWidth : layout.bodyCap=bodyCap)
    (b : ReportBundle) (siteSlot : b.header.siteSlot = sourceWord j)
    (body : b.factors = factors j)
    (sidecar : b.positions = W.seedPositions pos (ParseTable.signedLiteralCode ord) sites edges ports
      (gridOrder (finProdFinEquiv.symm j).2)) :
    CellSparse.Packet.Source.Delivered (description:=desc) (readings (runs (owner (cell (host j)).val)).history.val.2.2)
      (sourceWord j) H₀ (factors j) := by
  have receipt := reader.frozenSignedData_reportReceipt physical P ordinary fit W pos sites edges ports copies bundles headerFactor
    (fun u => (places u).valuation) (fun u => (places u).entry) (fun u => (places u).totals)
    (fun u => pinned u) L t (signedBootStripe first) (fun _ => []) gap N cell state sid edgeID portID F x boxes idRow
    host live (A₀).frame origin task.cube.cellBank task.cube.cellStride ((k+1)^2) digits before placed
    pin wire lp owner runs ib hb sb represented codes sizeFit hostRows picture placement placeFit delivery room tailPos short
    totalPositions j address layout headerWidth bodyWidth b siteSlot body sidecar
  intro bit meaningful
  have actual := receipt bit
  rw [siteSlot,body,headerWidth,bodyWidth] at actual
  have bound : (CellSparse.Packet.Source.boxBody (factors j)).length ≤ bodyCap :=
    W.seedBody_room pos (ParseTable.signedLiteralCode ord) sites edges ports _ _ _
  simp only [CellSparse.Packet.Source.siteData,List.length_append,List.length_ofFn] at meaningful
  simpa only [CellSparse.Packet.Source.siteWithTally,ite_eq_left (by omega : bit.val<H₀+bodyCap)] using actual

end Diagonal

end BorderVNP
end Computability
end OAI
