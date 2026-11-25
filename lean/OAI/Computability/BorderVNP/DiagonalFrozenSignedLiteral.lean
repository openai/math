import OAI.Computability.BorderVNP.DiagonalSignedBootedSites
import OAI.Computability.BorderVNP.PackedSeedLiteralMatrix
import OAI.Computability.BorderVNP.DiagonalEnrichedSiteWiring
import OAI.Computability.BorderVNP.PackedHistoryChosenTableGeometry
import OAI.Computability.BorderVNP.ParseBatchWiredWitnessTape
import OAI.Computability.BorderVNP.CellPacketGeometryChosenReceipt
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsBundle

/-! # Joint installation of the public gate packet and original signed verifier literals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Branch Cover Packing Packing.DeckGrid CellEntries ExternalSew ExternalSew.RowTrace
open VPVNP BurstRAM VerifierNetwork ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open TeamContraction TeamContraction.ProcessorSlots RoutingISA RoutingISA.Pins RoutingISA.Transmission
open GeometryAdvice GeometryFrameEncoding PackedHistoryCircuit TeamScales MvPolynomial
open scoped Classical BigOperators

set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {paid : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField paid aux q k s ord} {chart : AdvisedBranch C}
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r mult tally rw pinWidth pc a link ec axes d : ℕ}
    (reader : ChosenReader chart (R+1) r mult tally rw pinWidth) (physical : UniversalMachine.Program)
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
    (valuation entry totals : Fin (R+1) → ℕ) (old : Fin (R+1) → Fin 81 → Word rw)
    (L : Routing.WireLayout (R+1) r link)
    {reserve o field : ℕ} (t : Table (Fin reserve ⊕ Fin 0) o field)
    (boot : Stripe) (bootBits : Fin (R+1) → List Bool) (gap : ℕ)

local notation "tiles" => GridHosts.tileCount axes d
local notation "boxCap" => seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
local notation "bodyCap" => BottomGridBank.bodyBudget boxCap
local notation "H₀" => headerFactor*logWidth r (k+1)
local notation "dB" => seedDescriptionWidth (k+1) r axes d H₀ bodyCap
local notation3 (prettyPrint := false) "arena" => reader.startupArenaWith (n:=k+1) (reg:=64) physical a link L.header
local notation3 (prettyPrint := false) "fresh" => StartupArena.next arena+gap
local notation3 (prettyPrint := false) "off" => StartupArena.literal arena/4
local notation3 (prettyPrint := false) "ell" => GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve t.size o field*rw) r
local notation3 (prettyPrint := false) "st" => Allocation.stripe fresh reserve t.size o field off ell
local notation3 (prettyPrint := false) "ext" u => Allocation.fields (old u) fresh reserve t.size o field off ell
local notation3 (prettyPrint := false) "place" => fun u : Fin (R+1) =>
  ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (ext u)
local notation3 (prettyPrint := false) "geometryBits" => fun _ : Fin (R+1) =>
  GeometryAdvice.serialized (GeometryAdvice.packet (w:=rw) fresh (Allocation.packed fresh reserve t.size o field rw) t
    (fun i => StartupArena.broadcastBase arena+1+Fin.val i))
local notation3 (prettyPrint := false) "dir" => freeDirectory R r (arena).literal link tiles
  (GridHosts.inputBlockWidth r (k+1) axes d) (bundles*tiles) dB
local notation3 (prettyPrint := false) "strings" => W.seedLiteralMatrix pos (ParseTable.signedLiteralCode ord) sites edges ports
  copies bundles H₀
local notation3 (prettyPrint := false) "data" => reader.startupSitesWith physical P S place fit dir boot st bootBits
  geometryBits strings L.header

/-- One array of literal fields is fixed before the public pin and external wire
assignment. Its gate stripe contains the actual serialized fixed-address table.
The remaining field carries precisely the routed verifier's own private codes. -/
noncomputable def ChosenReader.frozenSignedData : SiteData R r 64 32 rw a := data

/-- A later choice of wire layout with the same broadcast length uses
exactly the same fixed public gate and private verifier literals. -/
theorem ChosenReader.frozenSignedData_header (L' : Routing.WireLayout (R+1) r link) (same : L.header=L'.header) :
    reader.frozenSignedData physical P S fit W pos sites edges ports copies bundles headerFactor valuation entry totals
      old L t boot bootBits gap =
    reader.frozenSignedData physical P S fit W pos sites edges ports copies bundles headerFactor valuation entry totals
      old L' t boot bootBits gap := by
  unfold ChosenReader.frozenSignedData
  rw [same]

/-- The private source used to install the descriptions, with its actual signed
parameter numbers, remains the verifier of the coefficient query after this
specific joint installation. This holds simultaneously for every pin, exterior,
team and scalar specialization, including zero entries. -/
theorem ChosenReader.frozenSignedData_query {F Gadget : Type} [CommRing F]
    (values : Gadget → F) (u : Fin (R+1)) (pin : Fin indexWidth → Bool)
    (wire : Exterior R r link → Bool) :
    let installed := wiringWith physical P data indexWidth link (k+1) ec fit
    (∑ z : W.Hidden pos, (W.seedGrid pos).value
      (fun v b g => interpret values (W.seedTags pos z v b g)) (fun i _ => publicBits installed u pin wire i)) =
    MvPolynomial.map (Int.castRingHom F) (∑ inside : Wires.Edge r 64 rw ec (rw+1) → Bool,
      ∏ i, labelQuery (Fin.last k) (0 : ParseTable.State (Fin (k+1) × Bool) s) (installed.word pin wire inside u i)) := by
  exact WiredWitness.tape_seed_value (D:=D) (q:=axes) (depth:=d) (R:=R) (r:=r) (pins:=indexWidth)
    (link:=link) (k:=k) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1) (a:=tail) (order:=gridOrder)
    (s:=s) (Gadget:=Gadget) (E:=F) physical fit W pos values ((data).enrichedFree physical P (k+1) ec link) u pin wire

local notation3 (prettyPrint := false) "wired" => wiringWith physical P data indexWidth link (k+1) ec fit
local notation3 (prettyPrint := false) "base" => S.withOperands (reader.siteOperandsWith physical P S place fit L.header)
local notation3 (prettyPrint := false) "packets" => fun u : Fin (R+1) => reader.packetAt (place u)
local notation3 (prettyPrint := false) "factors" => W.seedLiteralFactors pos (ParseTable.signedLiteralCode ord) sites edges ports copies bundles

/-- Every completed authenticated route on the installed literal delivers the
original verifier body and its own report-sidecar fields at the actual assigned
receiver, irrespective of later cell checks or scalar values. -/
theorem ChosenReader.frozenSignedData_received (pin : Fin indexWidth → Bool) (wire : Exterior R r link → Bool)
    (pp lp : ℕ → ℕ × ℕ) (owner : ℕ → Fin (R+1)) (origin stride : ℕ) (runs : Fin (R+1) → TeamHistory rw)
    (ib hb sb : Fin (R+1) → ℕ) (delivery : ReturnedDelivery wired pin wire L dir pp lp owner origin stride runs
      (fun u => Wiring.pinLayout wired u (ib u) (hb u) (sb u)))
    (room : JointRoom dir (freeStartWith physical r 32 64 rw (k+1)) a boot st)
    (tailPos : 0 < (dir).literal/2) (short : dB ≤ (dir).literal/2)
    (capacity : (bundles*tiles)*dB ≤ (R+1)*r*((dir).literal/2))
    (rep : (k+1+s+2)^24 ≤ r) (hf : 8 ≤ headerFactor) (small : boxCap ≤ k+1) (len : dB ≤ k+1)
    (j : Fin (bundles*tiles)) :
    let c := gridOrder (finProdFinEquiv.symm j).2
    let ps := W.seedPositions pos (ParseTable.signedLiteralCode ord) sites edges ports c
    let slot := origin+(pp j).1*stride+(pp j).2
    let mem := (runs (owner (pp j).1)).history.val.2.2
    (RoutingISA.CellPacket.Chunk.box slot H₀ (CellSparse.Packet.Source.boxBody (factors j))).Stored (fun a => (mem a).val) ∧
      DiagonalTallyBits.WordsAt mem (slot+H₀+bodyCap) (TallySidecar.words H₀ ps) ∧
      (TallySidecar.words H₀ ps).map TapeWord.value = TallySidecar.fields ps := by
  intro c ps slot mem
  have stateFit := seed_states_le (k+1) s r rep
  have hr : 1 ≤ r := (Nat.one_le_pow 24 _ (by omega)).trans rep
  have hg : Fintype.card (Fin (k+1) × Bool) + s + 1 ≤ r := by
    simpa only [ParseTable.State,Fintype.card_fin] using stateFit
  refine W.seedLiteralMatrix_decoded pos (ParseTable.signedLiteralCode ord) sites edges ports copies
    j mem slot hr hg hf small len (ParseTable.signedLiteralCode_bound ord) ?_
  intro bit
  have heard := joint_private_received_with physical P base dir packets boot st bootBits geometryBits strings fit
    pin wire L pp lp owner origin stride runs ib hb sb delivery room rfl tailPos short capacity j bit
  exact (congrArg Fin.val heard).trans (Nat.mod_eq_of_lt ((Bool.toNat_lt _).trans_le
    (Nat.one_lt_pow delivery.word.ne' (by decide : 1 < 2))))

open CellPacketGeometry.History.Native CellSparse.Packet Packing.Inherited Packing.CellAddresses
open Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.BottomReports DiagonalTallyCellReports

variable {siteCap edgeCap portCap cellCount levels keyWidth liveCount gx : ℕ} {Port X O : Type}
    [Fintype Port] [Fintype X] {pw : Port → ℕ}
    (N : Network D Port pw) (cell : N.Site → Fin cellCount) (state : N.Site → Site)
    (sid : N.Site ↪ Fin siteCap) (edgeID : N.Edge ↪ Fin edgeCap) (portID : Port ↪ Fin portCap)
    (F : Fields siteCap edgeCap portCap cellCount levels keyWidth rw X) (x : X → Bool)
    (boxes : Fin siteCap → List (Source.Box O)) (idRow : Fin (bundles*GridHosts.tileCount axes d) → Fin siteCap)
    (host : Fin (bundles*GridHosts.tileCount axes d) → N.Site) (live : Fin liveCount → Port)
    (frame dest sourceBase stride reportGap digits : ℕ) (before placed : ℕ → ℕ)
local notation3 (prettyPrint := false) "pl" => RoutingOutputs.privateLayout frame dest edgeCap cellCount
  (bundles*tiles) dB reportGap
local notation3 (prettyPrint := false) "sourceWord" j => ParseBatchSort.value (fun bit =>
  (SignedFields.frame F boxes idRow sourceBase stride reportGap dB gx digits).eval x (.inr j,bit))

/-- The actual signed pointer operand reaches every original private bit of
this report bundle at its assigned team. Its body and sidecar are authenticated
before, and independently of, all reported use choices. -/
theorem ChosenReader.frozenSignedData_reportReceipt (pin : Fin indexWidth → Bool) (wire : Exterior R r link → Bool)
    (lp : ℕ → ℕ × ℕ) (owner : ℕ → Fin (R+1)) (runs : Fin (R+1) → TeamHistory rw) (ib hb sb : Fin (R+1) → ℕ)
    (represented : Represents N cell (fun v => (state v).size) sid edgeID portID F x)
    (codes : ∀ c, (F.cells c).val=c.val)
    (sizeFit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c<2^rw)
    (hostRows : ∀ j, idRow j = sid (host j))
    (picture : RoutingOutputs.Image F (sid ∘ host) (portID ∘ live) x dest before)
    (placement : (pl).Image before (bundles*tiles) placed) (placeFit : (pl).Fits rw before)
    (delivery : ReturnedDelivery wired pin wire L dir (Directory.ISA.placement placed (pl).raw) lp owner sourceBase stride runs
      (fun u => Wiring.pinLayout wired u (ib u) (hb u) (sb u)))
    (room : JointRoom dir (freeStartWith physical r 32 64 rw (k+1)) a boot st)
    (tailPos : 0 < (dir).literal/2) (short : dB ≤ (dir).literal/2)
    (capacity : (bundles*tiles)*dB ≤ (R+1)*r*((dir).literal/2))
    (j : Fin (bundles*tiles))
    (address : CellPacketGeometry.History.opaquePointer (fun c => sourceBase+c*stride) (fun c => before ((pl).supplied+c))
      ((pl).owner before) reportGap dB j < 2^rw)
    (layout : ReportLayout) (headerWidth : layout.fieldWidth=H₀) (bodyWidth : layout.bodyCap=bodyCap)
    (b : ReportBundle) (siteSlot : b.header.siteSlot = sourceWord j)
    (body : b.factors = factors j)
    (sidecar : b.positions = W.seedPositions pos (ParseTable.signedLiteralCode ord) sites edges ports
      (gridOrder (finProdFinEquiv.symm j).2)) :
    b.delivered layout dB (readings (runs (owner (cell (host j)).val)).history.val.2.2) := by
  intro bit
  rw [siteSlot,body,sidecar,headerWidth,bodyWidth]
  exact chosen_descriptor_bits physical P base dir packets boot st bootBits geometryBits strings fit pin wire L lp
    owner sourceBase stride runs ib hb sb N cell state sid edgeID portID F x represented codes sizeFit boxes idRow
    host hostRows live frame dest reportGap digits before placed picture placement placeFit delivery room rfl
    tailPos short capacity j address bit

section PhysicalBoot

open RoutingISA.Evaluator JointHeader BorderVNP.Cube RoutingISA.CompactMachine

variable (task : Fin (R+1) → SignedTaskArena.Layout) (rawBase teamBase totalBase : Fin (R+1) → ℕ)
    (cubeD cubeN blocks box lanes symbols : ℕ)
local notation3 (prettyPrint := false) "signedOld" u => (task u).extension (rawBase u) (teamBase u) (totalBase u) (old u)
local notation3 (prettyPrint := false) "imageOld" => fun u : Fin (R+1) => CubeHeaderInstall.pinFields (signedOld u)
  (Allocation.stop fresh reserve (Table.size t) o field rw) cubeD (cubeN+1) (lanes*box) blocks reserve
  (Physical.declarationCap cubeN cubeD blocks box lanes symbols)
local notation3 (prettyPrint := false) "overlay₀" v => CubeHeaderInstall.jointFields v fresh reserve (Table.size t) o field
  off ell cubeD cubeN blocks box lanes symbols
local notation3 (prettyPrint := false) "signedExt" => fun u : Fin (R+1) => overlay₀ (signedOld u)
local notation3 (prettyPrint := false) "signedPlaces" => fun u : Fin (R+1) =>
  ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (signedExt u)
local notation3 (prettyPrint := false) "signedData" => reader.frozenSignedData physical P S fit W pos sites edges ports copies
  bundles headerFactor valuation entry totals imageOld L t boot bootBits gap
local notation3 (prettyPrint := false) "adOff" => adviceOffsetWith physical r 32 64 rw (k+1)
local notation3 (prettyPrint := false) "first" => freeStartWith physical r 32 64 rw (k+1)

set_option maxHeartbeats 2100000 in
/-- The same installed private W literals, public gate table and signed-task
reader fields serve all the live pins. Every positive exterior on the actual
sewn tape has its native timed boot, full 81-word image and delivered source
fields, before any private preparation or route check. -/
theorem ChosenReader.frozenSignedBoot (fixed : Routing.Block (R+1))
    (regions : JointRoom dir first a boot st) (copyRoom : reader.packetBitCount ≤ r)
    (ceiling : (arena).next < 2^rw) (hw : 0<rw) :
    let T := signedData
    let sewn := SewnTape.wiring (regs:=64) (w:=rw) (ec:=ec) (width:=rw+1) physical fit
      (T.enrichedFree physical P (k+1) ec link) indexWidth
    let packet := fun u : Fin (R+1) => reader.packetAt (signedPlaces u)
    let args := fun u => (arena).unitAddresses adOff (packet u)
    let frame := fun u => sewn.transferFrame u (args u).header (args u).dst
    (∀ u, (args u).Fitted sewn u (packet u) (T.publicWords u) adOff ∧
      packetUnitBudget (args u).advice.count rw (frame u) (sewn.pinLayout u (args u).ibase (args u).hbase (args u).starbase) ≤ T.limit.val) →
    ∀ pin : Fin indexWidth → Bool, ∃ B : (x : {z // PositiveExterior sewn args pin rw z}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver sewn T.publicWords T.registers args pin x.val u,
    ∀ x u, let ad := args u
      let F := sewn.processorFields u pin x.val ad.ibase ad.hbase ad.starbase
      let pub := T.publicWords u
      let hdr := observed L x.val fixed
      let m := (B x u).memory
      (B x u).used ≤ T.limit.val ∧ BootHeaderState F (frame u) ad.advice (packet u) pub hdr (B x u).out m ∧
        JointImage dir first a boot st (bootBits u) (geometryBits u) strings u.val F ∧
        LocalRow.BootPins pub (frame u) (signedExt u) hdr m ∧
        ∀ j : Fin 81, m ((pub 0).val+31+j.val) = (task u).extension (rawBase u) (teamBase u) (totalBase u)
          (overlay₀ (old u)) j := by
  intro T sewn packet args frame ready pin
  obtain ⟨B,ok⟩ := reader.booted_positive_sites physical P S fit valuation entry totals signedExt L dir
    boot st bootBits geometryBits strings SparseExterior.driver fixed pin regions copyRoom ceiling hw ready
  refine ⟨B,?_⟩
  intro x u ad F pub hdr mem
  obtain ⟨cost,loaded,fields⟩ := ok x u
  obtain ⟨cube,taskWords⟩ := reader.signedStartup_boot (task u) arena (valuation u) (entry u) (totals u)
    (rawBase u) (teamBase u) (totalBase u) (old u) fresh reserve (Table.size t) o field off ell cubeD cubeN blocks
    box lanes symbols loaded
  rw [(task u).cube_extension_signed (rawBase u) (teamBase u) (totalBase u) (old u)] at cube
  exact ⟨cost,loaded,fields,cube,taskWords⟩

end PhysicalBoot

end Diagonal

end BorderVNP
end Computability
end OAI
