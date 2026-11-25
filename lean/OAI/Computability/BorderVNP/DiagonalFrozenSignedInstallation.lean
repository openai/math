import OAI.Computability.BorderVNP.DiagonalFrozenSignedLiteral
import OAI.Computability.BorderVNP.PackedFrozenProfileTable
import OAI.Computability.BorderVNP.GeometryGateCeiling

/-! # The single signed geometry and private-data installation fixed before the input pins -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Branch Cover Packing Packing.DeckGrid CellEntries ExternalSew ExternalSew.RowTrace
open VPVNP BurstRAM VerifierNetwork ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open TeamContraction TeamContraction.ProcessorSlots RoutingISA RoutingISA.Pins RoutingISA.Transmission
open GeometryAdvice GeometryFrameEncoding PackedHistoryCircuit TeamScales MvPolynomial
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule EnrichedOuter
open Shortening Shortening.Adaptive Packing.Inherited
open BorderVNP.Epoch BorderVNP.Epoch.Round
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype

set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

variable {K : Type} [Field K] {D m : ℕ} [NeZero D] {ι : Type} [Fintype ι] {paid : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField paid aux q k s ord} {chart : AdvisedBranch C}
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r mult tally rw pinWidth pc a link ec d : ℕ}
    (reader : ChosenReader chart (R+1) r mult tally rw pinWidth) (physical : UniversalMachine.Program)
    (P : TeamOpcode.Program pc 64 32 8) (S : SiteData R r 64 32 rw a)
    (fit : fitsWith physical 64 32 r rw a R link (k+1) ec)
local notation "indexWidth" => (pairedTableParameters (k+1) s+2)*pinWidth
local notation "tail" => setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a)

local notation "axes" => Fintype.card (Epoch.Cube D)
variable {gridOrder : Fin (GridHosts.tileCount (Fintype.card (Epoch.Cube D)) d) ≃ (Fin (Fintype.card (Epoch.Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1)
        (k:=k) (a:=setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a))
        physical fit ((pairedTableParameters (k+1) s+2)*pinWidth)) (Fin.last k) D (Fintype.card (Epoch.Cube D)) d gridOrder
        (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (pos : (Fin (Fintype.card (Epoch.Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {ns ne np : ℕ}
    (sites : (W.routedFine pos).Site ↪ Fin ns) (edges : (W.routedFine pos).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1)
      (k:=k) (a:=setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a)) physical fit
      ((pairedTableParameters (k+1) s+2)*pinWidth))) ↪ Fin np)
    {T copies headerFactor Q : ℕ} {schedule : PackedHistoryCircuit.Normalized.SiteSchedule paid}
    (plan : PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan schedule (k+1) r d T copies headerFactor Q)
    (valuation entry totals : Fin (R+1) → ℕ) (old : Fin (R+1) → Fin 81 → Word rw)
    (L : Routing.WireLayout (R+1) r link) (boot : Stripe) (bootBits : Fin (R+1) → List Bool)
    {σ : Type} [Fintype σ] (x : σ → Bool)
local notation3 (prettyPrint := false) "G₀" => tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw)
  (e:=ec) (width:=rw+1) (k:=k) (a:=tail) physical fit indexWidth
variable (bottomTable : (seedBundle (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec)
      (width:=rw+1) (k:=k) (a:=setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a)) physical
      fit ((pairedTableParameters (k+1) s+2)*pinWidth)) (Fintype.card (Epoch.Cube D)) d gridOrder pos copies).Tables K)
    (wr : WidthRanges schedule (d+1) T (60*logWidth r (k+1))) (hm : 0 < «m»)
    (widths : ℕ → ℕ) (slots : ∀ j, Machine.Guess schedule (d+1) (fun _ _ => 60*logWidth r (k+1)) j ≃ Fin (widths j))
    {reserve o field : ℕ} (fits : broadcastWidth (fan schedule) widths T ≤ reserve)
    (emit : Frame ((σ ⊕ Fin reserve) ⊕ Packing.Inherited.FrozenTape.ProgramSchemas.outerPins schedule (d+1)
      (60*logWidth r (k+1)) (Boundary.seedFormat (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw)
        (e:=ec) (width:=rw+1) (k:=k) (a:=setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a)) physical
        fit ((pairedTableParameters (k+1) s+2)*pinWidth)) gridOrder pos copies) T) (Fin o × Fin field))
    (U deg : ℕ)
local notation3 (prettyPrint := false) "tag" => ParseTable.signedLiteralCode (s:=s) ord
local notation "tiles" => GridHosts.tileCount (Fintype.card (Epoch.Cube D)) d
local notation "bundles" => (fan schedule)^T
local notation "blockSize" => GridHosts.inputBlockWidth r (k+1) axes d
local notation "dB" => seedDescriptionWidth (k+1) r axes d (headerFactor*logWidth r (k+1))
  (BottomGridBank.bodyBudget (seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))))
local notation3 (prettyPrint := false) "arena" => reader.startupArenaWith (n:=k+1) (reg:=64) physical a link L.header
local notation3 (prettyPrint := false) "dir" => freeDirectory R r (arena).literal link tiles blockSize (bundles*tiles) dB
local notation3 (prettyPrint := false) "ringHeader" => WorkWords.grouped (CoverScale.sites (Epoch.Cube D) (d+1)) (copies*blockSize)
local notation "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation3 (prettyPrint := false) "fmt" => Boundary.seedFormat G₀ gridOrder pos copies
local notation3 (prettyPrint := false) "input" => plan.frozenStart G₀ gridOrder pos σ
local notation3 (prettyPrint := false) "geo" => (plan.execute G₀ gridOrder pos σ).choose
local notation3 (prettyPrint := false) "seed" => plan.frozenLeaf G₀ gridOrder pos W tag sites edges ports bottomTable x
local notation3 (prettyPrint := false) "M" => plan.compiled.machine
local notation3 (prettyPrint := false) "steps" => plan.compiled.tapeSteps fmt ringHeader key wr hm
local notation3 (prettyPrint := false) "hist" => compile steps T le_rfl (repeatLeaf (fan schedule) input T)
local notation3 (prettyPrint := false) "nativeOrder" => broadcastOrder (fan schedule) widths slots T
local notation3 (prettyPrint := false) "ceiling" => geometryGateCeiling U deg r (k+1)
local notation3 (prettyPrint := false) "table" => reservedGeometryTable hist nativeOrder fits emit x ceiling
local notation3 (prettyPrint := false) "code" => (M).nativeCode seed geo x rfl widths slots fits
local notation3 (prettyPrint := false) "data" => reader.frozenSignedData physical P S fit W pos sites edges ports copies bundles
  headerFactor valuation entry totals old L table boot bootBits (7*(dir).candidates)

set_option maxHeartbeats 1800000 in
/-- The concrete table and source slots are fixed together before the live index,
raw common profile, substituted pin and exterior are assigned. The original
weighted polynomial query, complete public guard, fixed gate count and emitted
packet words hold on this single installation. -/
theorem ChosenReader.frozenInstallation (gateFit : (geometryTable hist nativeOrder fits emit x).size ≤ ceiling) :
    (table).size = ceiling ∧
    (∀ raw : Fin reserve → Bool, GeometryOutput.validBit table (Sum.elim raw Fin.elim0)=true ↔
      ∃! q : (packHistory seed (M).epoch T).Index, (code q).val=raw) ∧
    (∀ q : (packHistory seed (M).epoch T).Index, nativeTableWords table (code q).val = fun i =>
      ParseBatchSort.value (fun j => emit.eval (Sum.elim (Sum.elim x (code q).val)
        (output steps T le_rfl (repeatLeaf (fan schedule) input T) x ((M).packBits seed T le_rfl q))) (i,j))) ∧
    ∀ (F Gadget : Type) [CommRing F] (values : Gadget → F) (u : Fin (R+1)) (pin : Fin indexWidth → Bool)
      (wire : Exterior R r link → Bool),
      let installed := wiringWith physical P data indexWidth link (k+1) ec fit
      (∑ z : W.Hidden pos, (W.seedGrid pos).value
        (fun v b g => interpret values (W.seedTags pos z v b g)) (fun i _ => publicBits installed u pin wire i)) =
      MvPolynomial.map (Int.castRingHom F) (∑ inside : Wires.Edge r 64 rw ec (rw+1) → Bool,
        ∏ i, labelQuery (Fin.last k) (0 : ParseTable.State (Fin (k+1) × Bool) s) (installed.word pin wire inside u i)) := by
  refine ⟨(geometryTable hist nativeOrder fits emit x).reserve_size ceiling gateFit,?_,?_,?_⟩
  · exact plan.frozenProfile_valid G₀ gridOrder pos W tag sites edges ports bottomTable x wr hm widths slots fits emit ceiling
  · exact plan.frozenProfile_words G₀ gridOrder pos W tag sites edges ports bottomTable x wr hm widths slots fits emit ceiling
  · intro F Gadget _ values u pin wire
    exact reader.frozenSignedData_query physical P S fit W pos sites edges ports copies bundles headerFactor valuation
      entry totals old L table boot bootBits (7*(dir).candidates) values u pin wire

section InstalledBoot

open RoutingISA.Evaluator JointHeader BorderVNP.Cube RoutingISA.CompactMachine

variable (task : Fin (R+1) → SignedTaskArena.Layout) (rawBase teamBase totalBase : Fin (R+1) → ℕ)
    (cubeD cubeN cubeBlocks box lanes symbols : ℕ)

local notation3 (prettyPrint := false) "installedGap" => 7*(dir).candidates
local notation3 (prettyPrint := false) "fresh" => StartupArena.next arena+installedGap
local notation3 (prettyPrint := false) "off" => StartupArena.literal arena/4
local notation3 (prettyPrint := false) "ell" => GeometryAdviceRate.stripeWidth
  (GeometryOutput.packetCount reserve (Table.size table) o field*rw) r
local notation3 (prettyPrint := false) "st" => Allocation.stripe fresh reserve (Table.size table) o field off ell
local notation3 (prettyPrint := false) "signedOld" u => (task u).extension (rawBase u) (teamBase u) (totalBase u) (old u)
local notation3 (prettyPrint := false) "imageOld" => fun u : Fin (R+1) => CubeHeaderInstall.pinFields (signedOld u)
  (Allocation.stop fresh reserve (Table.size table) o field rw) cubeD (cubeN+1) (lanes*box) cubeBlocks reserve
  (Physical.declarationCap cubeN cubeD cubeBlocks box lanes symbols)
local notation3 (prettyPrint := false) "overlay₀" v => CubeHeaderInstall.jointFields v fresh reserve (Table.size table) o field
  off ell cubeD cubeN cubeBlocks box lanes symbols
local notation3 (prettyPrint := false) "signedExt" => fun u : Fin (R+1) => overlay₀ (signedOld u)
local notation3 (prettyPrint := false) "signedPlace" => fun u : Fin (R+1) =>
  ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (signedExt u)
local notation3 (prettyPrint := false) "T₀" => reader.frozenSignedData physical P S fit W pos sites edges ports copies bundles
  headerFactor valuation entry totals imageOld L table boot bootBits installedGap
local notation3 (prettyPrint := false) "geomBits" => fun _ : Fin (R+1) =>
  GeometryAdvice.serialized (GeometryAdvice.packet (w:=rw) fresh (Allocation.packed fresh reserve (Table.size table) o field rw)
    table (fun i => StartupArena.broadcastBase arena+1+Fin.val i))
local notation3 (prettyPrint := false) "strings" => W.seedLiteralMatrix pos (ParseTable.signedLiteralCode ord) sites edges ports
  copies bundles (headerFactor*logWidth r (k+1))
local notation3 (prettyPrint := false) "adOff" => adviceOffsetWith physical r 32 64 rw (k+1)
local notation3 (prettyPrint := false) "first" => freeStartWith physical r 32 64 rw (k+1)

set_option maxHeartbeats 2600000 in
/-- Select the physical boot for every live pin from one frozen installation.
The shortened public profile, original private W, all signed and cube fields,
and the reserved reference packet therefore agree on the same sewn wiring. -/
theorem ChosenReader.frozenInstallation_boots (fixed : Routing.Block (R+1))
    (regions : JointRoom dir first a boot st) (copyRoom : reader.packetBitCount ≤ r)
    (memFit : (arena).next < 2^rw) (hw : 0<rw) :
    let installed := T₀
    let sewn := SewnTape.wiring (regs:=64) (w:=rw) (ec:=ec) (width:=rw+1) physical fit
      (installed.enrichedFree physical P (k+1) ec link) indexWidth
    let packets := fun u : Fin (R+1) => reader.packetAt (signedPlace u)
    let args := fun u => (arena).unitAddresses adOff (packets u)
    let frame := fun u => sewn.transferFrame u (args u).header (args u).dst
    (∀ u, (args u).Fitted sewn u (packets u) (installed.publicWords u) adOff ∧
      packetUnitBudget (args u).advice.count rw (frame u)
        (sewn.pinLayout u (args u).ibase (args u).hbase (args u).starbase) ≤ installed.limit.val) →
    ∃ B : (pin : Fin indexWidth → Bool) → (x : {z // PositiveExterior sewn args pin rw z}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver sewn installed.publicWords installed.registers args pin x.val u,
    ∀ pin x u, let ad := args u
      let F := sewn.processorFields u pin x.val ad.ibase ad.hbase ad.starbase
      let pub := installed.publicWords u
      let hdr := observed L x.val fixed
      let mem := (B pin x u).memory
      (B pin x u).used ≤ installed.limit.val ∧ BootHeaderState F (frame u) ad.advice (packets u) pub hdr (B pin x u).out mem ∧
        JointImage dir first a boot st (bootBits u) (geomBits u) strings u.val F ∧
        LocalRow.BootPins pub (frame u) (signedExt u) hdr mem ∧
        ∀ j : Fin 81, mem ((pub 0).val+31+j.val) = (task u).extension (rawBase u) (teamBase u) (totalBase u)
          (overlay₀ (old u)) j := by
  intro installed sewn packets args frame ready
  let runs := reader.frozenSignedBoot physical P S fit W pos sites edges ports copies bundles headerFactor
    valuation entry totals old L table boot bootBits installedGap task rawBase teamBase totalBase cubeD cubeN cubeBlocks box
    lanes symbols fixed regions copyRoom memFit hw ready
  exact ⟨fun pin => (runs pin).choose,fun pin => (runs pin).choose_spec⟩

end InstalledBoot

end Diagonal

end BorderVNP
end Computability
end OAI
