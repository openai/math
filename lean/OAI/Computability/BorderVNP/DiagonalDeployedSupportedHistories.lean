import OAI.Computability.BorderVNP.DiagonalFrozenSignedDeployment
import OAI.Computability.BorderVNP.DiagonalDeployedFrozenBoots
import OAI.Computability.BorderVNP.DiagonalFrozenSignedInstallation
import OAI.Computability.BorderVNP.DiagonalChosenSupportedHistories

/-! # Physical profile recognition on the deployed frozen sites -/

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
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins RoutingISA.Evaluator RoutingISA.CompactMachine
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype

set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

variable {K : Type} [Field K] {D m : ℕ} [NeZero D] {ι : Type} [Fintype ι] {paid : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField paid aux q k s ord} {chart : AdvisedBranch C}
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r rw pinWidth pc a link ec d : ℕ}
    (reader : ChosenReader chart (R+1) r rw rw rw pinWidth) (physical : UniversalMachine.Program)
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
    (L : Routing.WireLayout (R+1) r link)
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
variable (task : SignedTaskArena.Layout) (exteriorBudget : ℕ)
local notation3 (prettyPrint := false) "gap" => 7*(Directory.Layout.candidates dir)
local notation3 (prettyPrint := false) "fresh" => StartupArena.next arena+gap
local notation3 (prettyPrint := false) "origin" => Allocation.dest fresh reserve (Table.size table) o field
local notation3 (prettyPrint := false) "query" => Fintype.card (Board.Physical (pairedTableParameters (k+1) s) pinWidth rw (paid.Entry ⊕ ι))
local notation3 (prettyPrint := false) "guesses" => Fintype.card (Guess (Fin (pairedTableParameters (k+1) s)) reader.gridRank
  (Nat.clog 2 C.p+1) (Nat.clog 2 C.p))
local notation3 (prettyPrint := false) "ordinary" => SignedTaskArena.withOrdinary S (fun _ => task) arena
  (fun _ => origin) (fun _ => 0) (fun _ => query) (fun _ => guesses) (fun _ => reader.gates)
local notation3 (prettyPrint := false) "routed" => routingExtension (signedBudgetWords rw exteriorBudget)
  dir origin task.cube.cables task.cube.cells
local notation3 (prettyPrint := false) "places" u => reader.frozenTaskPlacement task arena u routed
local notation3 (prettyPrint := false) "pinned" u => CubeHeaderInstall.pinFields (places u).extension
  (Allocation.stop fresh reserve (Table.size table) o field rw) task.cube.header.d (task.cube.n+1)
  (task.cube.h*task.cube.b) task.cube.header.blocks reserve
  (BorderVNP.Cube.Physical.declarationCap task.cube.n task.cube.header.d task.cube.header.blocks task.cube.b task.cube.h task.cube.s)
local notation3 (prettyPrint := false) "first" => freeStartWith physical r 32 64 rw (k+1)

local notation3 (prettyPrint := false) "held" => reader.deployedFrozenSites physical P S fit W pos sites edges ports
  copies bundles headerFactor L table task exteriorBudget
local notation3 (prettyPrint := false) "off" => StartupArena.literal arena/4
local notation3 (prettyPrint := false) "ell" => GeometryAdviceRate.stripeWidth
  (GeometryOutput.packetCount reserve (Table.size table) o field*rw) r
local notation3 (prettyPrint := false) "st" => Allocation.stripe fresh reserve (Table.size table) o field off ell
local notation3 (prettyPrint := false) "exts" u => Allocation.fields (pinned u) fresh reserve (Table.size table) o field off ell
local notation3 (prettyPrint := false) "pack" u => reader.packetAt (ReaderPlacement.inArena arena
  (places u).valuation (places u).entry (places u).totals (exts u))
local notation3 (prettyPrint := false) "strings" => W.seedLiteralMatrix pos (ParseTable.signedLiteralCode ord) sites edges ports
  copies bundles (headerFactor*logWidth r (k+1))

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8000 in
/-- A real bare pre-call return on the deployed signed site determines a unique
original public-history word before any of the shared transfer data are trusted. -/
theorem ChosenReader.deployed_bare_history
    (gateFit : (geometryTable hist nativeOrder fits emit x).size ≤ ceiling)
    (headerWidth : L.header = JointHeader.PositiveFields.width reserve task.cube.n task.cube.header.d
      task.cube.header.cap (R+1) task.dim rw)
    (pin : Fin indexWidth → Bool) (regions : JointRoom dir first a (signedBootStripe first) st)
    (copiesFit : reader.packetBitCount ≤ r) (wordFit : field ≤ rw)
    (endFits : Allocation.stop fresh reserve ceiling o field rw < 2^rw)
    (p : JointHeader.PositiveFields reserve task.cube.n task.cube.header.d task.cube.header.cap (R+1) task.dim rw)
    (wire : HeaderExterior L p.bits) (u : Fin (R+1)) :
    let T := held
    let G := wiringWith physical P T indexWidth link (k+1) ec fit
    let args := fun u : Fin (R+1) => (arena).unitAddresses (adviceOffsetWith physical r 32 64 rw (k+1)) (pack u)
    ∀ B : BootedPinStart SparseExterior.driver G T.publicWords T.registers args pin wire.val u,
      B.start.Prefix task.id → ∃! v, (code v).val=p.profile := by
  intro T G args B prep
  let mac := TeamSiteEvents.macros (w:=rw) (siteLibrary SparseExterior.driver) (nativeClock (k+1))
  have check := reader.frozen_profile_positive_sites physical P ordinary fit (fun u => (places u).valuation)
    (fun u => (places u).entry) (fun u => (places u).totals) (fun u => pinned u) L plan G₀ gridOrder pos W tag
    sites edges ports bottomTable x wr hm widths slots fits emit dir ceiling (signedBootStripe first)
    (fun _ => []) strings p gateFit (p.bits_length.trans headerWidth.symm) wire u pin mac (T.registers u)
    regions copiesFit wordFit endFits
  exact check.1.mp (B.profileOfPrefix prep)

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8000 in
/-- Decode the chosen public history on the deployed signed site table. Its original verifier,
budget word, reserved gates and reader locations are those of this installation. The return
belongs to the supplied booted pin states for this particular live pin. -/
noncomputable def ChosenReader.deployedSupportedPreparations
    (gateFit : (geometryTable hist nativeOrder fits emit x).size ≤ ceiling)
    (headerWidth : L.header = JointHeader.PositiveFields.width reserve task.cube.n task.cube.header.d
      task.cube.header.cap (R+1) task.dim rw)
    (pin : Fin indexWidth → Bool) (regions : JointRoom dir first a (signedBootStripe first) st)
    (copiesFit : reader.packetBitCount ≤ r) (wordFit : field ≤ rw)
    (endFits : Allocation.stop fresh reserve ceiling o field rw < 2^rw)
    (fixed : Routing.Block (R+1)) (hw : 0 < rw) :
    let T := held
    let G := wiringWith physical P T indexWidth link (k+1) ec fit
    let codec := (code).toEmbedding.trans (Function.Embedding.subtype _)
    let args := fun u : Fin (R+1) => (arena).unitAddresses (adviceOffsetWith physical r 32 64 rw (k+1)) (pack u)
    ∀ (ready : ∀ u, (args u).Fitted G u (pack u) (T.publicWords u) (adviceOffsetWith physical r 32 64 rw (k+1)))
      (B : (v : {ext // PositiveExterior G args pin rw ext}) → (u : Fin (R+1)) →
        BootedPinStart SparseExterior.driver G T.publicWords T.registers args pin v.val u),
      BootedPinStart.PreparedHistoryDecoder SparseExterior.driver task.id G T.publicWords T.registers pin L
        headerWidth codec args fixed hw (fun _ => rfl) (fun u => (T.publicWords u 0).val) (fun u => (ready u).physical) B := by
  intro T G codec args ready B
  exact reader.frozenSupportedPreparations physical P ordinary fit (fun u => (places u).valuation)
    (fun u => (places u).entry) (fun u => (places u).totals) (fun u => pinned u) L plan G₀ gridOrder pos W
    tag sites edges ports bottomTable x wr hm widths slots fits emit dir ceiling (signedBootStripe first)
    (fun _ => []) strings SparseExterior.driver task.id gateFit headerWidth pin regions copiesFit wordFit endFits
    args fixed hw (fun _ => rfl) (fun u => (T.publicWords u 0).val) (fun u => (ready u).physical) B

local notation3 (prettyPrint := false) "args₀" => fun u : Fin (R+1) =>
  (arena).unitAddresses (adviceOffsetWith physical r 32 64 rw (k+1)) (pack u)
local notation3 (prettyPrint := false) "sewn" => SewnTape.wiring (regs:=64) (w:=rw) (ec:=ec) (width:=rw+1) physical fit
  ((held).enrichedFree physical P (k+1) ec link) indexWidth
local notation3 (prettyPrint := false) "frame₀" u => (sewn).transferFrame u ((args₀) u).header ((args₀) u).dst

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8000 in
/-- For each live pin, construct the actual decoder on the very family of
booted executions obtained by running the deployed signed site table. The
same witnesses still carry their original word bounds and packet readback. -/
noncomputable def ChosenReader.deployedBootDecoder
    (gateFit : (geometryTable hist nativeOrder fits emit x).size ≤ ceiling)
    (headerWidth : L.header = JointHeader.PositiveFields.width reserve task.cube.n task.cube.header.d
      task.cube.header.cap (R+1) task.dim rw)
    (fixed : Routing.Block (R+1)) (regions : JointRoom dir first a (signedBootStripe first) st)
    (copiesFit : reader.packetBitCount ≤ r) (wordFit : field ≤ rw)
    (endFits : Allocation.stop fresh reserve ceiling o field rw < 2^rw)
    (memFit : (arena).next < 2^rw) (hw : 0 < rw) (three : 2 < R+1) (hdr : 0 < L.header) (cap : L.header ≤ r*link)
    (clock : ∀ u, packetUnitBudget ((args₀) u).advice.count rw (frame₀ u)
      ((sewn).pinLayout u ((args₀) u).ibase ((args₀) u).hbase ((args₀) u).starbase) ≤ S.limit.val) :
    let chosen := reader.deployedFrozenSites_boots physical P S fit W pos sites edges ports copies bundles headerFactor L
      table task exteriorBudget fixed regions copiesFit memFit hw three hdr cap clock
    let codec := (code).toEmbedding.trans (Function.Embedding.subtype _)
    ∀ pin : Fin indexWidth → Bool,
      BootedPinStart.PreparedHistoryDecoder SparseExterior.driver task.id sewn (held).publicWords (held).registers pin L
        headerWidth codec args₀ fixed hw (fun _ => rfl) (fun u => ((held).publicWords u 0).val)
        (fun u => ((chosen.1 u).1).physical) (chosen.2.choose pin) := by
  intro chosen codec pin
  exact reader.deployedSupportedPreparations physical P S fit W pos sites edges ports plan L x bottomTable wr hm widths
    slots fits emit U deg task exteriorBudget gateFit headerWidth pin regions copiesFit wordFit endFits fixed hw
    (fun u => (chosen.1 u).1) (chosen.2.choose pin)

set_option maxHeartbeats 3000000 in
/-- The actual deployed signed memory uses this one reserved public table. Its
valid words are exactly the codes of original packed histories, and its
private verifier still computes the indexed polynomial on every column. -/
theorem ChosenReader.deployedFrozenInstallation (gateFit : (geometryTable hist nativeOrder fits emit x).size ≤ ceiling) :
    (table).size = ceiling ∧
    (∀ raw : Fin reserve → Bool, GeometryOutput.validBit table (Sum.elim raw Fin.elim0)=true ↔
      ∃! q : (packHistory seed (M).epoch T).Index, (code q).val=raw) ∧
    (∀ q : (packHistory seed (M).epoch T).Index, nativeTableWords table (code q).val = fun i =>
      ParseBatchSort.value (fun j => emit.eval (Sum.elim (Sum.elim x (code q).val)
        (output steps T le_rfl (repeatLeaf (fan schedule) input T) x ((M).packBits seed T le_rfl q))) (i,j))) ∧
    ∀ (F Gadget : Type) [CommRing F] (values : Gadget → F) (u : Fin (R+1)) (pin : Fin indexWidth → Bool)
      (wire : Exterior R r link → Bool),
      let installed := wiringWith physical P held indexWidth link (k+1) ec fit
      (∑ z : W.Hidden pos, (W.seedGrid pos).value
        (fun v b g => interpret values (W.seedTags pos z v b g)) (fun i _ => publicBits installed u pin wire i)) =
      MvPolynomial.map (Int.castRingHom F) (∑ inside : Wires.Edge r 64 rw ec (rw+1) → Bool,
        ∏ i, labelQuery (Fin.last k) (0 : ParseTable.State (Fin (k+1) × Bool) s) (installed.word pin wire inside u i)) := by
  refine ⟨(geometryTable hist nativeOrder fits emit x).reserve_size ceiling gateFit,?_,?_,?_⟩
  · exact plan.frozenProfile_valid G₀ gridOrder pos W tag sites edges ports bottomTable x wr hm widths slots fits emit ceiling
  · exact plan.frozenProfile_words G₀ gridOrder pos W tag sites edges ports bottomTable x wr hm widths slots fits emit ceiling
  · intro F Gadget _ values u pin wire
    exact reader.frozenSignedData_query physical P ordinary fit W pos sites edges ports copies bundles headerFactor
      (fun i => (places i).valuation) (fun i => (places i).entry) (fun i => (places i).totals) (fun i => pinned i)
      L table (signedBootStripe first) (fun _ => []) gap values u pin wire

end Diagonal

end BorderVNP
end Computability
end OAI
