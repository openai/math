import OAI.Computability.BorderVNP.DiagonalFrozenSignedLiteral
import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart
import OAI.Computability.BorderVNP.DiagonalNativeTimedArena

/-! # Measured operands at the chosen signed startup -/

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

/-- The fixed gate stripe, arena decoder and original signed descriptions
that the booted geometry semantics reads are precisely the data installed at
this site. The identification holds for all initial extended-frame words. -/
theorem ChosenReader.frozenSignedData_startup :
    reader.frozenSignedData physical P S fit W pos sites edges ports copies bundles headerFactor valuation entry totals
      old L t boot bootBits gap =
      reader.startupSitesWith physical P S place fit dir boot st bootBits geometryBits strings L.header := rfl

/-- The front timing formula reads the exact packet width, tape length and
pin count of this deployed source. In particular the packet contains a full
physical word even at a zero-width private input. -/
theorem ChosenReader.frozenSignedData_frontOperands (u : Fin (R+1)) :
    let deployed := reader.frozenSignedData physical P S fit W pos sites edges ports copies bundles headerFactor
      valuation entry totals old L t boot bootBits gap
    let G := wiringWith physical P deployed indexWidth link (k+1) ec fit
    let packet := reader.packetAt (place u)
    let slot := adviceOffsetWith physical r 32 64 rw (k+1)
    let args := (arena).unitAddresses slot packet
    let op := reader.siteOperandsWith physical P S place fit L.header u
    let f := G.transferFrame u args.header args.dst
    packet.bits.length=reader.packetBitCount ∧ rw≤packet.bits.length ∧ args.header=L.header ∧
      args.dst=(arena).broadcastBase ∧ f.literal=(arena).literal ∧
      op.layout.count=f.processors*f.literal := by
  intro deployed G packet slot args op f
  have size : rw≤packet.bits.length := by
    rw [ReferencePacket.bits_length,ReferencePacket.offset]
    exact (Nat.le_mul_of_pos_right rw (by omega)).trans (Nat.le_add_right _ _)
  exact ⟨reader.packetAt_length _,size,rfl,rfl,rfl,rfl⟩

end Diagonal

end BorderVNP
end Computability
end OAI
