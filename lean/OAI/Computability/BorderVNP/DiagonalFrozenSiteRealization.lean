import OAI.Computability.BorderVNP.DiagonalSignedDemandPacket
import OAI.Computability.BorderVNP.DiagonalEnrichedPacketGeometry
import OAI.Computability.BorderVNP.DiagonalFrozenReaderBounds
import OAI.Computability.BorderVNP.DiagonalEnrichedRealization
import OAI.Computability.BorderVNP.DiagonalEnrichedSiteWiring
import OAI.Computability.BorderVNP.DiagonalFixedSignedSites

/-! # The charged reader on one physical site table and one initialized signed seed -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Branch Crossing Cover Shortening Shortening.Adaptive Packing Packing.DeckGrid Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew GridHosts TeamContraction ProcessorSlots TeamScales EnrichedOuter
open ParseBatch ParseBatchVerifier Prewire VPVNP BorderVNP.Epoch BorderVNP.Epoch.Round
open RoutingISA RoutingISA.Evaluator CompactMachine CellMacro.Generator ResiduePins ResidueIndex ResidueBox
open VPVNP.BurstRAM
open scoped Classical BigOperators
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 7000
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K K₀ : Type} [Field K] [Field K₀] {paid : PaidIdentity K D m}
    {schedule : SiteSchedule paid} (cube : FixedCube K₀) (φ : K₀ →+* K)
    {extra E deg Q₀ A B j cut : ℕ} (scales : EpochScales schedule (cube.pred+1) extra)
    (b : JointSchedule.{0} scales (E+1) deg Q₀ A B j)
    {R r k link rw ec a s copies T d header Q pinWidth pc char : ℕ}
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) {common : CommonField paid (φ ∘ cube.table) char k s ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (R+1) r (b.physical.multBits (k+1)) (b.physical.tally (k+1)) rw pinWidth)
    (plan : SeedPlan schedule (k+1) r d T copies header Q)
    (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc 64 32 8)
    (fit : fitsWith physical 64 32 r rw a R link (k+1) ec)
    (data : SiteData R r 64 32 rw a)

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => tileCount (Fintype.card (Cube D)) d
local notation "h" => pairedTableParameters (k+1) s
local notation "pins" => (h+2)*pinWidth
local notation "tail" => setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a)
local notation3 (prettyPrint := false) "G₀" => tapeTemplate (r:=r) (R:=R) (link:=link) (regs:=64) (w:=rw)
  (e:=ec) (width:=rw+1) (k:=k) (a:=tail) physical fit pins
local notation3 (prettyPrint := false) "free" => data.enrichedFree physical P (k+1) ec link
local notation3 (prettyPrint := false) "G₁" => wiringWith physical P data pins link (k+1) ec fit

variable {order : Fin (tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate (r:=r) (R:=R) (link:=link) (regs:=64) (w:=rw)
      (e:=ec) (width:=rw+1) (k:=k) (a:=setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a))
      physical fit ((pairedTableParameters (k+1) s+2)*pinWidth)) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate (r:=r) (R:=R) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1) (k:=k)
      (a:=setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a)) physical fit
      ((pairedTableParameters (k+1) s+2)*pinWidth))) ↪ Fin np)
    (table : (seedBundle (tapeTemplate (r:=r) (R:=R) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1) (k:=k)
      (a:=setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a)) physical fit
      ((pairedTableParameters (k+1) s+2)*pinWidth)) (Fintype.card (Cube D)) d order position copies).Tables K) {σ : Type} [Fintype σ] (x : σ → Bool)
    (count : (fan schedule)^T*copies=R+1) (hg : 0 < inputBlockWidth r (k+1) (Fintype.card (Cube D)) d)

local notation3 (prettyPrint := false) "leaf" => plan.frozenLeaf G₀ order position W code sites edges ports table x
local notation3 (prettyPrint := false) "net" => EnrichedTape.network physical fit position free count plan.compiled.machine leaf rfl
local notation3 (prettyPrint := false) "bank" => canonicalBank (G:=G₁) hg (gridRoom G₁ (Fintype.card_pos : 0<tiles))
local notation3 (prettyPrint := false) "codec" => boxPinCodec h reader.rankFits reader.boxFits
local notation "Idx" => Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin h) (chart.pinRadius (R+1) r)
local notation "alphabet" => BorderVNP.Cube.alphabet scales.α (k+1)
local notation "volume" => ((R+1)*exterior ((scales.τ:ℝ)/5) r (k+1) : ℕ)
local notation3 (prettyPrint := false) "Y" => chart.gadgets ∘ Sum.inl
/-- Team numbering of the original algebraic expansion. -/
noncomputable local instance runTeams {j : ℕ} : Fintype (Port (fan schedule) (Fin copies × Unit) j) :=
  Replay.batchFinite (fan schedule) (Fin copies × Unit) j

/-- The expansion uses the chosen frozen verifier, the actual RAM literal and
the canonical substituted bank. On this same site, the two startup modes and
the weighted physical run give the complete residue column. All four numeric
reader conditions follow from the selected seed and the cube packet count. -/
noncomputable def realizationOfDeployedSite
    (length : LengthBudget b cut (k+1)) (room : ReaderTallyInputsAt cube b (k+1))
    (batch : r = stretch b.ρ (k+1)) (candidate : s = stretch b.σ (k+1)) (groups : R = b.physical.teamsPred (k+1))
    (depthEq : d+1 = CoverScale.initialDepth (Cube D) r (k+1)) (time : T = epochs scales.τ (k+1))
    (small : 1+initialMass (D:=D) (k+1) r d copies header ≤ TeamScales.width (k+1) (1/2:ℝ))
    (packet : ∀ q, PacketPlacement (Port (fan schedule) (Fin copies × Unit) T)
      cube.pred alphabet cube.b cube.h cube.copies (net q))
    (packed : ∀ q, (packet q).blocks = BorderVNP.Cube.Physical.blocksFor volume (cube.h*cube.b) (alphabet^(cube.pred+1)))
    (args : Fin (R+1) → UnitAddresses) (mac : TeamOpcode.Macros rw 8)
    (modes : ∀ j : Idx, signedContraction (G₁).slot ((codec).encode j) =
      (if (codec).encode j = (codec).encode reader.star then 1 else 0) +
        ∑ ext, ∏ u, positiveMaskedNativeValue G₁ (signedBody (cube.cubeID paid)) mac data.publicWords data.registers args
          ((codec).encode j) data.limit.val data.burst.val ((k+1)^25) ext u)
    (reject : ∀ (j : Idx) ext, ¬ PositiveExterior G₁ args ((codec).encode j) rw ext →
      (∏ u, positiveMaskedNativeValue G₁ (signedBody (cube.cubeID paid)) mac data.publicWords data.registers args
        ((codec).encode j) data.limit.val data.burst.val ((k+1)^25) ext u)=0)
    (runs : ∀ j : Idx, reader.WiredPinExecution (cube.cubeID paid) SparseExterior.driver G₁ args mac
      data.publicWords data.registers data.limit.val data.burst.val
      (EnrichedTape.assignedPath (cs:=cube.width) physical fit W position free count plan.compiled.machine leaf rfl Y
        chart.preserves_paid Sum.inl hg packet Sum.inr bank)
      (EnrichedTape.assigned (cs:=cube.width) physical fit W position free count plan.compiled.machine leaf rfl Y
        chart.preserves_paid Sum.inl hg packet Sum.inr bank ord) j) :
    reader.Realization (TeamContraction.cutWidth (k+1)+tail) link (Wires.innerWidth r 64 rw ec (rw+1))
      (Wires.Edge r 64 rw ec (rw+1)) := by
  apply EnrichedTape.realizationOfWiredRuns cube φ ord chart reader physical fit W position free count
    plan.compiled.machine leaf rfl hg packet bank (canonical_read (G:=G₁) hg (gridRoom G₁ Fintype.card_pos))
    (cube.cubeID paid) SparseExterior.driver args mac data.publicWords data.registers data.limit.val data.burst.val modes reject runs
  intro raw u
  exact plan.frozen_assigned_reader_bounds physical fit W position code sites edges ports table x free count
    Y chart.preserves_paid Sum.inl hg cube scales b length room batch candidate groups depthEq time small packet
    Sum.inr packed ord raw u chart.degreeSum

local notation3 (prettyPrint := false) "frozenWords" => (plan.execute G₀ order position σ).choose.eval x

/-- The mean packet is the actual selected directory on the prewired rows.
Every later installed literal reads that same row network. The joint history,
substituted pin bank, source ownership and block count are shared. -/
noncomputable def realizationOfFrozenPacketRuns
    (length : LengthBudget b cut (k+1)) (room : ReaderTallyInputsAt cube b (k+1))
    (batch : r = stretch b.ρ (k+1)) (candidate : s = stretch b.σ (k+1)) (groups : R = b.physical.teamsPred (k+1))
    (depthEq : d+1 = CoverScale.initialDepth (Cube D) r (k+1)) (time : T = epochs scales.τ (k+1))
    (small : 1+initialMass (D:=D) (k+1) r d copies header ≤ TeamScales.width (k+1) (1/2:ℝ))
    (calibrated : plan.SignedLabelRows count link (cube.pred+1) scales.α ((scales.τ:ℝ)/5))
    (lit : (G₀).program.length+(TeamContraction.cutWidth (k+1)+tail) = literal scales.α (k+1))
    (hd : 0 < alphabet) (hp : (fieldSewParams G₀ axes d).Valid)
    {cells : ℕ} (number : (Cube D → Deck (depth schedule (d+1) T+1)) ≃ Fin cells) (gap : ℕ)
    (args : Fin (R+1) → UnitAddresses) (mac : TeamOpcode.Macros rw 8) :=
  let physicalPackets := plan.signedPackets count G₀ order position W code sites edges ports table frozenWords (leaf).property
    cube scales.α ((scales.τ:ℝ)/5) calibrated lit hd hp number gap
  plan.realizationOfDeployedSite cube φ scales b ord chart reader physical P fit data W position code sites edges ports
    table x count hp.block length room batch candidate groups depthEq time small (fun q => physicalPackets q)
    (fun q => plan.signedPackets_blocks count G₀ order position W code sites edges ports table frozenWords (leaf).property
      cube scales.α ((scales.τ:ℝ)/5) calibrated lit hd hp number gap q) args mac

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
