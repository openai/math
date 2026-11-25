import OAI.Computability.BorderVNP.TransmissionChosenStartup
import OAI.Computability.BorderVNP.TransmissionStartupArena

/-! # Allocating the complete chosen-reader startup from the physical team dimensions -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueEntryInput DiagonalResidueRAM
open VPVNP BurstRAM RAMTape TeamContraction TeamContraction.ProcessorSlots
open RoutingISA RoutingISA.Pins
open scoped Classical

variable {K : Type*} [Field K] {dim labels : ℕ} {ι : Type} [Fintype ι]
variable {paid : PaidIdentity K dim labels} {aux : ι → K} {q k s : ℕ}
variable {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} {R : CommonField paid aux q k s ord}
variable {chart : AdvisedBranch R} [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E]
variable {teams r multBits tally W pinWidth pc reg routines m g a link n e : ℕ} {Q Γ : Type} [Fintype Q]

local notation "h" => pairedTableParameters (k+1) s
local notation "indexWidth" => (h+2)*pinWidth
variable (reader : ChosenReader chart (teams+1) r multBits tally W pinWidth)
variable (P : TeamOpcode.Program pc reg 32 routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
variable (S : SiteData teams r reg 32 W a) (fit : Fits P lib r W a teams link n e)

/-- The number of physical processors carrying a non-padding packet bit is determined
before allocating any base address or choosing the contents of the extended frame. -/
noncomputable def ChosenReader.packetBitCount : ℕ :=
  W*(6+3*reader.gates+Fintype.card (Board.Physical h pinWidth tally (paid.Entry ⊕ ι))+81)+indexWidth

/-- Serializing a chosen reader at arbitrary addresses always has the same exact length. -/
theorem ChosenReader.packetAt_length (loc : ReaderPlacement W) :
    (reader.packetAt loc).bits.length = reader.packetBitCount := by
  unfold ChosenReader.packetAt ChosenReader.nativePacket ChosenReader.packetBitCount
  exact ReferencePacket.certificate_charge _ _ _ _ _ _

/-- The literal size includes the program prefix, all initialization parameters,
the distributed advice bit and the entire free region. -/
noncomputable def ChosenReader.startupArena (free peers header : ℕ) : StartupArena :=
  ⟨teams+1,r,entryLiteral (TeamSite.Processor.machine P lib) (W+1) n (prefixCapacity r 32 reg W n+1+free),
    peers,header,reader.packetBitCount⟩

/-- Reader base addresses within the team arena. Valuations, decoded entry and summed
totals can be allocated beyond the startup arena by the subsequent pipeline. -/
def ReaderPlacement.inArena (A : StartupArena) (valuation entry totals : ℕ) (extension : Fin 81 → Word W) :
    ReaderPlacement W :=
  ⟨valuation,entry,A.ibase,A.hbase,totals,A.frame,A.dense,A.broadcastBase,extension⟩

variable (valuation entry totals : Fin (teams+1) → ℕ) (extension : Fin (teams+1) → Fin 81 → Word W)
variable (L : Routing.WireLayout (teams+1) r link)

local notation "arena" => reader.startupArena (n := n) P lib a link L.header
local notation "place" => fun u : Fin (teams+1) =>
  ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (extension u)
local notation "off" => adviceOffset P lib r W n
local notation "operands" => reader.siteOperands P lib S place fit L.header

/-- The allocator's tuple is the ordinary operand bank actually encoded on each processor. -/
theorem ChosenReader.siteOperands_arena (u : Fin (teams+1)) :
    operands u = (arena).operands u off (reader.packetAt (place u)) := by
  let A := arena
  let G := wiring P lib S indexWidth link n e fit
  let p := reader.packetAt (place u)
  change operandsAtSite G u A.ibase A.hbase (A.dense+p.offset) A.frame L.header A.broadcastBase
    ⟨off,p.bits.length,A.dense⟩ p = A.operands u off p
  rw [show p.bits.length = A.copied from reader.packetAt_length (place u)]
  rfl

/-- The nonempty broadcast fits into an actual unordered block and the chosen packet
fits on its physical processors. The single allocation ceiling now bounds all addresses
used by the broadcast, advice decoder, pin substitution, and identity checker. -/
theorem ChosenReader.arena_fits (u : Fin (teams+1)) (hdr : 0 < L.header)
    (copies : reader.packetBitCount ≤ r) (ceiling : (arena).next < 2^W) :
    let B := operands u
    let p := reader.packetAt (place u)
    B.Fits W ∧ B.broadcast.Fits W B.frameBase ∧ B.advice.Fits B.broadcast W B.frameBase ∧
      ExtendedFrame.Fits W B.frameBase B.advice.dst p.entry.length ∧
      LoopFits W B.layout ∧ IdentityFits B.layout W ∧ B.layout.width ≤ B.layout.count := by
  have three := L.three
  let edge : Routing.Block (teams+1) := ⟨(⟨0,by omega⟩,⟨1,by omega⟩),Nat.zero_lt_one⟩
  have block : L.header ≤ link*r := by
    have load := L.fits edge
    rw [Nat.mul_comm]; omega
  have procs : 0 < r := Nat.pos_of_mul_pos_left (hdr.trans_le block)
  have peers : 0 < link := Nat.pos_of_mul_pos_right (hdr.trans_le block)
  have slot : off < (arena).literal := by
    change _ < entryLiteral _ (W+1) n (prefixCapacity r 32 reg W n+1+a)
    unfold adviceOffset entryLiteral
    omega
  intro B p
  have all := (arena).fits u off p three procs (Nat.zero_le _ |>.trans_lt slot) peers hdr block slot
    (reader.packetAt_length (place u)).le copies ceiling
  dsimp only [B]
  rw [reader.siteOperands_arena P lib S fit valuation entry totals extension L u]
  exact all

variable (D : Packing.Directory.Layout) (boot geom : GeometryAdvice.Stripe)
variable (bootBits geomBits : Fin (teams+1) → List Bool)
variable (strings : Fin D.entries → Fin D.description → Bool)

local notation "start" => freeStart P lib r W n
local notation "sites" => reader.startupSites P lib S place fit D boot geom bootBits geomBits strings L.header

set_option maxRecDepth 3500 in
/-- The real signed processor executes the jointly allocated chosen-reader and broadcast
startup on every team. All machine fit and copy disjointness obligations follow from the
physical packet count, a nonempty broadcast and the contiguous arena ceiling. -/
theorem ChosenReader.arena_header_startup (bits : List Bool) (length : bits.length = L.header)
    (payload : Fin (teams+1) → Fin (teams+1) → ℕ → Bool) (u : Fin (teams+1))
    (pin : Fin indexWidth → Bool) (mac : TeamOpcode.Macros W 8) (bank : Bank W)
    (regions : JointRoom D start a boot geom) (hdr : 0 < L.header)
    (copies : reader.packetBitCount ≤ r) (ceiling : (arena).next < 2^W) :
    let T := sites
    let B := operands u
    let p := reader.packetAt (place u)
    let pub := T.publicWords u
    let G := wiring P lib T indexWidth link n e fit
    let ext := JointHeader.exterior L bits length payload
    let F := G.processorFields u pin ext B.layout.ibase B.layout.hbase B.layout.starbase
    let f := G.transferFrame u L.header B.broadcastBase
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord W F.header)
    ∃ es z mz, Runs pub mac JointHeader.bootHeader bank initial es z mz ∧
      traceCost es ≤ jointBudget p.bits.length W+f.readTicks ∧
      (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧
      JointHeader.BootHeaderState F f B.advice p pub bits z mz ∧
      JointImage D start a boot geom (bootBits u) (geomBits u) strings u.val F := by
  have bounds := reader.arena_fits P lib S fit valuation entry totals extension L u hdr copies ceiling
  apply reader.joint_header_startup P lib S place fit D boot geom bootBits geomBits strings
    L bits length payload u pin mac bank regions bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2.1
  · exact Nat.le_add_right _ _
  · left
    change (arena).dense + (reader.packetAt (place u)).bits.length ≤ (arena).dense + reader.packetBitCount
    rw [reader.packetAt_length]

end Diagonal

end BorderVNP
end Computability
end OAI
