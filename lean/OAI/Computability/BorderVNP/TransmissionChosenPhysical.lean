import OAI.Computability.BorderVNP.TransmissionChosenArena
import OAI.Computability.BorderVNP.TransmissionJointProgram

/-! # The chosen reader starts on the actual physical program table -/

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
variable {teams r multBits tally W pinWidth pc reg routines a link n e : ℕ}

local notation "h" => pairedTableParameters (k+1) s
local notation "indexWidth" => (h+2)*pinWidth
variable (reader : ChosenReader chart (teams+1) r multBits tally W pinWidth)
variable (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc reg 32 routines)
variable (S : SiteData teams r reg 32 W a)

section Operands
variable (places : Fin (teams+1) → ReaderPlacement W) (fit : fitsWith physical reg 32 r W a teams link n e)

/-- Concrete ordinary operand bank which points to precisely the chosen reader's packet,
actual pin arrays and the real layout of its processor tapes. -/
noncomputable def ChosenReader.siteOperandsWith (header : ℕ) (u : Fin (teams+1)) : PacketOperands :=
  let p := reader.packetAt (places u)
  let G := wiringWith physical P S indexWidth link n e fit
  let A : AdviceLayout := ⟨adviceOffsetWith physical r 32 reg W n,p.bits.length,(places u).dense⟩
  operandsAtSite G u (places u).row (places u).column (A.dst+p.offset)
    (places u).frame header (places u).broadcast A p

variable (D : Packing.Directory.Layout) (boot geom : GeometryAdvice.Stripe)
variable (bootBits geomBits : Fin (teams+1) → List Bool)
variable (strings : Fin D.entries → Fin D.description → Bool)

local notation "start" => freeStartWith physical r 32 reg W n
local notation "packs" => fun v : Fin (teams+1) => reader.packetAt (places v)
local notation "operands" => reader.siteOperandsWith physical P S places fit

/-- Install all ordinary operands, the chosen reader packet, the two wider advice stripes
and the actual original private descriptions in a single signed wiring. -/
noncomputable def ChosenReader.startupSitesWith (header : ℕ) : SiteData teams r reg 32 W a :=
  (S.withOperands (operands header)).joint D start packs boot geom bootBits geomBits strings

variable {Q Γ : Type} [Fintype Q] {m g : ℕ} (lib : Fin routines → TeamSite.Macro Q Γ m g)

/-- The first free bit in the ordinary interpreter is the actual physical offset
of that interpreter's complete fixed prefix. -/
theorem freeStartWith_ordinary : freeStartWith (TeamSite.Processor.machine P lib) r 32 reg W n =
    freeStart P lib r W n := (freeStart_eq P lib n).symm

/-- The original signed site data is recovered on the original interpreter. -/
theorem ChosenReader.startupSitesWith_ordinary (fit₀ : Fits P lib r W a teams link n e) (header : ℕ) :
    reader.startupSitesWith (TeamSite.Processor.machine P lib) P S places fit₀ D boot geom bootBits geomBits strings header =
      reader.startupSites P lib S places fit₀ D boot geom bootBits geomBits strings header := by
  unfold ChosenReader.startupSitesWith ChosenReader.startupSites
  rw [freeStartWith_ordinary P lib]
  rfl

end Operands

variable (fit : fitsWith physical reg 32 r W a teams link n e)

/-- The literal size includes the program prefix, all initialization parameters,
the distributed advice bit and the entire free region. -/
noncomputable def ChosenReader.startupArenaWith (free peers header : ℕ) : StartupArena :=
  ⟨teams+1,r,entryLiteral physical (W+1) n (prefixCapacity r 32 reg W n+1+free),
    peers,header,reader.packetBitCount⟩

variable (valuation entry totals : Fin (teams+1) → ℕ) (extension : Fin (teams+1) → Fin 81 → Word W)
variable (L : Routing.WireLayout (teams+1) r link)

local notation "arena" => reader.startupArenaWith (n := n) (reg := reg) physical a link L.header
local notation "place" => fun u : Fin (teams+1) =>
  ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (extension u)
local notation "off" => adviceOffsetWith physical r 32 reg W n
local notation "operands" => reader.siteOperandsWith physical P S place fit L.header

/-- The allocator's tuple is the ordinary operand bank actually encoded on each processor. -/
theorem ChosenReader.siteOperands_arenaWith (u : Fin (teams+1)) :
    operands u = (arena).operands u off (reader.packetAt (place u)) := by
  let A := arena
  let G := wiringWith physical P S indexWidth link n e fit
  let p := reader.packetAt (place u)
  change operandsAtSite G u A.ibase A.hbase (A.dense+p.offset) A.frame L.header A.broadcastBase
    ⟨off,p.bits.length,A.dense⟩ p = A.operands u off p
  rw [show p.bits.length = A.copied from reader.packetAt_length (place u)]
  rfl

/-- The nonempty broadcast fits into an actual unordered block and the chosen packet
fits on its physical processors. The single allocation ceiling now bounds all addresses
used by the broadcast, advice decoder, pin substitution, and identity checker. -/
theorem ChosenReader.arena_fitsWith (u : Fin (teams+1)) (hdr : 0 < L.header)
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
    unfold adviceOffsetWith entryLiteral
    omega
  intro B p
  have all := (arena).fits u off p three procs (Nat.zero_le _ |>.trans_lt slot) peers hdr block slot
    (reader.packetAt_length (place u)).le copies ceiling
  dsimp only [B]
  rw [reader.siteOperands_arenaWith physical P S fit valuation entry totals extension L u]
  exact all

variable (D : Packing.Directory.Layout) (boot geom : GeometryAdvice.Stripe)
variable (bootBits geomBits : Fin (teams+1) → List Bool)
variable (strings : Fin D.entries → Fin D.description → Bool)

local notation "start" => freeStartWith physical r 32 reg W n
local notation "sites" => reader.startupSitesWith physical P S place fit D boot geom bootBits geomBits strings L.header

set_option maxRecDepth 3500 in
/-- On the actual signed site, arbitrary nonheader wires are allowed during the initial packet and header copy. -/
theorem ChosenReader.arena_header_startupCommonWith (bits : List Bool) (length : bits.length = L.header)
    (wire : Exterior teams r link → Bool)
    (common : ∀ b, (L.exteriorEquiv wire).broadcast b = JointHeader.headerBits bits length) (u : Fin (teams+1))
    (pin : Fin indexWidth → Bool) (mac : TeamOpcode.Macros W 8) (bank : Bank W)
    (regions : JointRoom D start a boot geom) (hdr : 0 < L.header)
    (copies : reader.packetBitCount ≤ r) (ceiling : (arena).next < 2^W) :
    let T := sites
    let B := operands u
    let p := reader.packetAt (place u)
    let pub := T.publicWords u
    let G := wiringWith physical P T indexWidth link n e fit
    let ext := wire
    let F := G.processorFields u pin ext B.layout.ibase B.layout.hbase B.layout.starbase
    let f := G.transferFrame u L.header B.broadcastBase
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord W F.header)
    ∃ es z mz, Runs pub mac JointHeader.bootHeader bank initial es z mz ∧
      traceCost es ≤ jointBudget p.bits.length W+f.readTicks ∧
      (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧
      JointHeader.BootHeaderState F f B.advice p pub bits z mz ∧
      JointImage D start a boot geom (bootBits u) (geomBits u) strings u.val F := by
  have bounds := reader.arena_fitsWith physical P S fit valuation entry totals extension L u hdr copies ceiling
  intro T B p pub G ext F f initial
  have scalar := B.packetFrame (S.publicWords u) bounds.1
  have base : (pub 0).val = B.frameBase := B.frameBase_word (S.publicWords u) bounds.1
  obtain ⟨es,z,mz,run,cost,events,post⟩ := JointHeader.packet_header_runCommonWith physical P T
    (fun v => reader.packetAt (place v)) link n e fit u pin L bits length wire common
    B.layout.ibase B.layout.hbase B.layout.starbase B.broadcastBase pub mac bank B.advice
    scalar (base.symm ▸ bounds.2.1) (base.symm ▸ bounds.2.2.1) (base.symm ▸ bounds.2.2.2.1)
    rfl le_rfl rfl (base.symm ▸ Nat.le_add_right _ _) (Or.inl (by
      change (arena).dense+(reader.packetAt (place u)).bits.length ≤ (arena).dense+reader.packetBitCount
      rw [reader.packetAt_length]))
  exact ⟨es,z,mz,run,cost,events,post,joint_image_with physical P (S.withOperands operands)
    D (fun v => reader.packetAt (place v)) boot geom bootBits geomBits strings fit
    u pin ext B.layout.ibase B.layout.hbase B.layout.starbase regions⟩

/-- The real signed processor executes the jointly allocated chosen-reader and broadcast
startup on every team. All machine fit and copy disjointness obligations follow from the
physical packet count, a nonempty broadcast and the contiguous arena ceiling. -/
theorem ChosenReader.arena_header_startupWith (bits : List Bool) (length : bits.length = L.header)
    (payload : Fin (teams+1) → Fin (teams+1) → ℕ → Bool) (u : Fin (teams+1))
    (pin : Fin indexWidth → Bool) (mac : TeamOpcode.Macros W 8) (bank : Bank W)
    (regions : JointRoom D start a boot geom) (hdr : 0 < L.header)
    (copies : reader.packetBitCount ≤ r) (ceiling : (arena).next < 2^W) :
    let T := sites
    let B := operands u
    let p := reader.packetAt (place u)
    let pub := T.publicWords u
    let G := wiringWith physical P T indexWidth link n e fit
    let ext := JointHeader.exterior L bits length payload
    let F := G.processorFields u pin ext B.layout.ibase B.layout.hbase B.layout.starbase
    let f := G.transferFrame u L.header B.broadcastBase
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord W F.header)
    ∃ es z mz, Runs pub mac JointHeader.bootHeader bank initial es z mz ∧
      traceCost es ≤ jointBudget p.bits.length W+f.readTicks ∧
      (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧
      JointHeader.BootHeaderState F f B.advice p pub bits z mz ∧
      JointImage D start a boot geom (bootBits u) (geomBits u) strings u.val F := by
  exact reader.arena_header_startupCommonWith physical P S fit valuation entry totals extension L D boot geom
    bootBits geomBits strings bits length (JointHeader.exterior L bits length payload)
    (JointHeader.exterior_header L bits length payload) u pin mac bank regions hdr copies ceiling

end Diagonal

end BorderVNP
end Computability
end OAI
