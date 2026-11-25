import OAI.Computability.BorderVNP.TransmissionChosenPacket
import OAI.Computability.BorderVNP.TransmissionJointHeaderBoot

/-! # The chosen finite-branch reader in the real signed site and its RAM startup -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueEntryInput
open VPVNP BurstRAM RAMTape TeamContraction TeamContraction.ProcessorSlots
open RoutingISA RoutingISA.Pins

/-- All local addresses of a chosen reader installation. The row and column addresses
are the actual substituted and live pin arrays; totals is the real summed exponent bank. -/
structure ReaderPlacement (w : ℕ) where
  /-- Beginning of the shared gate valuation bank. -/
  valuation : ℕ
  /-- Destination of the decoded entry program. -/
  entry : ℕ
  /-- Substituted row index. -/
  row : ℕ
  /-- Copy of the actual column index. -/
  column : ℕ
  /-- Summed exponent and multiplicity bank. -/
  totals : ℕ
  /-- Ordinary and extended scalar frame base. -/
  frame : ℕ
  /-- Contiguous residue-entry, extended-frame and H* bit packet. -/
  dense : ℕ
  /-- Destination of the common broadcast read from the actual exterior blocks. -/
  broadcast : ℕ
  /-- Exact 81 runtime extended-frame fields. -/
  extension : Fin 81 → Word w

variable {K : Type*} [Field K] {dim labels : ℕ} {ι : Type} [Fintype ι]
variable {paid : PaidIdentity K dim labels} {aux : ι → K} {q k s : ℕ}
variable {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} {R : CommonField paid aux q k s ord}
variable {chart : AdvisedBranch R} [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E]
variable {teams r multBits tally W pinWidth pc reg routines m g a link n e : ℕ} {Q Γ : Type} [Fintype Q]

local notation "indexWidth" => (pairedTableParameters (k+1) s + 2)*pinWidth
variable (reader : ChosenReader chart (teams+1) r multBits tally W pinWidth)
variable (P : TeamOpcode.Program pc reg 32 routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
variable (S : SiteData teams r reg 32 W a) (places : Fin (teams+1) → ReaderPlacement W)
variable (fit : Fits P lib r W a teams link n e)

/-- The native packet, with source addresses taken from this particular physical team's
three pin/subtotal arrays and its reference taken from the chosen reader on the curve. -/
noncomputable def ChosenReader.packetAt (loc : ReaderPlacement W) : ReferencePacket W indexWidth :=
  reader.nativePacket loc.valuation loc.entry loc.row loc.column loc.totals loc.extension

/-- Concrete ordinary operand bank which points to precisely the chosen reader's packet,
actual pin arrays and the real layout of its processor tapes. -/
noncomputable def ChosenReader.siteOperands (header : ℕ) (u : Fin (teams+1)) : PacketOperands :=
  let p := reader.packetAt (places u)
  let G := wiring P lib S indexWidth link n e fit
  let A : AdviceLayout := ⟨adviceOffset P lib r W n,p.bits.length,(places u).dense⟩
  operandsAtSite G u (places u).row (places u).column (A.dst+p.offset)
    (places u).frame header (places u).broadcast A p

variable (D : Packing.Directory.Layout) (boot geom : GeometryAdvice.Stripe)
variable (bootBits geomBits : Fin (teams+1) → List Bool)
variable (strings : Fin D.entries → Fin D.description → Bool)

local notation "start" => freeStart P lib r W n
local notation "packs" => fun v : Fin (teams+1) => reader.packetAt (places v)
local notation "operands" => reader.siteOperands P lib S places fit

/-- Install all ordinary operands, the chosen reader packet, the two wider advice stripes
and the actual original private descriptions in a single signed wiring. -/
noncomputable def ChosenReader.startupSites (header : ℕ) : SiteData teams r reg 32 W a :=
  (S.withOperands (operands header)).joint D start packs boot geom bootBits geomBits strings

local notation "sites" => reader.startupSites P lib S places fit D boot geom bootBits geomBits strings
local notation "distinguished" =>
  PinCodec.encode (boxPinCodec (pairedTableParameters (k+1) s) reader.rankFits reader.boxFits) reader.star

set_option maxRecDepth 3500 in
/-- Every real processor decodes the chosen team-specific bank from its actual signed
input word. The finite scalar bank discharges the public-frame premise at the same time. -/
theorem ChosenReader.site_operand_run (header : ℕ) (u : Fin (teams+1)) (j : Fin r)
    (pin : Fin indexWidth → Bool) (ext : Exterior teams r link → Bool)
    (int : Wires.Edge r reg W e (W+1) → Bool) (hw : 0 < W) (hH : 2^e ≤ n) :
    let B := operands header
    let G := wiring P lib (sites header) indexWidth link n e fit
    let F := G.processorFields u pin ext (B u).layout.ibase (B u).layout.hbase (B u).layout.starbase
    let stride := entryStride (TeamSite.Processor.machine P lib) (W+1) n (prefixCapacity r 32 reg W n+1+a) teams link
    (B u).Fits W → 2*(j.val*stride+(F.row j).length) ≤ 2^(W+1) → 2*(F.row j).length ≤ 4*(2^e) →
      ∃ ticks bank, ticks ≤ TeamSite.Processor.preludeTime (entryBudget W n e (F.row j).length)
          reg 32 W (last j) ∧
        StackRuns (TeamSite.Processor.code P lib) ticks TeamSite.Processor.start
          (StackCompiler.labeledInput TeamSite.Layout.input (List.ofFn (G.word pin ext int u j)))
          (TeamSite.Processor.beginBlock (last j)) bank ∧
        (∀ i : Arg, bank (TeamSite.Layout.site (.clock (.isa (.pub i)))) = wordBits ((B u).bank (S.publicWords u) i)) ∧
        PacketFrame (B u).layout (B u).broadcast (B u).advice (B u).entryWords W
          (fun _ => 0) (operand ((sites header).publicWords u)) := by
  intro B G F stride room address count
  let T := S.joint D start packs boot geom bootBits geomBits strings
  exact site_operands_loaded P lib T B packs link n e fit hw hH u j pin ext int
    (B u).layout.ibase (B u).layout.hbase (B u).layout.starbase room address count

set_option maxRecDepth 3500 in
/-- From the literal-initialized RAM on *every* team and every exterior assignment,
the native startup installs the chosen board's entry program, curve reference and extended
frame. The two jointly pinned stripes and original private input slots are still present. -/
theorem ChosenReader.joint_startup (header : ℕ) (u : Fin (teams+1)) (pin : Fin indexWidth → Bool)
    (ext : Exterior teams r link → Bool) (mac : TeamOpcode.Macros W 8) (bank : Bank W)
    (regions : JointRoom D start a boot geom) :
    let T := sites header
    let B := operands header u
    let p := reader.packetAt (places u)
    let pub := T.publicWords u
    let G := wiring P lib T indexWidth link n e fit
    let L := B.layout
    let F := G.processorFields u pin ext L.ibase L.hbase L.starbase
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord W F.header)
    B.Fits W → B.broadcast.Fits W B.frameBase → B.advice.Fits B.broadcast W B.frameBase →
    ExtendedFrame.Fits W B.frameBase B.advice.dst p.entry.length →
    ∃ es z mz, Runs pub mac Evaluator.unitStartup bank initial es z mz ∧
      traceCost es ≤ jointBudget p.bits.length W ∧ (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧
      F.ContainsInput mz ∧ PacketFrame L B.broadcast B.advice p.entry.length W (readings pub) (readings mz) ∧
      (∀ i : Fin 81, mz (B.frameBase+31+i.val) = (places u).extension i) ∧
      DiagonalTallyBits.WordsAt mz B.advice.dst (p.entry.map wordBits) ∧
      (∀ i : Fin indexWidth, mz (L.starbase+i.val) = TeamTapeInputEmit.word W (distinguished i).toNat) ∧
      JointImage D start a boot geom (bootBits u) (geomBits u) strings u.val F := by
  intro T B p pub G L F initial bounds space adviceRoom frameRoom
  have scalar := B.packetFrame (S.publicWords u) bounds
  have base : (pub 0).val = B.frameBase := B.frameBase_word (S.publicWords u) bounds
  obtain ⟨es,z,mz,run,cost,events,input,installed,extension,entry,ref⟩ :=
    jointPacket_run P lib T packs link n e fit u pin ext L.ibase L.hbase L.starbase pub mac bank B.broadcast B.advice
      scalar (base.symm ▸ space) (base.symm ▸ adviceRoom) (base.symm ▸ frameRoom) rfl le_rfl rfl
  exact ⟨es,z,mz,run,cost,events,input,installed,base ▸ extension,entry,ref,
    signed_joint_image P lib (S.withOperands (operands header)) D packs boot geom bootBits geomBits strings fit
      u pin ext L.ibase L.hbase L.starbase regions⟩

set_option maxRecDepth 3500 in
/-- On the canonical exterior assignment the same jointly wired chosen-reader site also
executes the full native broadcast. Its copied header, original private strings, H* and
entry data all inhabit one final physical memory. -/
theorem ChosenReader.joint_header_startup (L : Routing.WireLayout (teams+1) r link) (bits : List Bool)
    (length : bits.length = L.header) (payload : Fin (teams+1) → Fin (teams+1) → ℕ → Bool)
    (u : Fin (teams+1)) (pin : Fin indexWidth → Bool) (mac : TeamOpcode.Macros W 8) (bank : Bank W)
    (regions : JointRoom D start a boot geom) :
    let T := sites L.header
    let B := operands L.header u
    let p := reader.packetAt (places u)
    let pub := T.publicWords u
    let G := wiring P lib T indexWidth link n e fit
    let ext := JointHeader.exterior L bits length payload
    let F := G.processorFields u pin ext B.layout.ibase B.layout.hbase B.layout.starbase
    let f := G.transferFrame u L.header B.broadcastBase
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord W F.header)
    B.Fits W → f.Fits W B.frameBase → B.advice.Fits f W B.frameBase →
    ExtendedFrame.Fits W B.frameBase B.advice.dst p.entry.length →
    B.frameBase+112 ≤ B.broadcastBase →
    (B.advice.dst+p.bits.length ≤ B.broadcastBase ∨ B.broadcastBase+L.header ≤ B.advice.dst) →
    ∃ es z mz, Runs pub mac JointHeader.bootHeader bank initial es z mz ∧
      traceCost es ≤ jointBudget p.bits.length W+f.readTicks ∧
      (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧
      JointHeader.BootHeaderState F f B.advice p pub bits z mz ∧
      JointImage D start a boot geom (bootBits u) (geomBits u) strings u.val F := by
  intro T B p pub G ext F f initial bounds space adviceRoom frameRoom above apart
  have scalar := B.packetFrame (S.publicWords u) bounds
  have base : (pub 0).val = B.frameBase := B.frameBase_word (S.publicWords u) bounds
  obtain ⟨es,z,mz,run,cost,events,post⟩ := JointHeader.packet_header_run P lib T packs link n e fit
    u pin L bits length payload B.layout.ibase B.layout.hbase B.layout.starbase B.broadcastBase
    pub mac bank B.advice scalar (base.symm ▸ space) (base.symm ▸ adviceRoom) (base.symm ▸ frameRoom)
    rfl le_rfl rfl (base.symm ▸ above) apart
  exact ⟨es,z,mz,run,cost,events,post,
    signed_joint_image P lib (S.withOperands (operands L.header)) D packs boot geom bootBits geomBits strings fit
      u pin ext B.layout.ibase B.layout.hbase B.layout.starbase regions⟩

end Diagonal

end BorderVNP
end Computability
end OAI
