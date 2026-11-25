import OAI.Hierarchy.DescentTerminalBranchInputs
import OAI.Hierarchy.DescentTerminalBranchBankRoom
import OAI.Hierarchy.DescentTerminalBranchEventRoom
import OAI.Hierarchy.DescentTerminalBranchPointerRoom
import OAI.Hierarchy.DescentTerminalBranchLiteralReads
import OAI.Hierarchy.DescentTerminalPlacedSeen
import OAI.Hierarchy.DescentTerminalScalarLUTPrice

namespace OAI
/-! # A reached leaf printed by the placed native terminal program -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentSixParty DescentCompiler DescentKernelHistory DescentEpochTagKeys DescentTerminalEmitter.Branch
open DescentTerminalEmitter.Compact DescentTerminalVertexFields DescentTerminalBinReaddress DescentTerminalPorts
open DescentTerminalScalarTransposes Computability.BorderVNP.Crossing
open scoped Classical BigOperators

noncomputable section
set_option quotPrecheck false

variable {F Port U : Type} [Field F] [Fintype Port] {ew : Port → ℕ}
variable {D k age zStage degree wire hist K W q piece bw H N A verts initial arity groups stride : ℕ}
variable {G : PoweredGadget F} {ε price : ℝ} {σ : AtomSchedule} {world : MarkedWorld F D Port ew}
variable {live : DescentSixParty.Reached world G price ε σ k age zStage degree wire hist}
variable (cfg : Shape) (l : Leaf cfg world live U W q piece H N A verts) (book : Codec U initial)
variable (J : Input) (R : MaskAllocation.Channels (2^k)) (start header front B : ℕ)
local notation "grain" => W*piece
local notation "roles" => DescentBundleTagKeys.capacity initial arity groups grain stride
local notation "V" => (⟨q,roles,H,N,A,grain,σ.groupCount age⟩ : Home.Format)
local notation "codes" => DescentTerminalScalarHeader.range q roles H N A grain verts
local notation "empty" => (DescentTerminalChronologicalBooks.empty q roles H N A grain verts grain).val
local notation "base" => afterMeter V cfg R start
local notation "registerFile" => registers V cfg R start header
local notation "counter" => meter V R start
local notation "cols" => ScalarLiterals.columns q roles H N A grain verts W B cfg.terminal.pool J.sources
local notation "inputPlan" => ({J with sources:=cols} : Input)
local notation "abi" => layout cfg inputPlan base registerFile
local notation "groupsAt" => σ.groupCount age
local notation "nativeBanks" => DescentTerminalChipBootWords.chipBanks (K:=K) (W:=W) (q:=q)
  (p:=piece) codes (abi).emit front empty
local notation "processor" => chip cfg inputPlan base
variable (page : verts*span q (DescentBundleTagKeys.capacity initial arity groups (W*piece) stride)
    H N A (W*piece) ≤ B) (values : Fin 43 → ℕ → ℕ)
local notation "literals" => ScalarLiterals.data q roles H N A grain verts W B cfg.terminal.pool l.qp J.sources values
variable (m : Memory bw) (pay : RowBit cfg.terminal.plane.rawRows (q*(W*piece)) → Bool)
    (outer : Ports ew) (z : DescentTerminalChipPins.Inputs K W q piece → Bool)
local notation "mounted" => (rowArena cfg inputPlan base).mount (input V cfg inputPlan R start header page literals m)
local notation "eventsAt" => Suffix.events cfg abi (counter).layout mounted
local notation "slotsAt" => Suffix.sockets cfg abi mounted
local notation "issuedAt" => DescentTerminalEmitter.issued cfg.terminal (abi).emit (abi).directory
  (maskedMem (counter).layout (abi).directory (σ.hostSize age) slotsAt)

/-- Read the real boot rows before the immutable scalar tables and execute the fixed
calendar placement. Each private node, route, and scatter record comes from the same
entering branch. All fixed address, literal, and chip capacity fields are computed here. -/
def placed_printed
    (siteCount : cfg.sites = σ.hostSize age)
    (gateRows : cfg.terminal.rows = K*W) (pool : cfg.terminal.pool = K*W)
    (leaves : cfg.terminal.leaves = cfg.terminal.pool)
    (early : Earlier cfg inputPlan base (counter).layout bw)
    (room : last V cfg inputPlan R start < 2^bw)
    (before : front + DescentTerminalBoot.total K W q piece codes ≤ start)
    (boot : ∀ j < DescentTerminalBoot.total K W q piece codes,
      m (front+j) = DescentTerminalBoot.back z bw codes j)
    (h : ℕ) (roleCount : 0 < roles) (spare : 0 < B)
    (shortPage : 32*B ≤ h) (shortRows : 32*W ≤ h) (shortWord : 16*(q*grain) ≤ h)
    (large : 10 ≤ h) (addressBits : h/2 ≤ bw)
    (b : l.Entering cfg (arity:=arity) (groups:=groups) (stride:=stride) book abi
      (counter).layout mounted nativeBanks pay outer pool page) :
    l.Printed cfg (arity:=arity) (groups:=groups) (stride:=stride) book abi
      (counter).layout mounted nativeBanks processor pay outer z B := by
  have low : start ≤ base := by change start ≤ start+_+_+_+_+3; omega
  have beforeAll := before.trans low
  have liveBounds := branchBanks cfg inputPlan base registerFile codes front empty beforeAll gateRows room
  have homeBounds := branchEvents cfg inputPlan base (counter).layout registerFile early room
  have machine := suffix_room cfg inputPlan base (counter).layout registerFile early room
  have words := shared_tables q roles H N A grain verts W B h roleCount page shortPage shortRows shortWord large
  have higher : 2^(h/2) ≤ 2^bw := Nat.pow_le_pow_right (by decide) addressBits
  have booted := chip_started V cfg inputPlan R start header page literals front empty z m early room before boot
  have tables := branch_literal_reads V cfg J R start header verts W l.qp page values front empty z m early room before boot
  have same : issuedAt = eventsAt := by
    unfold Suffix.events Suffix.pages
    rw [siteCount]
  refine {
    siteCount := siteCount
    fitsBins := l.binsFit cfg pool
    pos := by omega
    capacity := machine.issuer
    wordFit := by omega
    volume := l.volume
    clustered := b.clustered
    emptyKey := rfl
    bounds := liveBounds.bounds
    roomOut := liveBounds.roomOut
    tableFit := liveBounds.tableFit
    keyFit := words.2.2.2.trans higher
    headerBase := liveBounds.headerBase
    headerRoom := liveBounds.headerRoom
    payloadRoom := liveBounds.payloadRoom
    ptrRoom := liveBounds.ptrRoom
    short := b.short
    onePass := leaves
    homeId := b.homeId
    ranking := b.ranking
    bp := spare
    oneWord := page
    occupied := b.occupied
    previous := b.previous
    shared := b.shared
    controls := b.controls
    pages := by simpa only [siteCount] using homeBounds.pages
    stored := homeBounds.stored
    pagesFit := by simpa only [siteCount] using homeBounds.pagesFit
    preserve := homeBounds.preserve
    wordSide := (show W ≤ bw by omega).trans_lt Nat.lt_two_pow_self
    eventFit := homeBounds.eventFit
    eventSize := homeBounds.eventSize
    frames := homeBounds.frames
    compileLow := homeBounds.compileLow
    half := ?_
    identity := ?_
    decoder := ?_
    maskAlias := homeBounds.maskAlias
    romLow := homeBounds.romLow
    fieldsFit := words.2.1.trans higher
    headerROM := ?_
    pointer := ?_
    safe := branch_pointer_safe (K:=K) (W:=W) (q:=q) (piece:=piece) cfg inputPlan base registerFile codes front empty beforeAll
    ports := b.ports
    cables := b.cables
    gateRows := gateRows
    gateBank := rfl
    gateLife := branch_gate_life (K:=K) (W:=W) (q:=q) (piece:=piece) cfg inputPlan base registerFile codes front empty gateRows
    VG := b.VG
    VV := b.VV
    VM := b.VM
    VA := b.VA
    nameBits := b.nameBits
    localFit := b.localFit
    names := b.names
    args := b.args
    matchNames := b.matchNames
    routeSpace := by simpa only [gateRows] using machine.issuer.gate
    routeColumns := b.routeColumns
    fits := liveBounds.fits
    sizes := liveBounds.sizes
    seen := l.placed_seen cfg inputPlan base registerFile codes front empty b.cables.volume pay outer
    routeFit := liveBounds.routeFit
    routeSize := liveBounds.routeSize
    bootInit := ?_
    bootBefore := booted.2.2
    bootCaps := liveBounds.bootCaps }
  · rw [same]; exact tables.half
  · rw [same]; exact tables.identity
  · rw [same]; exact tables.decoder
  · rw [same]; exact tables.headerROM
  · rw [same]; exact tables.pointer
  · rw [same]; exact booted.1

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
