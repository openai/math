import OAI.Hierarchy.DescentTerminalBranchJoined
import OAI.Hierarchy.DescentTerminalPaidBoot

namespace OAI
/-! # One physical original input for hidden row words and all native chip banks -/
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
local notation "raw" => RowBit cfg.terminal.plane.rawRows (q*grain) → Bool
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
variable (m : Memory bw) (outer : Ports ew) (choice : DescentTerminalPaidBoot.Input K W q piece cfg.terminal.plane.rawRows → Bool)
local notation "mounted" => (rowArena cfg inputPlan base).mount (input V cfg inputPlan R start header page literals m)
local notation "eventsAt" => Suffix.events cfg abi (counter).layout mounted
local notation "slotsAt" => Suffix.sockets cfg abi mounted
local notation "issuedAt" => DescentTerminalEmitter.issued cfg.terminal (abi).emit (abi).directory
  (maskedMem (counter).layout (abi).directory (σ.hostSize age) slotsAt)

/-- All row choices and all chip controls project from the actual joined RAM input.
The word-addressed startup tape is the same tape used to publish the public and
private row streams. -/
def paid_printed
    (siteCount : cfg.sites = σ.hostSize age)
    (gateRows : cfg.terminal.rows = K*W) (pool : cfg.terminal.pool = K*W)
    (leaves : cfg.terminal.leaves = cfg.terminal.pool)
    (early : Earlier cfg inputPlan base (counter).layout bw)
    (room : last V cfg inputPlan R start < 2^bw)
    (before : front + DescentTerminalPaidBoot.total K W q piece codes cfg.terminal.plane.rawRows ≤ start)
    (boot : ∀ j < DescentTerminalPaidBoot.total K W q piece codes cfg.terminal.plane.rawRows,
      m (front+j) = DescentTerminalPaidBoot.back choice bw codes j)
    (h : ℕ) (roleCount : 0 < roles) (spare : 0 < B)
    (shortPage : 32*B ≤ h) (shortRows : 32*W ≤ h) (shortWord : 16*(q*grain) ≤ h)
    (large : 10 ≤ h) (addressBits : h/2 ≤ bw)
    (b : l.Entering cfg (arity:=arity) (groups:=groups) (stride:=stride) book abi
      (counter).layout mounted nativeBanks (choice ∘ Sum.inr) outer pool page) :
    l.Printed cfg (arity:=arity) (groups:=groups) (stride:=stride) book abi
      (counter).layout mounted nativeBanks processor (choice ∘ Sum.inr) outer (choice ∘ Sum.inl) B := by
  have bootRows := (DescentTerminalPaidBoot.ranges choice bw codes front m boot).1
  have chipRows : DescentTerminalBoot.total K W q piece codes ≤
      DescentTerminalPaidBoot.total K W q piece codes cfg.terminal.plane.rawRows := Nat.le_add_right ..
  exact placed_printed cfg l book J R start header front B page values m (choice ∘ Sum.inr) outer
    (choice ∘ Sum.inl) siteCount gateRows pool leaves early room
    ((Nat.add_le_add_left chipRows front).trans before) bootRows h roleCount spare shortPage
    shortRows shortWord large addressBits b

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
