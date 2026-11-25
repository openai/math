import OAI.Hierarchy.DescentTerminalDatedScanBefore
import OAI.Hierarchy.DescentTerminalFixedSlices

namespace OAI
/-! # Bank placement at the original last scheduled reset -/

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler Catalyst DescentExteriorReplay DescentDatedAddressBook
open DescentTerminalPreflightSpace DescentTerminalFixedSlices ProtocolRAM
open DescentPacking.PackedMatch.Local.Stage DescentResetInvoice CorrectionBatch

noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {cp ar : ℕ} (X : Approximation F cp ar) (G : PoweredGadget F) (S : AtomSchedule)
  (k g p tail q drift : ℕ) (op : RotorSpec) (headerRows paidRows j r : ℕ) (snapshots : Snapshots k)
  {n deg : ℕ} (board : NonlinearExpanders.Graph n deg) (age f degree payload : ℕ)
  (ordinary : ℕ → Dated.Ordinary) (operandLanes primitiveLanes : ℕ) (previous : StageVenueTail.Date)
  (addr : ℕ → ℕ → Bank) (roster : Bank) (floor earlyFloor : ℕ)

local notation "spec" => preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
local notation "phase" => Phase.scheduled G S board k tail age p f g drift degree payload ordinary op
  operandLanes primitiveLanes previous addr roster floor
local notation "out" => (phase).output
local notation "origin" => (phase).dateBase
local notation "cal" => replayCalendar X S k tail j r snapshots
local notation "start" => (phase).stop earlyFloor
local notation "shelf" => (spec).scanPages ((cal).packetEnd start) q
local notation "census" => (shelf).stop
local notation "paid" => fun x : Fin (spec).scalar.blocks => (out).terminalPaid origin x.val
local notation "actor" => fun x : Fin (spec).scalar.blocks => (out).terminalActor origin x.val
local notation "wing" => fun (x : Fin (spec).scalar.blocks) (a : Fin (2*(spec).cap)) => (out).terminalWing origin x.val a.val

/-- The genuine last reset allocates all retained source banks before the census.
The destination mask bound also fits the preceding deterministic replay. -/
theorem last_bank_placement {w : ℕ}
    (base : S.baseGroups = 2^tail) (last : age+1 = S.length) (oldK : previous.k = k)
    (priorMetadata : (out).metadataEnd origin ≤ earlyFloor)
    (maskRoom : (spec).maskBase census < 2^w) :
    (spec).Before census paid actor wing ((out).terminalPeer origin)
      (shelf).total (shelf).modulo ((cal).homes start) (shelf).boundaries ∧
    (∀ x, (spec).scalar.shops ≤ (paid x).size) ∧
    (∀ x a, (spec).scalar.shops ≤ (wing x a).size) ∧
    (∀ x, (spec).scalar.shops ≤ (actor x).size) := by
  have fromFloor : earlyFloor ≤ start := by
    have rows : 0 < 2 ^ Nat.clog 2 ((out).receiver.blocks * (out).receiver.hosts) := Nat.two_pow_pos _
    unfold Phase.stop DescentTerminalCompiledPrefix.AddressPlan.sliceStop DescentTerminalSliceShelf.fence
      DescentTerminalSliceShelf.stage DescentTerminalPointerDigits.Gather.rom DescentOperandStateBanks.guard
    omega
  have replayFits : (cal).stop census < 2^w := by
    change (spec).cohortEnd census < 2^w
    obtain ⟨a,b,c,d,e,f,g,h,i⟩ := (spec).layers census
    exact (a.trans (b.trans (c.trans (d.trans (e.trans (f.trans (g.trans (h.trans i)))))))).trans_lt maskRoom
  exact scheduled_scan_before X G S k g p tail q drift op headerRows paidRows j r snapshots
    start board age f degree payload ordinary (S.firstWidth G.b p) (S.grainAt G.b p 0)
    operandLanes primitiveLanes previous addr roster floor base last oldK (priorMetadata.trans fromFloor) replayFits

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
