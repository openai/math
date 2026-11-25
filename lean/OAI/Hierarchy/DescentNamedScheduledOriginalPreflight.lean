import OAI.Hierarchy.DescentNamedOriginalPreflight
import OAI.Hierarchy.DescentTerminalDatedScanBefore
import OAI.Hierarchy.DescentNamedOriginalReplayRead

namespace OAI
/-! The terminal prefix with one public scheduled reset, its actual retained venue banks,
and the fixed, deterministic replay. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentMixedRouter Catalyst DescentInitialHost DescentExteriorReplay
open DescentTerminalPreflightSpace DescentTerminalFixedSlices DescentTerminalPrimitiveArena
open DescentTerminalPointerDigits DescentTerminalCombinedRole DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.Routing CallPool
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] originalPreflight originalPreflightMemory originalPreflightClocks
set_option maxHeartbeats 800000

variable {F:Type} [Field F] {cp ar:ℕ} (X:Approximation F cp ar) (G:PoweredGadget F) (S:AtomSchedule)
  {k tail:ℕ} (baseGroups:S.baseGroups=2^tail) (radix:S.radix=2^k)
  (g p q drift:ℕ) (op:RotorSpec) (headerRows paidRows:ℕ)
local notation "spec" => preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
local notation "ports" => Fintype.card (Port ar X.width)

open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentResetInvoice CorrectionBatch
variable {n deg : ℕ} (board : NonlinearExpanders.Graph n deg) (age f degree payload : ℕ)
  (ordinary : ℕ→Dated.Ordinary) (operandLanes primitiveLanes : ℕ)
  (previous : StageVenueTail.Date) (addr : ℕ→ℕ→Bank) (oldRoster : Bank) (floor : ℕ)
  (j r t base compact : ℕ) (tag : ℕ→Bool) (rotation : ℕ→ℕ) (A : Snapshots k) (roleBase : ℕ)
local notation "phase" => Phase.scheduled G S board k tail age p f g drift degree payload ordinary op
  operandLanes primitiveLanes previous addr oldRoster floor
local notation "output" => (phase).output
local notation "origin" => (phase).dateBase
local notation "s₀" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "dated" => PhysicalReset.scheduled G S board k tail age p f g drift degree payload ordinary op
  s₀ Z operandLanes primitiveLanes previous addr oldRoster floor
local notation "cal" => replayCalendar X S k tail j r A
local notation "early" => DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t ports
local notation "image₀" => DescentExteriorMatrixUpdate.Calendar.earlyImage S k tail base tag rotation j r t ports compact
local notation "slices" => (phase).stop early
local notation "packet" => (cal).packetEnd slices
local notation "shelf" => (spec).scanPages packet q
local notation "census" => (shelf).stop
local notation "D" => (output).venue.next
local notation "hw" => (output).receiver
local notation "H" => (spec).scalar.shops
local notation "bs" => (spec).scalar.blocks
local notation "blocks" => (rfl : bs=(hw).blocks)
local notation "paid" => fun x:Fin bs=>(output).terminalPaid origin x.val
local notation "actor" => fun x:Fin bs=>(output).terminalActor origin x.val
local notation "wing" => fun (x:Fin bs) (a:Fin (2*(spec).cap))=>(output).terminalWing origin x.val a.val
local notation "peer" => (output).terminalPeer origin
/-- The dated matrix tables begin at or above the public base. -/
theorem scheduled_base_le_early (S : AtomSchedule) (k tail base j r t portCount : ℕ) :
    base ≤ DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t portCount := by
  unfold DescentExteriorMatrixUpdate.Calendar.earlyEnd DescentExteriorMatrixUpdate.Calendar.earlyAt
    DescentExteriorMatrixUpdate.Calendar.stop DescentExteriorMatrixUpdate.Calendar.tableAt
  omega

/-- Address immediately beyond the scheduled preflight census. -/
abbrev scheduledPreflightStop := (cal).stop census
variable {w : ℕ} (room : scheduledPreflightStop X G S (tail:=tail) g p q drift op headerRows paidRows
  board age f degree payload ordinary operandLanes primitiveLanes previous addr oldRoster floor j r t base A < 2^w)
local notation "code" => originalPreflight X G S baseGroups radix g p q drift op headerRows paidRows
  j r t base compact tag rotation (phase) A blocks roleBase peer paid actor wing room
local notation "dst" => originalPreflightMemory X G S baseGroups radix g p q drift op headerRows paidRows
  j r t base compact tag rotation (phase) A blocks roleBase peer paid actor wing room
local notation "ticks" => originalPreflightClocks X G S (k:=k) (tail:=tail) g p q drift op headerRows paidRows j r t
  base (phase) A blocks peer paid actor wing room
local notation "colors" => DescentPrimitivePalette.colors G s₀ Z op
local notation "args" => NativeBranch.privateSlotCapacity G S drift
local notation "roleBits" => fun f:Fin 6=>DescentTerminalCombinedRole.width colors (max 8 (2^S.capGain))
  args p drift f*(S.epochPower^S.localTokenExponent)*(spec).groups

/-- The instruction stream contains no branch-specific choice of terminal input banks. -/
def scheduledOriginalCPU : Procedure w := code

def scheduledOriginalMemory (m : Memory w) := dst m
def scheduledOriginalClocks := ticks

variable (last : age+1=S.length) (oldK : previous.k=k)
  (word : (preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)).maskBase (((preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)).scanPages
    ((replayCalendar X S k tail j r A).packetEnd ((Phase.scheduled G S board k tail age p f g drift degree payload ordinary op
      operandLanes primitiveLanes previous addr oldRoster floor).stop
      (DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t (Fintype.card (Port ar X.width))))) q).stop)<2^w) (positive : 0<w) (alive : 0<(preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)).scalar.shops)
  (prev : ∀i<S.length,rotation i<base) (seed : compact+32*DescentExteriorShelf.span j r t (Fintype.card (Port ar X.width))≤base)
  (earlier : (PhysicalReset.scheduled G S board k tail age p f g drift degree payload ordinary op
    (S.firstWidth G.b p) (S.grainAt G.b p 0) operandLanes primitiveLanes previous addr oldRoster floor).fullEnd floor≤(DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t (Fintype.card (Port ar X.width))))
  (signedPitch : (Phase.scheduled G S board k tail age p f g drift degree payload ordinary op
      operandLanes primitiveLanes previous addr oldRoster floor).output.venue.next.signedLanes=S.groupCount S.length)
  (rank : ∀t<S.length,∀b,A.compact t=some b→b.Fits w base)
  (roleEnd : roleBase+DescentTerminalRoleTables.count (fun f:Fin 6 => DescentTerminalCombinedRole.width (DescentPrimitivePalette.colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op) (max 8 (2^S.capGain))
    (NativeBranch.privateSlotCapacity G S drift) p drift f*(S.epochPower^S.localTokenExponent)*(preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)).groups)≤base)

include last oldK word positive alive prev seed earlier signedPitch rank roleEnd in
/-- Execute the entire named terminal prefix on every input. The physical predecessor is the
real last reset; all source sizes, addresses, and transported lanes are derived here. -/
theorem scheduled_original_preflight (m : Memory w) :
    ((code).Exec m (dst m) ticks ∧ CheapCode code ∧
      (∀a,a<base ∨ (spec).maskBase census≤a → dst m a=m a) ∧ (shelf).Reads (dst m)) ∧
    (∀a<packet,dst m a=(cal).memory slices census room ((phase).memory early (image₀ m)) a) ∧
    (∀a<slices,dst m a=(phase).memory early (image₀ m) a) ∧
    (∀f (b:Fin (hw).blocks) (h:Fin (hw).hosts),
      dst m (((phase).banks early f).base+(finProdFinEquiv (b,h)).val)=
        (((phase).write f (DescentTerminalSliceShelf.seen (phase).chart (image₀ m) b h)).val:Word w)) ∧
    ∀i:Fin (cal).packets,((cal).homes slices).read (dst m) (i.val:Word w)=
      ((cal).homes slices).read ((cal).memory slices census room ((phase).memory early (image₀ m))) (i.val:Word w) := by
  have before : early≤ slices:=by
    unfold Phase.stop DescentTerminalCompiledPrefix.AddressPlan.sliceStop DescentTerminalSliceShelf.fence
      DescentTerminalSliceShelf.stage DescentTerminalPointerDigits.Gather.rom DescentOperandStateBanks.guard
    simp only [Nat.add_assoc, Nat.le_add_right]
  have begins := scheduled_base_le_early S k tail base j r t ports
  obtain ⟨s₀',s₁,s₂,c₀,_⟩:=(cal).addresses slices census
  have lit:packet≤census:=Nat.le_add_right ..
  have atSnapshot:=begins.trans (before.trans s₀')
  have fitted : ∀t<S.length,∀b,A.compact t=some b→b.Fits w ((cal).scratch slices) := by
    intro t ht b here
    have h:=rank t ht b here
    exact ⟨h.1,h.2.1,h.2.2.trans atSnapshot⟩
  have roles : roleBase+DescentTerminalRoleTables.count roleBits≤(spec).cohortEnd census:=
    roleEnd.trans (atSnapshot.trans (s₁.trans (s₂.trans (lit.trans c₀))))
  have booked:=scheduled_scan_before X G S k g p tail q drift op headerRows paidRows j r A
    slices board age f degree payload ordinary s₀ Z operandLanes primitiveLanes previous addr oldRoster floor
    baseGroups last oldK (earlier.trans before) room
  have chart:=Phase.scheduled_layout G S board k tail age p f g drift degree payload ordinary op
    operandLanes primitiveLanes previous addr oldRoster floor last
  have one:=Phase.scheduled_one G S board k tail age p f g drift degree payload ordinary op
    operandLanes primitiveLanes previous addr oldRoster floor last baseGroups signedPitch
  exact original_preflight_receipt X G S baseGroups radix g p q drift op headerRows paidRows j r t
    base compact tag rotation (phase) A blocks chart.2.1.symm roleBase peer paid actor wing room
    word positive alive prev seed earlier one fitted roles booked.1 booked.2.1 booked.2.2.1 m


section Selected
local notation "wireWidth" => S.epochPower^S.priceExponent
local notation "rate" => (1/((s₀:ℝ)*(wireWidth:ℝ)):ℝ)
local notation "err" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
variable {h C₀ R : ℕ} {he : 0≤(((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {hu : 0≤(1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ)*((S.epochPower^S.priceExponent):ℝ)}
  {epoch : Epochs G hu he (h:=h) (C:=C₀) (Ht:=GroupStage.depthBound (atRound S.rounds) n f g)
    (t:=S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
  {c : (Epochs.finish G hu he epoch).Choice} (b : Branch X G S radix R epoch c) (hp : 0<p)
  (width : S.groupWidth k tail 0+k=j+(j+r))

include last oldK word positive alive prev seed earlier signedPitch roleEnd in
/-- On a selected branch, the output of the entire fixed prefix contains the true
terminal home of every public packet at its numeric address. -/
theorem scheduled_original_homes (m : Memory w) (rows : b.path.snapshotRanks A base m)
    (labels : b.path.snapshotLabels A) (hostFit : ∀i<S.length,S.hostSize i≤A.hosts i)
    (kept : j≤S.groupWidth k tail S.length+k) (bits : (k*S.length+1)*2^(8+S.capGain*S.length)≤w)
    (i : Fin (ports*2^(j+r))) :
    ((cal).homes slices).read (dst m) (i.val:Word w)=((publicHost X G S b hp baseGroups width i).val:Word w) := by
  have run:=scheduled_original_preflight X G S baseGroups radix g p q drift op headerRows paidRows
    board age f degree payload ordinary operandLanes primitiveLanes previous addr oldRoster floor j r t
    base compact tag rotation A roleBase room last oldK word positive alive prev seed earlier signedPitch
    (b.path.snapshot_rank_rooms A base m rows) roleEnd m
  have one:=Phase.scheduled_one G S board k tail age p f g drift degree payload ordinary op
    operandLanes primitiveLanes previous addr oldRoster floor last baseGroups signedPitch
  have seen:=original_replay_from_dated X G S b hp baseGroups width A census (phase) base t compact tag
    rotation m room (Nat.le_add_right ..) hostFit rows labels positive prev seed earlier one kept
    alive bits
  exact (run.2.2.2.2 i).trans (seen.homes i)

end Selected
end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
