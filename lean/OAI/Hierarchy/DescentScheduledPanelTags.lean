import OAI.Hierarchy.DescentNamedTaggedOperandPanels
import OAI.Hierarchy.DescentScheduledArchivePanels
import OAI.Hierarchy.DescentNamedPanelPublicCapacity

namespace OAI
/-! # Seven attained reset fields after the registered predecessor and its own public menu -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSixParty DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentPackedColony DescentBundleHistory DescentSIMDLookup DescentResetGates
open DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
open DescentPackedZip DescentOrdinaryHostPad DescentRetainedRangeDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (p drift degree payload w : ℕ) (ordinary : ℕ→Dated.Ordinary)
    (seats profile : ℕ→ℕ) (header : ℕ) (cursor : Position)
local notation "op" => RotorSpec.ofRates ctl
local notation "s₀" => S.firstWidth G.b p
local notation "Z₀" => S.grainAt G.b p 0
local notation "board" => ctl.board
local notation "old" => cursor.ports.venue
local notation "io" => cursor.ports.io
local notation "cap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "oldExp" => NativePitch.resetCut S k tail p f payload age
local notation "nextM" => NativePitch.incoming S k tail p f payload ordinary (age+1)
local notation "oldL" => cursor.ports.operandLanes
local notation "roleL" => cursor.ports.roleLanes
local notation "token" => DescentPrimitivePalette.printedBits G s₀ Z₀ op
local notation "rcut" => receiverCut G S board k tail age p f g drift degree payload oldExp nextM (op).C (op).w
  oldL roleL token old
local notation "base" => cursor.ports.priorStart k cursor.floor
local notation "history" => (cursor.ports.afterPad k cursor.floor).archive
local notation "outer" => scheduledAtPorts G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor
local notation "a" => (outer).inner
local notation "v" => (a).successor
local notation "HH" => S.hostSize age
local notation "fits" => scheduled_cut_origin G S board k tail age p f g drift degree payload ordinary op s₀ Z₀ oldL roleL old
local notation "priorFits" => preceding_cut S k tail p f payload age
local notation "publisher" => priorArchivePhase G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w
variable (capacity : cursor.ports.venue.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)
    (space : ScheduledCodeRoom G S ctl.board k tail age p f g drift degree payload ordinary (RotorSpec.ofRates ctl)
      (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports.operandLanes cursor.ports.roleLanes
      cursor.ports.venue cursor.ports.io (cursor.ports.priorStart k cursor.floor) w (cursor.ports.afterPad k cursor.floor).archive)
local notation "u" => DatePorts.resetInputs G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w space

local notation "ports" => cursor.ports
local notation "mem₁" m:arg => (publisher).image m
variable {description : BitDescription W} {R : ℕ} (number : Local description)
  (bounds : DatePorts.RangeRoom cursor.ports input description) (shape : WorldShape p R description)
  (label : NodeOrder.All description→Label G (S.firstWidth G.b p) (S.grainAt G.b p 0) (RotorSpec.ofRates ctl))

local notation "phase" => (a).ingress.phase base w (io).hubs (fun x=>(io).atoms x.val)
  (fun j=>(io).wire j.1.val j.2.val)
local notation "atMem" m:arg => (phase).image (mem₁ m)
local notation "menuRows" => DateInputs.PublicOperandRowsAt (B:=B) drift degree payload rcut oldExp (2^rcut) nextM oldL roleL token old io base w
  fits fits priorFits (history).count (history).nodeBase (history).arguments (history).seed
  (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space)

theorem registered_panel_tags (m : Memory w) (degreeAt : (old).degree=D) (capAt : input.placement.cap=cap)
    (ready : (u).Ready) (homes : (old).hosts=HH) (blocks : (old).k=k)
    (groups : (old).groups=S.groupCount age) (widths : DatePorts.ArchiveWidths G S (RotorSpec.ofRates ctl) cursor.ports k tail p drift degree payload age)
    (args : (ports).argumentsPerNode=(if age=0 then 3*(s₀/p) else S.retainedArgumentsAt G drift))
    (held : RegisteredOperandPanels B p drift degree payload w ordinary cursor space number bounds shape label m
      degreeAt capAt ready homes blocks groups widths args)
    (menus : ∃dst : Memory w,(u).ThroughActors (atMem m) dst ∧ menuRows ready dst)
    (small : 2*(v).receiver.candidates<2^(v).receiver.queryBits) :
    ∃dst : Memory w,(u).ThroughActors (atMem m) dst ∧ (u).TaggedOrdinals ready small dst:=by
  obtain ⟨_,_,_,original⟩:=held
  obtain ⟨dst,exec,_,tags⟩:=DateInputs.tagged_from_operand_panels (B:=B) drift degree payload rcut oldExp (2^rcut)
    nextM oldL roleL token old io base w fits fits priorFits (history).count (history).nodeBase (history).arguments
    (history).seed (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space) degreeAt capAt ready (mem₁ m) _ original
  obtain ⟨other,previous,reads⟩:=menus
  have eqn : other=dst:=exec_unique _ _ _ _ previous exec
  exact ⟨dst,exec,tags (eqn ▸ reads)⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
