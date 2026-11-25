import OAI.Hierarchy.DescentPriorPackedPrimitivePage
import OAI.Hierarchy.DescentScheduledVenueOld
import OAI.Hierarchy.DescentPostedResetCheckpoints
import OAI.Hierarchy.DescentDatedInheritedRegister

namespace OAI
/-! # The inherited primitive words in the actual scheduled reset input -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony DescentSIMDLookup DescentOrdinaryHostPad DescentPrimitivePalette
open DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentPackedWalsh
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree payload : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (ports : Chronology.DatePorts) (floor w : ℕ)
local notation "s" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "old" => ports.venue
local notation "next" => ports.priorStart k floor
local notation "post" => ports.afterPad k floor
local notation "pack" => ports.resetPad k
local notation "a" => (scheduledAtPorts G S board k tail age p f gain drift degree payload ordinary op s Z ports floor).inner
local notation "move" => (a).successor.roleTransfer.transfer
local notation "retained" => (a).successor.setup.retained
local notation "padPhase" => priorArchivePhase G S board k tail age p f gain drift degree payload ordinary op s Z ports floor w
local notation "loaded" => previousArchiveLayout G S board k tail age p f gain drift degree payload ordinary op s Z ports floor
local notation "maxCap" => ((capCalendar G.b S.rounds gain S.height).take age).prod*256
local notation "support" => ScheduledCodeRoom G S board k tail age p f gain drift degree payload ordinary op s Z
  ports.operandLanes ports.roleLanes old ports.io next w (post).archive
variable (capacity : (old).cap=maxCap) (space : support)
local notation "finish" => DatePorts.resetFinalInputs G S board k tail age p f gain drift degree payload ordinary op s Z
  ports floor w capacity space
local notation "ingress" => (a).ingress
local notation "front" => (ingress).phase next w ports.io.hubs (fun x=>ports.io.atoms x.val)
  (fun j=>ports.io.wire j.1.val j.2.val)
local notation "start" => (a).stageStart next

variable {P : Type} {d₀ : ℕ} {bits : P→ℕ} {W : MarkedWorld F d₀ P bits} {q ε : ℝ} {z D wire hist : ℕ}
    (input : Reached W G q ε S k age z D wire hist) {B : BitDescription W} (order : Local B)
    (room : DatePorts.RangeRoom ports input B) {R : ℕ} (shape : WorldShape p R B)
    (label : NodeOrder.All B→Label G s Z op) (m : Memory w)
    (homes : (old).hosts=S.hostSize age) (blocks : (old).k=k) (groups : (old).groups=S.groupCount age)
    (widths : DatePorts.ArchiveWidths G S op ports k tail p drift degree payload age)
    (args : ports.argumentsPerNode=(if age=0 then 3*(S.firstWidth G.b p/p) else S.retainedArgumentsAt G drift))
    (data : (loaded).Values)
    (roles : Fin (2^k)→Fin ports.operandHosts→Fin (old).groups→Cell (ports.tokenBits*ports.nodes))
local notation "archive" => ScheduledOldAt G S board k tail age p f gain drift degree payload ordinary op s Z
  ports floor w space input m homes blocks groups widths args order room shape label data roles
local notation "tokens" => Reached.NodeCells.previousTokens input B order move rfl rfl
  (fun y=>token G s Z op (label y))
local notation "before" => (front).image ((padPhase).image m)

/-- All physical source words of the retained role mover, with their bounds and
capacity, on the very memory from which the operand and output programs run. -/
theorem scheduled_inherited_tokens (stored : archive) (native : ports.ArchiveFits k floor)
    (ready : 0<ports.roleLanes)
    (hubFit : ports.io.hubs.Fits w floor)
    (atomFit : ∀x : Fin (2^(ingress).k),(ports.io.atoms x.val).Fits w floor)
    (wireFit : ∀j : (ingress).signed.Slot,(ports.io.wire j.1.val j.2.val).Fits w floor)
    (endRoom : start<2^w) :
    (∀j,(move).hosts*chunks (move).groups (move).previousLanes≤((finish).previousRoles j).size) ∧
    (∀j,((finish).previousRoles j).Fits w start) ∧
    ∀j,Reads ((finish).previousRoles j) (tokens j) (move).previousLanes before:=by
  have priorCut:=ports.pad_order k floor
  have low:=priorCut.1.trans priorCut.2
  have higher : next≤ start:=(ingress).after next
  have padRoom:=higher.trans_lt endRoom
  have room₀:=low.trans_lt padRoom
  have safe : ∀j,(ports.archive.prior loaded j).Fits w floor:=
    (loaded).prior_registers ports.archive.seed ports.archive.nodeBase ports.archive.arguments floor w
      (native.data retained).1 (native.data retained).2 room₀
  have previous (j : Fin (2^k)) : (ports.archive.roles.bank j.val).Fits w floor:=
    ports.archive.roles.fits w floor j.val (j.isLt.trans_le native.blocks) native.roles room₀
  have incoming:=ports.full_pad_reads k floor (ports.archive.prior loaded) (fun j=>ports.archive.roles.bank j.val)
    m safe previous padRoom ready data roles stored.1 stored.2.1
  have roleBounds (j : Fin (move).blocks) :=
    (pack).role_fit floor (priorCut.2.trans_lt padRoom) j
  have extent : (move).hosts=(old).hosts:=homes.symm
  have cohort : (move).groups=(old).groups:=groups.symm
  have nodes : (move).previousNodes=ports.nodes:=widths.nodes.symm
  have countRoom (j : Fin (move).blocks) :
      (move).hosts*chunks (move).groups (move).previousLanes≤((finish).previousRoles j).size:=by
    change (move).hosts*chunks (move).groups ports.roleLanes≤((pack).roleBank floor j).size
    rw [extent,cohort]
    exact (roleBounds j).2
  have inside (j : Fin (move).blocks) : ((finish).previousRoles j).Fits w next:=by
    obtain ⟨fit,_⟩:=roleBounds j
    exact ⟨fit.1,fit.2.1,fit.2.2.trans priorCut.2⟩
  have lift {b : Bank} (fits : b.Fits w floor) : b.Fits w next:=⟨fits.1,fits.2.1,fits.2.2.trans low⟩
  have preserve:=((ingress).any next ports.io.hubs _ _ ((padPhase).image m) (lift hubFit)
    (fun x=>ProtocolRAMGeneratedWrite.fits_mono _ low (atomFit x)) (fun j=>lift (wireFit j)) endRoom).2
  refine ⟨countRoom,fun j=>⟨(inside j).1,(inside j).2.1,(inside j).2.2.trans higher⟩,?_⟩
  intro j
  have labeled:=DatePorts.padded_token_read (room:=room) (label:=label) move rfl rfl extent nodes rfl rfl
    widths.token j ((finish).previousRoles j) ((padPhase).image m) (roles j) (stored.2.2.1 j) (incoming.2.2 j)
  intro pos
  have atBase : ((finish).previousRoles j).base+(row _ _ _ pos).val<next:=
    (Nat.add_lt_add_left ((row _ _ _ pos).isLt.trans_le (countRoom j)) _).trans_le (inside j).2.2
  exact (preserve _ (.inl atBase)).trans (labeled pos)

open DescentOperandStateBanks

include homes blocks groups widths args in
/-- Starting with the previous chronological archive, obtain all three operands
of the inherited-register theorem without providing separate role words. -/
theorem scheduled_archive_inherited_tokens
    (seen : ports.held input floor m) (counted : ports.archive.count.base<floor)
    (wires : ports.WireRoom w floor) (capAt : (old).cap=input.placement.cap)
    (native : ports.ArchiveFits k floor) (ready : 0<ports.roleLanes)
    {ptr : NodeOrder.All B→ℕ→Pointer}
    {flags : Fin (2^(old).k)→Fin ports.nodes→Fin ports.operandHosts→Fin (old).groups→ℕ}
    (actual : DatePorts.ArchiveRead ports input B order room shape op label ptr flags m) (sized : ports.RoleRows)
    (hubFit : ports.io.hubs.Fits w floor)
    (atomFit : ∀x : Fin (2^(ingress).k),(ports.io.atoms x.val).Fits w floor)
    (wireFit : ∀j : (ingress).signed.Slot,(ports.io.wire j.1.val j.2.val).Fits w floor)
    (endRoom : start<2^w) :
    (∀j,(move).hosts*chunks (move).groups (move).previousLanes≤((finish).previousRoles j).size) ∧
    (∀j,((finish).previousRoles j).Fits w start) ∧
    ∀j,Reads ((finish).previousRoles j) (tokens j) (move).previousLanes before:=by
  obtain ⟨values,names,source⟩:=scheduled_venue_archive_witness G S board k tail age p f gain drift degree payload
    ordinary op s Z ports floor w space input m seen counted wires homes blocks capAt groups native
    (((ingress).after next).trans_lt endRoom) ready widths args actual widths.token sized
  exact scheduled_inherited_tokens G S board k tail age p f gain drift degree payload ordinary op ports floor w
    capacity space input order room shape label m homes blocks groups widths args values names source native ready
    hubFit atomFit wireFit endRoom

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
