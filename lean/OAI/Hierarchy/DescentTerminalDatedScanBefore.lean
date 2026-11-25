import OAI.Hierarchy.DescentTerminalLastVenueShape
import OAI.Hierarchy.DescentStageVenueWireRoom
import OAI.Hierarchy.DescentTerminalResetBanks
import OAI.Hierarchy.DescentTerminalFundedPreflight
import OAI.Hierarchy.DescentNamedPreflightFormat
import OAI.Hierarchy.DescentNamedReplayCalendar
import OAI.Hierarchy.DescentWalshDyadicChosen

namespace OAI
/-! The paid, occupancy, cable and sorted-neighbor banks actually allocated by the last
reset, together with the physical public-packet bank in the fixed replay. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSixParty DescentSIMDLookup ProtocolRAM
noncomputable section
set_option quotPrecheck false

variable (v : ResetOutput) (base : ℕ)
local notation "V" => v.venue
local notation "d" => (V).next
local notation "fund" => v.fundedEnd base
local notation "loc" => (V).venueStart fund

def terminalPaid (x : ℕ) : Bank :=
  DescentVenueSlabs.page (d).paidShape ((d).firstEnd loc) (if x<2^(d).k then x else 0)

/-- One page per block, with one occupancy bit per group on each host. -/
def terminalActor (x : ℕ) : Bank :=
  DescentVenueSlabs.page (d).aliveShape ((d).secondEnd loc) x

def terminalWing (x j : ℕ) : Bank :=
  DescentVenueSlabs.page (d).signedShape loc (x*(2*(d).cap)+j)

def terminalPeer : Bank :=
  DescentCompactVenuePeers.peers ((V).peerStart fund) (V).rawHosts (V).dense.hosts

/-- These four functions are the actual successor venue's pages before its later actor-mask
reduction. The latter also leaves the per-block one-bit pages resident. -/
theorem terminal_venue_banks (prior : ResetVenue.Earlier) (x j : ℕ) :
    let entered:=(V).sources prior fund
    let b:=(d).transported entered loc
    b.paid x=v.terminalPaid base x ∧ b.alive x=v.terminalActor base x ∧
      ((d).operands entered loc).wire x j=v.terminalWing base x j ∧
      ((d).operands entered loc).roster=v.terminalPeer base := ⟨rfl,rfl,rfl,rfl⟩

theorem terminal_paid_room {w : ℕ} (fit : v.fullEnd base<2^w) (x : Fin (2^(d).k)) :
    (v.terminalPaid base x.val).base+(v.terminalPaid base x.val).size≤v.fullEnd base ∧
      (d).hosts*chunks (d).groups (d).lanes≤(v.terminalPaid base x.val).size := by
  obtain ⟨_,_,after_,last_⟩:=(d).order loc
  have high: (d).secondEnd loc≤v.fullEnd base:=after_.trans last_
  have row:=DescentVenueSlabs.page_room (d).paidShape ((d).firstEnd loc) w x (high.trans_lt fit)
  simp only [terminalPaid, x.isLt, ↓reduceIte]
  exact ⟨row.1.2.2.trans high, row.2⟩

theorem terminal_actor_room {w : ℕ} (fit : v.fullEnd base<2^w) (x : Fin (2^(d).k)) :
    (v.terminalActor base x.val).base+(v.terminalActor base x.val).size≤v.fullEnd base ∧
      (d).hosts*chunks (d).groups (d).lanes≤(v.terminalActor base x.val).size := by
  have high: (d).thirdEnd loc≤v.fullEnd base:=((d).order loc).2.2.2
  have row:=DescentVenueSlabs.page_room (d).aliveShape ((d).secondEnd loc) w x (high.trans_lt fit)
  exact ⟨row.1.2.2.trans high,row.2⟩

theorem terminal_wing_room {w : ℕ} (fit : v.fullEnd base<2^w) (x : Fin (2^(d).k)) (j : Fin (2*(d).cap)) :
    (v.terminalWing base x.val j.val).base+(v.terminalWing base x.val j.val).size≤v.fullEnd base ∧
      (d).hosts*chunks (d).groups (d).lanes≤(v.terminalWing base x.val j.val).size := by
  have high : (d).firstEnd loc≤v.fullEnd base :=
    ((d).order loc).2.1.trans (((d).order loc).2.2.1.trans ((d).order loc).2.2.2)
  let index : Fin (d).signedShape.pages:=finProdFinEquiv (x,j)
  have address:index.val=x.val*(2*(d).cap)+j.val:=by
    simp [index,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
  have row:=DescentVenueSlabs.page_room (d).signedShape loc w index (high.trans_lt fit)
  rw [address] at row
  exact ⟨row.1.2.2.trans high,row.2⟩

theorem terminal_peer_room : (v.terminalPeer base).base+(v.terminalPeer base).size≤v.fullEnd base ∧
    3*(V).dense.hosts≤(v.terminalPeer base).size := by
  have old : (v.terminalPeer base).base+(v.terminalPeer base).size≤loc := by
    change (v.terminalPeer base).base+DescentCompactVenuePeers.span (3*(V).dense.hosts)≤
      ((v.terminalPeer base).base+DescentCompactVenuePeers.span (3*(V).dense.hosts))+
        DescentCompactVenuePeers.span (V).dense.hosts
    exact Nat.le_add_right ..
  have ord:loc≤v.fullEnd base:=by rw [show v.fullEnd base=(d).endAddress loc from rfl,(d).translates loc];omega
  exact ⟨old.trans ord,(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler Catalyst DescentExteriorReplay DescentDatedAddressBook DescentTerminalPreflightSpace
open DescentSIMDLookup DescentTerminalPointerDigits ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F:Type} [Field F] {cp ar:ℕ} (X:Approximation F cp ar) (G:PoweredGadget F) (S:AtomSchedule)
  (k g p tail q drift:ℕ) (op:RotorSpec) (headerRows paidRows j r:ℕ) (snapshots:Snapshots k)
  (v:ResetOutput) (dateBase start:ℕ)
local notation "spec" => preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
local notation "cal" => replayCalendar X S k tail j r snapshots
local notation "d" => v.venue.next
local notation "Gs" => S.groupCount S.length
local notation "H" => S.hostSize S.length
local notation "cap" => (capCalendar G.b S.rounds g S.height).prod*256
local notation "shelf" => (spec).scanPages ((cal).packetEnd start) q
local notation "census" => (shelf).stop
local notation "pay" => fun x:Fin (2^k)=>v.terminalPaid dateBase x.val
local notation "act" => fun x:Fin (2^k)=>v.terminalActor dateBase x.val
local notation "wing" => fun (x:Fin (2^k)) (s:Fin (2*cap))=>v.terminalWing dateBase x.val s.val

/-- The earlier source conditions for the purchased terminal schedule, from the last date's
actual bank dimensions. Both the source field bank and the destination public-home bank
have their full dyadic allocation inside the proven address boundaries. -/
theorem dated_scan_before {w : ℕ} (base : S.baseGroups=2^tail)
    (shape : (d).k=k ∧ (d).hosts=H ∧ (d).groups=Gs ∧ (d).cap=cap ∧ (d).lanes=Gs)
    (earlier : v.metadataEnd dateBase≤ start) (word : (cal).stop census<2^w) :
    (spec).Before census pay act wing (v.terminalPeer dateBase) (shelf).total (shelf).modulo
      ((cal).homes start) (shelf).boundaries ∧ (∀x,H≤(pay x).size) ∧
      (∀x j,H≤(wing x j).size) ∧ (∀x,H≤(act x).size) := by
  obtain ⟨ik,shops,groups,sockets,lanes⟩:=shape
  obtain ⟨a,b,c,e,_⟩:=(cal).addresses start census
  have lit : (cal).packetEnd start≤census:=Nat.le_add_right ..
  have first : v.fullEnd dateBase≤ start :=
    (v.terminal_order dateBase).2.1.trans ((v.terminal_order dateBase).2.2.trans earlier)
  have end_ : v.fullEnd dateBase≤(spec).cohortEnd census:=first.trans (a.trans (b.trans (c.trans (lit.trans e))))
  have room : v.fullEnd dateBase<2^w:=end_.trans_lt word
  have final : Gs=2^tail:=by simp [AtomSchedule.groupCount,base]
  have one : chunks Gs Gs=1:=by
    rw [final]
    simpa only [chunks,Nat.sub_self,pow_zero] using DescentWalshDyadicBudget.exact_batch tail tail le_rfl
  have P₀ (x : Fin (2^k)) :
      (pay x).base+(pay x).size≤(spec).cohortEnd census ∧ H*chunks Gs Gs≤(pay x).size := by
    have z:=v.terminal_paid_room dateBase room ⟨x.val,by simpa only [ik] using x.isLt⟩
    exact ⟨z.1.trans end_,by simpa only [shops,groups,lanes] using z.2⟩
  have A₀ (x : Fin (2^k)) :
      (act x).base+(act x).size≤(spec).cohortEnd census ∧ H*chunks Gs Gs≤(act x).size := by
    have z:=v.terminal_actor_room dateBase room ⟨x.val,by simpa only [ik] using x.isLt⟩
    exact ⟨z.1.trans end_,by simpa only [shops,groups,lanes] using z.2⟩
  have W₀ (x : Fin (2^k)) (s : Fin (2*cap)) :
      (wing x s).base+(wing x s).size≤(spec).cohortEnd census ∧ H*chunks Gs Gs≤(wing x s).size := by
    have z:=v.terminal_wing_room dateBase room ⟨x.val,by simpa only [ik] using x.isLt⟩
      ⟨s.val,by simpa only [sockets] using s.isLt⟩
    exact ⟨z.1.trans end_,by simpa only [shops,groups,lanes] using z.2⟩
  have homesBorder:((cal).homes start).base+((cal).homes start).size=(cal).packetEnd start:=rfl
  refine ⟨(spec).scan_before ((cal).packetEnd start) q census le_rfl pay act wing
    (v.terminalPeer dateBase) ((cal).homes start) (fun x=>(P₀ x).1) (fun x=>(P₀ x).2)
    (fun x=>(A₀ x).1) (fun x=>(A₀ x).2) (fun x s=>(W₀ x s).1)
    ((v.terminal_peer_room dateBase).1.trans end_) (homesBorder.le.trans (lit.trans e)),?_,?_,?_⟩
  · intro x
    simpa only [one,Nat.mul_one] using (P₀ x).2
  · intro x s
    simpa only [one,Nat.mul_one] using (W₀ x s).2
  · intro x
    simpa only [one,Nat.mul_one] using (A₀ x).2


section Scheduled
variable {n degree₀:ℕ} (board:NonlinearExpanders.Graph n degree₀)
    (age f degree height:ℕ) (ordinary:ℕ→DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary)
    (s Z operandLanes primitiveLanes:ℕ) (old:StageVenueTail.Date) (addr:ℕ→ℕ→Bank)
    (roster:Bank) (floor:ℕ)
local notation "machine" => PhysicalReset.scheduled G S board k tail age p f g drift degree height ordinary
  op s Z operandLanes primitiveLanes old addr roster floor
local notation "output" => (machine).successor
local notation "origin" => (machine).rebased ((machine).stageStart floor)
local notation "paidPages" => fun x:Fin (2^k)=>(output).terminalPaid origin x.val
local notation "actorPages" => fun x:Fin (2^k)=>(output).terminalActor origin x.val
local notation "wirePages" => fun (x:Fin (2^k)) (a:Fin (2*cap))=>(output).terminalWing origin x.val a.val

/-- Original final-date specialization. The stored pages and all calendar dimensions
are computed by the scheduled reset, including the last capacity multiplier. -/
theorem scheduled_scan_before {w : ℕ} (base : S.baseGroups=2^tail)
    (last : age+1=S.length) (blocks : old.k=k)
    (earlier : (output).metadataEnd origin≤ start) (word : (cal).stop census<2^w) :
    (spec).Before census paidPages actorPages wirePages ((output).terminalPeer origin)
      (shelf).total (shelf).modulo ((cal).homes start) (shelf).boundaries ∧
    (∀x,H≤(paidPages x).size) ∧ (∀x a,H≤(wirePages x a).size) ∧ (∀x,H≤(actorPages x).size) :=
  dated_scan_before X G S k g p tail q drift op headerRows paidRows j r snapshots (output) origin start base
    (PhysicalReset.scheduled_terminal_shape G S board k tail age p f g drift degree height ordinary op
      s Z operandLanes primitiveLanes old addr roster floor last blocks) earlier word

end Scheduled
end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
