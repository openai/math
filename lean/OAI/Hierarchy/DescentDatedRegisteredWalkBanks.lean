import OAI.Hierarchy.DescentDatedRetainedHeaderFrame
import OAI.Hierarchy.DescentDatedOperandPhysicalRead
import OAI.Hierarchy.DescentOrdinaryRegisteredRows

namespace OAI
/-! The raw and sorted four-hop row numbers read by the ordinary operand resolver. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPackedColony DescentPackedZip DescentSIMDLookup DescentHaloWalkRAM DescentRawCablePanel
open DescentDatedAddressBook DescentOrdinaryAtomFieldRAM DescentOperandVectorArena DescentOperandStateBanks
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1500000
set_option maxRecDepth 6000
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "P" => breadth (fmt).degree
private theorem cast_roster {m n : ℕ} (same : m=n) (p : Ports m) :
    (same ▸ p : Ports n).roster=p.roster:=by cases same;rfl

theorem ArgumentEntry.measured_roster (A : v.ArgumentEntry) (floor : ℕ) (mat : A.Match v floor)
    (pg : Fin v.vector.pageCount) (q : Fin v.vector.lows) :
    (((A.directory v floor mat).refs pg q).ports).roster=(A.ports v floor).roster:=by
  exact cast_roster mat.paths _

private theorem from_measured {H H' paths paths' groups M w : ℕ} {io : Ports paths}
    {old : Fin H→Fin paths→Option (Fin H)} {new_ : Fin H'→Fin paths'→Option (Fin H')}
    (hosts : H=H') (degrees : paths=paths') (same : HEq old new_) {m : Memory w}
    (source : Mounted io (DescentSortedRoster.indexed old) m groups M) :
    ∀h p,m (io.roster.base+(Ranks.id h p).val)=(number (DescentSortedRoster.indexed new_ h p):Word w):=by
  subst H';subst paths'
  have order:=eq_of_heq same
  subst new_
  intro h p
  have addr : (Ranks.id h p).val=h.val*paths+p.val:=by
    simp [Ranks.id,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
  rw [addr]
  exact source.roster h p

variable (floor : ℕ) (A : v.ArgumentEntry) (mat : A.Match v floor)
local notation "vec" => v.vectorStart floor
local notation "hi" => v.operandHeaderEnd floor
local notation "lo" => v.donorEnd floor
local notation "start" => v.materialStart floor
local notation "refs" => (A.directory v floor mat).refs
variable {w : ℕ} (pg : Fin v.vector.pageCount) (q : Fin v.vector.lows)
    (safe : v.OperandHeaderRoom floor A mat (A.directory v floor mat).refs ((A.directory v floor mat).refs pg) w)
    (adj parts : Bank) (m paid : Memory w)
    (pre : PriorHeader.Room adj v.material.oldHosts v.material.groups v.material.lanes (v.ticket.depotShape v.short).degree (v.donorEnd floor) w)
local notation "first" => PriorHeader.image (e).oldHosts (e).groups (e).lanes (fmt).degree lo adj m
local notation "state" => (v.materialAt start parts (v.operandRanks floor).reverseRank w).image first
local notation "here" => (v.toOperandHeaders floor A mat refs (refs pg) safe).image paid

include pre in
theorem registered_walk_banks (c : v.SignedChart)
    (bill : v.MaterialRoom start parts (v.operandRanks floor).reverseRank w)
    (R : Fin (e).oldHosts→Fin (fmt).degree→Option (Fin (e).oldHosts))
    (prior : ∀h j,m (adj.base+h.val*(fmt).degree+j.val)=(number (R h j):Word w))
    (saved : ∀a,a<(e).endAddress start→here a=state a)
    {H G n M nb mb a : ℕ}
    (V : ScalarOperand.Values v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity H G a nb mb)
    (measured : ScalarOperand.Measured (refs pg q) V n M vec (A.mountedTape v floor paid))
    (hosts : H=(e).oldHosts) (degrees : breadth v.reference.degree=P)
    (walks : HEq V.walks (Gather.reaching R)) :
    v.WalkBanks floor A (Gather.reaching R) hi here:=by
  have frames:=v.operand_header_frames floor A mat refs (refs pg) safe paid
  have startEq : start=PriorHeader.endAddress (e).oldHosts (e).groups (e).lanes (fmt).degree lo:=by rw [←c.degree];rfl
  have materialOrder : start≤(e).endAddress start:=by
    rw [MaterialExtent.translated];exact Nat.le_add_right ..
  have payroll:=v.signed_stage_paid floor
  have signedToHeader:=frames.1.order
  have startToHeader : start≤hi:=
    materialOrder.trans (payroll.2.1.trans (payroll.2.2.trans signedToHeader))
  have fit:=PriorHeader.at_bank (e).oldHosts (e).groups (e).lanes (fmt).degree lo (P+15) (P+20) (by omega) pre.roof
  have visitsFit : (v.operandRanks floor).endpoints.Fits w hi:=
    ⟨fit.1,fit.2.1,fit.2.2.trans (startEq.symm.le.trans startToHeader)⟩
  have lim:=PriorHeader.limits (e).oldHosts (e).groups (e).lanes (fmt).degree
  have material:=v.material_any bill first
  have hold (a : ℕ) (prior_ : a<start) : here a=first a:=
    (saved a (prior_.trans_le materialOrder)).trans (material.2 a (.inl prior_))
  have directory:=PriorHeader.held_directory lo adj pre m R prior here (fun a low=>hold a (low.trans_le startEq.symm.le))
  have page:=measured.fromOld (0:Fin (2^v.reference.k))
  have bank:=A.measured_roster v floor mat pg q
  have rowSpace : (e).oldHosts*P≤(A.ports v floor).roster.size:=by
    rw [←hosts,←degrees,←bank]
    exact page.rosterRoom
  have sortedFit : (A.ports v floor).roster.Fits w vec:=by rw [←bank];exact page.roster
  refine ⟨visitsFit,⟨sortedFit.1,sortedFit.2.1,sortedFit.2.2.trans frames.2.1⟩,
    lim.2.2.1,rowSpace,pre.hosts,directory.visit,?_⟩
  intro h t
  have addr : (A.ports v floor).roster.base+(Ranks.id h t).val<vec:=
    (Nat.add_lt_add_left ((Ranks.id h t).isLt.trans_le rowSpace) _).trans_le sortedFit.2.2
  rw [frames.2.2 _ addr,←bank]
  exact from_measured hosts degrees walks measured.mounted h t

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
