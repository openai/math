import OAI.Hierarchy.DescentPhysicalResetDateOperands
import OAI.Hierarchy.DescentPhysicalJointRoom
import OAI.Hierarchy.DescentPhysicalStemOperand
import OAI.Hierarchy.DescentPhysicalTrunkRoom

namespace OAI
/-! # Space for the measured candidate metadata and the original ordinal columns -/
namespace Hierarchy.DescentDatedAddressBook
open DescentResetFieldAssembler DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

theorem CandidateSheets.meta_before_original (s : CandidateSheets) (r : ℕ) :
    s.metaEnd r≤ s.originalEnd r:=by
  have first:s.metaEnd r≤ s.inputDonorsEnd r:=by
    rw [s.donors_shift r, CandidateSheets.coordinateEnd, s.stemSources.extent (s.metaEnd r)]
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have second:s.inputDonorsEnd r≤ s.donorEnd r:=Nat.le_add_right ..
  have third:s.donorEnd r≤ s.publicFormatEnd r:=Nat.le_add_right ..
  have fourth:s.publicFormatEnd r≤ s.stemFormatEnd r:=Nat.le_add_right ..
  have fifth:s.stemFormatEnd r≤ s.privateArgsEnd r:=by
    unfold CandidateSheets.privateArgsEnd DescentUniformSlotOperands.stop DescentResetHaloBroadcast.endAt
    exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have sixth:s.privateArgsEnd r≤ s.original r:=Nat.le_add_right ..
  have last:s.original r≤ s.originalEnd r:=Nat.le_add_right ..
  omega

private theorem pair_bound {x y X Y : ℕ} (xlt : x<X) (ylt : y<Y):x*Y+y<X*Y:=
  (Nat.add_lt_add_left ylt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right Y xlt)

/-- Only genuine in-bounds slots are read in the original four-sector sheet,
including the last physical row before its successor. -/
theorem original_slot_space {w : ℕ} (base rows X K : ℕ) (x : Fin X) (j : Fin K)
    (top : DescentResetOriginalSlots.finish base rows X K<2^w) :
    (DescentResetOriginalSlots.bank base rows K x j).Fits w (DescentResetOriginalSlots.finish base rows X K):=by
  let stride:=DescentResetOriginalSlots.stride rows
  have lt:=pair_bound x.isLt j.isLt
  have stop:=Nat.mul_le_mul_right stride (Nat.succ_le_of_lt lt)
  rw [Nat.succ_mul] at stop
  change 0<stride ∧ stride<2^w ∧ (base+(x.val*K+j.val)*stride)+stride≤base+X*K*stride
  change base+X*K*stride<2^w at top
  exact ⟨Nat.two_pow_pos _,by omega,by omega⟩

namespace PhysicalReset.DateInputs
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "s" => (v).sheets
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "r" => ((v).remap b).endAddress
local notation "start" => (v).sheetsStart b
local notation "E" => (v).actorEnd b
local notation "scene" => (v).issuedScene b u.earlier

/-- The physical prefix pays for the compact roster and all earlier sources.
The named chart sets its sparse extent to the actor directory's true canvas. -/
theorem rank_rooms_of_roof
    (palette : 0<(v).front.peer.shapes) (sites : (v).front.peer.hosts≤((v).actor.directory ((v).middle.stop b)).sites)
    (matched : DescentResetCandidatePair.endAddress start (A).blocks
      (CandidateSheet.size u.sectors.stems u.sectors.contacts u.sectors.privates) u.sectors.pageBits=(v).candidateEnd b)
    (hosts : (A).hosts=(s).hosts) (groups : (A).groups=(s).groups) (lanes : (A).lanes=(s).lanes)
    (room : (v).finalEnd b<2^w) :
    (v).RankPortRoom b w ∧ ((v).rankBook ((v).linkedRankInputs u.sectors start) b).Previous w:=by
  have order:=(v).ranked_space_earlier b
  have late : (v).jointEnd b≤(v).candidateEnd b:=
    ((v).receipt_order b).2.trans ((Nat.le_add_right ..).trans ((s).room r))
  have packed : (v).jointEnd b<2^w:=late.trans_lt (((v).rankPort_after b).trans_lt (order.2.2.trans_lt room))
  have space:=(v).rank_port_room b u.earlier (u.joints_of_roof palette packed) sites room
  exact ⟨space,(v).previous_from_shelves u.sectors start b matched space hosts groups lanes⟩

theorem sheet_access (blocks : (s).blocks=(A).blocks) (size : (s).candidates=(A).candidates)
    (bits : u.sectors.pageBits=Nat.clog 2 (s).rows)
    (count : (s).jobs=(s).blocks*((s).contacts+(s).privates))
    (sb : (A).blocks=(v).front.blocks) (st : u.directory.stems=(v).front.signedQueries)
    (hosts : (A).hosts=(s).hosts) (groups : (A).groups=(s).groups) (lanes : (A).lanes=(s).lanes)
    (room : (v).finalEnd b<2^w) :
    (∀x j,(u.sectors.header x j).Fits w start) ∧ (∀x j,(u.sectors.original x j).Fits w start) ∧
    (A).hosts*chunks (A).groups (A).lanes≤2^u.sectors.pageBits ∧
    DescentResetCandidatePair.endAddress start (A).blocks
      (CandidateSheet.size u.sectors.stems u.sectors.contacts u.sectors.privates) u.sectors.pageBits=(v).candidateEnd b:=by
  have matched:=(v).sheets_boundary u.sectors b blocks size bits
  have order:=(v).ranked_space_earlier b
  have before: (v).candidateEnd b<2^w:=((v).rankPort_after b).trans_lt (order.2.2.trans_lt room)
  have roomStart : start<2^w:=by
    rw [←matched] at before
    unfold DescentResetCandidatePair.endAddress DescentResetCandidatePair.originalBase at before
    omega
  have low : (s).metaEnd r≤ start:=(s).meta_before_original r
  have privateLow : (v).privateEnd b≤r:=Nat.le_add_right ..
  let layer : DescentResetCandidateDate.Mixed :=
    {first:=r,jobs:=(s).jobs,lanes:=(s).lanes,hosts:=(s).hosts,groups:=(s).groups,
     bits:=(s).metaBits,rankReads:=fun _ _=>.lit 0,rawReads:=fun _ _=>.lit 0}
  have mixedLow : r≤(s).metaEnd r:=layer.ordered.1.trans layer.ordered.2
  have trunkLow : (v).trunkEnd b≤ start:=by
    have mass : (v).trunkEnd b≤(v).massEnd b:=by unfold ResetOutput.massEnd;rw [(v).contactShape.translate];omega
    obtain ⟨join_,private_⟩:=(v).receipt_order b
    omega
  have source (x : Fin (A).blocks) (j : ℕ) (good : j<(s).contacts+(s).privates) :
      (Expr.lookup (((s).masks r).output 9 (s).metaBits (x.val*((s).contacts+(s).privates)+j)) .row).Fits w start:=by
    have steps : x.val<(s).blocks:=blocks.symm ▸ x.isLt
    have slot : x.val*((s).contacts+(s).privates)+j<(s).jobs:=count.symm ▸ pair_bound steps good
    have fit:=((s).masks r).output_fits (N:=9) (field:=(s).metaBits) _ slot (low.trans_lt roomStart)
    exact ⟨⟨fit.1,fit.2.1,fit.2.2.trans low⟩,trivial⟩
  refine ⟨?_,?_,?_,matched⟩
  · intro x j
    rcases j with j|j
    · exact ProtocolRAMGeneratedWrite.fits_mono _ trunkLow ((v).front.stem_operand_fits E scene
        (trunkLow.trans_lt roomStart) (x.cast sb) (j.cast st))
    rcases j with j|j
    · exact ProtocolRAMGeneratedWrite.fits_mono _ trunkLow
        ((v).front.trunk_operand_fits E scene (x.cast sb) (trunkLow.trans_lt roomStart))
    rcases j with j|j
    · exact source x j.val (j.isLt.trans_le (Nat.le_add_right ..))
    · exact source x ((s).contacts+j.val) (Nat.add_lt_add_left j.isLt _)
  · intro x j
    let p:=CandidateSheet.index u.directory.stems (s).contacts (s).privates j
    have eq := size.trans u.directory.count
    exact ⟨original_slot_space ((s).original r) (s).rows (s).blocks (s).candidates
      (x.cast blocks.symm) (p.cast eq.symm) roomStart,trivial⟩
  · rw [bits,hosts,groups,lanes]
    exact Nat.le_pow_clog (by decide) _

end PhysicalReset.DateInputs
end
end Hierarchy.DescentDatedAddressBook

end OAI
