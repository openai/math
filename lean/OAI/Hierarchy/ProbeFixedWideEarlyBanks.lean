import OAI.Hierarchy.TaggedWideEarlyBanks
import OAI.Hierarchy.ProbeFixedWideDated
import OAI.Hierarchy.ProbeFixedSourceGeometry

namespace OAI
/-! # The actual calibrated calendar supplies the slack for every speculative role and ballot read -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard.HistoryRoles RoleProgram
open scoped Classical

theorem attempt_before_final_feed (c : Mesh) (phase : 0<c.inject+c.cool)
    (j : Fin (events c).length) (a : Attempt) (current : (events c).get j=.attempt a) :
    j.val+2≤(events c).length := by
  obtain ⟨p,ph⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt phase)
  let pre:=(List.range p).flatMap (outerBlock c)++(List.range c.outerFuel).flatMap (trialBlock c p)
  have calendar : events c=pre++[.feed (.outer p)] := by
    simp only [events,ph,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    simp only [outerBlock,pre,List.append_assoc]
  have length : (events c).length=pre.length+1 := by rw [calendar];simp
  by_contra! last
  have eq : j.val=pre.length := by have :=j.isLt;omega
  have get : (events c)[j.val]=.attempt a := current
  have impossible : Event.feed (.outer p) = Event.attempt a := by
    simpa only [calendar, List.getElem_append, eq, lt_irrefl, dite_false, Nat.sub_self,
      List.getElem_cons_zero] using get
  cases impossible

namespace FixedProtocolFormat
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width ell unitCost : ℕ)
local notation "T" => (events v.mesh).length
local notation "g" => v.wideDated h width ell unitCost
local notation "N" => Native.wordBits h (2^v.W) Native.copies
local notation "S" => WideCPU.stride (fun i=>((g).ballot i).span (g).sites)

theorem wide_dated_ballot_clearance : (g).roleWords+2≤T*S := by
  have p : 0<v.mesh.inject+v.mesh.cool:=lt_of_lt_of_le v.clock.inject_pos (Nat.le_add_right ..)
  let phase : Fin (v.mesh.inject+v.mesh.cool):=⟨0,p⟩
  let trial : Fin v.mesh.outerFuel:=⟨0,v.clock.outer_pos⟩
  obtain ⟨j,hit⟩:=List.mem_iff_get.mp (dated_outer_occurs v.mesh phase trial)
  apply (g).ballot_clearance j
  · change v.widePacketDegree≤(v.widePacketShape h width ((events v.mesh).get j)).columns
    rw [hit]
    have low:=v.widePacket_low_extent h width (.outer phase.val trial.val)
    omega
  · have dates:=attempt_before_final_feed v.mesh p j _ hit
    omega

theorem wide_role_bank_before_control (work later : ℕ) (near : work≤later)
    (j : Fin T) (date : Fin (T+1)) (f : Fin 3) (word : (g).controlBase later j+1<2^N) :
    (DatedRoleSheets.bank (g).physical ((g).roleStart work date) (g).roleWords
      (ProtocolRAMPurchaseSampler.bits (g).roleWords) f).Fits N ((g).controlBase later j+1) := by
  have endAt:=(g).role_bank_before_control work later near j date f (v.wide_dated_ballot_clearance h width ell unitCost)
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (endAt.trans_lt word),endAt⟩

theorem wide_ballot_bank_before_control (work : ℕ) (j : Fin T) (a : Attempt) (hit : (events v.mesh).get j=.attempt a)
    (word : (g).controlBase work j+1<2^N) :
    (RoleROM.bank ((g).ballotStart work j+1) ((g).sites*((g).ballot j).columns)).Fits N ((g).controlBase work j+1) := by
  have phase : 0<v.mesh.inject+v.mesh.cool:=lt_of_lt_of_le v.clock.inject_pos (Nat.le_add_right ..)
  have endAt:=(g).ballot_bank_before_control work j (attempt_before_final_feed v.mesh phase j a hit)
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (endAt.trans_lt word),endAt⟩

end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar

end
end OAI
