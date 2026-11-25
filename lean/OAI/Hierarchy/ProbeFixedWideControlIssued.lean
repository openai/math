import OAI.Hierarchy.ProbeFixedWideEarlyBanks
import OAI.Hierarchy.ProbeSparseParticipantROM
import OAI.Hierarchy.TaggedWideControlResident
import OAI.Hierarchy.TaggedWideLocalPageRun
import OAI.Hierarchy.TaggedWidePageSweep
import OAI.Hierarchy.TaggedWideVacantBallot

namespace OAI
/-! # The original ballot and dense control work on a single chronological heap -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard HistoryRoles WideCPU
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width ell fee rom work : ℕ)
local notation "B" => Native.wordBits h (2^v.W) Native.copies
local notation "g" => v.wideDated h width ell fee
local notation "D" => v.widePacketDegree
local notation "T" => (events v.mesh).length
variable (sites : Fin (v.wideDated h width ell fee).siteDirectorySize → ℕ)
  (transport : Fin (v.wideDated h width ell fee).rawEdges → Bool)
  (initial : Memory (Native.wordBits h (2^v.W) Native.copies))
  (gap : 3*(v.wideDated h width ell fee).romEnd rom+2≤work)
  (room : (v.wideDated h width ell fee).workEnd work<2^(Native.wordBits h (2^v.W) Native.copies))
  (j : Fin (events v.mesh).length)

include gap room

theorem wide_feed_ballot_issued (b : Boundary) (hit : (events v.mesh).get j=.feed b) :
    (PageResult.skip ((g).ballotPage rom work j)).Issued work ((g).words rom sites transport initial) := by
  intro now low
  let x:=(g).fields j ((g).siteROM rom) ((g).siteStride rom) ((g).roleStart work j.castSucc) ((g).roleStart work j.succ)
  have shape : (g).ballot j=⟨0,0,0⟩:=by change v.widePacketShape h width ((events v.mesh).get j)=_;rw [hit];rfl
  have none : ((g).ballot j).parties=0:=congrArg Shape.parties shape
  have cells : ((g).ballot j).columns=0:=congrArg Shape.columns shape
  have count : ((g).ballot j).count=0:=by rw [shape];rfl
  have mounted:=(g).ballot_public rom work sites transport initial now j
    (fun i _ bound=>low i (by
      have endAt:=extent ((g).firstROM rom) (fun t=>((g).ballot t).advice (g).sites) j
      change (g).ballotROM rom j+_≤(g).controlROMStart rom at endAt
      have after : (g).controlROMStart rom≤(g).romEnd rom:=by
        dsimp only [Dated.romEnd,Dated.maskROM,endOf];omega
      omega)) x (fun i=>False.elim (by have:=i.isLt;omega))
    (by omega) (by omega) gap room
  refine ⟨now, ?_, trivial, fun _ _ => rfl⟩
  exact Shape.empty_exec ((g).ballot j) (g).sites ((g).ballotROM rom j) ((g).ballotStart work j) x now count cells
    (by have:=mounted.space;omega) mounted.address mounted.value

set_option maxHeartbeats 1200000 in
theorem wide_original_control_issued :
    (PageResult.skip ((g).controlPage rom work j)).Issued work ((g).words rom sites transport initial) := by
  intro now low
  let a:=(g).controlBase work j
  let val:=(g).controls j ((g).siteStride rom) ((g).roleStart work j.castSucc) ((g).roleStart work j.succ) ((g).ballotStart work j+1)
  have ws : work≤(g).rolesEnd work:=Nat.le_add_right ..
  have sa : (g).rolesEnd work≤(g).controlStart work:=Nat.le_add_right ..
  have near : work≤a:=(ws.trans sa).trans (Nat.le_add_right ..)
  have endAt:=extent ((g).controlStart work) (fun t=>((g).control t).span (g).sites) j
  change a+((g).control j).span (g).sites≤(g).maskStart work at endAt
  have last : (g).maskStart work≤(g).workEnd work :=by dsimp only [Dated.workEnd,Dated.slotStart];omega
  have billed : a+((g).control j).span (g).sites<2^B:=endAt.trans_lt (last.trans_lt room)
  have fit : a+1<2^B:=by dsimp only [WideCPU.Shape.span] at billed;omega
  have one : 1<2^B:=by omega
  have sitepos : 0<(g).sites:=Nat.zero_lt_succ _
  have size : ((g).control j).columns≤2^B:=by
    have:=Nat.le_mul_of_pos_left ((g).control j).columns sitepos
    dsimp only [WideCPU.Shape.span] at billed
    omega
  have siteEnd : rom+(g).sites≤(g).romEnd rom:=by
    dsimp only [Dated.romEnd,Dated.maskROM,Dated.controlROMStart,Dated.firstROM,Dated.siteROM,endOf];omega
  have table : ((g).siteStride rom).Fits B (a+1) := by
    have pad:=ProtocolRAMPurchaseSampler.span_le (g).sites
    change 0<ProtocolRAMPurchaseSampler.span (g).sites ∧ ProtocolRAMPurchaseSampler.span (g).sites<2^B ∧
      rom+ProtocolRAMPurchaseSampler.span (g).sites≤a+1
    exact ⟨Nat.two_pow_pos _,by omega,by omega⟩
  have localFields : ∀i,(val.selected i).Fits B (a+1) ∧ (val.site i).Fits B (a+1) ∧
      ∀c,(val.value i c).Fits B (a+1) := by
    apply SiteControls.fixed_fits (g).sites (g).physical D (v.wideNeighborCap width fee)
      ((g).siteStride rom) ((g).roleStart work j.castSucc) ((g).roleStart work j.succ)
      ((g).ballotStart work j+1) ((g).ballot j).columns
      (v.widePacketLowStart h width ((events v.mesh).get j)) table
    · intro b f
      cases b <;> exact v.wide_role_bank_before_control h width ell fee work work le_rfl j _ f fit
    · intro present
      have attempt_of_columns (e : Event) (active : (v.widePacketShape h width e).columns ≠ 0) :
          ∃ a : Attempt, e = .attempt a := by
        cases e with
        | attempt a => exact ⟨a, rfl⟩
        | feed b => exact (active rfl).elim
      obtain ⟨attempt, hit⟩ := attempt_of_columns ((events v.mesh).get j) present
      exact v.wide_ballot_bank_before_control h width ell fee work j attempt hit fit
  have pub:=(g).control_public rom work sites transport initial now j
    (fun i _ bound=>low i (by
      have upto:=extent ((g).controlROMStart rom) (fun t=>((g).control t).advice (g).sites) j
      change (g).controlROM rom j+_≤(g).maskROM rom at upto
      have lastROM : (g).maskROM rom≤(g).romEnd rom:=Nat.le_add_right ..
      omega)) val localFields (by exact one.le) size gap room
  obtain ⟨out,ran,words,keep⟩:=SiteControls.fixed_run
    (sites:=(g).sites) (n:=(g).physical) («D»:=D) (cap:=v.wideNeighborCap width fee) ((g).siteStride rom)
    ((g).roleStart work j.castSucc) ((g).roleStart work j.succ) ((g).ballotStart work j+1)
    ((g).ballot j).columns ((g).controlROM rom j) a (v.widePacketLowStart h width ((events v.mesh).get j))
    now one size billed pub.mounted pub.stride pub.value pub.address
  exact ⟨out,ran,trivial,fun i small=>keep i (Or.inl (by
    simpa [Dated.controlPage,Shape.sheet,Scatter.floor,a] using small))⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
