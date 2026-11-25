import OAI.Hierarchy.TaggedWideDatedROM
import OAI.Hierarchy.TaggedWideDatedNeighborReads
import OAI.Hierarchy.ProtocolRAMCalendarMesh

namespace OAI
/-! # Bounds for the original dyadically indexed role banks at an elected ballot -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles
open scoped Classical

/-- A real attempt and its enclosing phase's feed are separate dates. -/
theorem attempt_two_dates (c : Mesh) (a : Attempt) (active : Event.attempt a∈events c) :
    2≤(events c).length := by
  have phases : 0<c.inject+c.cool := by
    by_contra! none
    have no : c.inject+c.cool=0 := by omega
    simp [events,no] at active
  have trials : 0<c.outerFuel := by
    by_contra! none
    have no : c.outerFuel=0 := by omega
    simp [events,outerBlock,no] at active
  rw [event_count]
  have block := Nat.mul_pos trials (show 0<1+c.reserveSteps*(c.innerFuel+1) by omega)
  have big:=Nat.le_mul_of_pos_left (c.outerFuel*(1+c.reserveSteps*(c.innerFuel+1))+1) phases
  omega

namespace WideCPU
variable {W T : ℕ} (p : Dated T)

/-- The two original role records read by this dated ballot. The logical
record has `roleWords` entries, while its lookup bank extends to the next
power of two. Earlier dates leave a complete role triple; at the last
date the first ballot stride covers that final dyadic tail. -/
theorem Dated.role_bank_before_ballot_control (work : ℕ) (j : Fin T) (i : Fin (T+1))
    (earlier : i.val≤j.val+1) (dates : 2≤T)
    (columns : p.roleCount≤(p.ballot j).columns)
    (range : p.controlStart work<2^W) (f : Fin 3) :
    (DatedRoleSheets.bank p.physical (p.roleStart work i) p.roleWords
      (ProtocolRAMPurchaseSampler.bits p.roleWords) f).Fits W (p.ballotStart work j+1) := by
  let S:=p.roleSpan
  let L:=p.roleWords
  let len:=ProtocolRAMPurchaseSampler.span L
  let gap:=stride (fun k=>(p.ballot k).span p.sites)
  have enough : L+1≤S := by dsimp [S,L,Dated.roleSpan,DatedRoleSheets.span];omega
  have size : len≤2*(L+1):=ProtocolRAMPurchaseSampler.span_le _
  have nonempty : 0<len:=Nat.lt_of_le_of_lt (Nat.zero_le _) (ProtocolRAMPurchaseSampler.lt_span L)
  have span_covered : L+1≤gap := by
    have cover:=Nat.mul_le_mul_left p.sites columns
    have bound : (p.ballot j).span p.sites≤gap :=
      Finset.single_le_sum (f:=fun t:Fin T=>(p.ballot t).span p.sites)
        (fun t _=>Nat.zero_le _) (Finset.mem_univ j)
    change p.sites*p.roleCount+1≤gap
    change 1+p.sites*(p.ballot j).columns+2*(p.ballot j).count≤gap at bound
    omega
  have f_bound : f.val*S≤2*S := Nat.mul_le_mul_right S (by omega)
  have startMax : i.val*(3*S)≤T*(3*S):=Nat.mul_le_mul_right (3*S) (by omega)
  have after : work+i.val*(3*S)+f.val*S+1+len≤work+(T+1)*(3*S)+j.val*gap+1 := by
    rw [Nat.add_mul,one_mul]
    by_cases early : i.val<T
    · have next:=Nat.mul_le_mul_right (3*S) early
      rw [Nat.succ_mul] at next
      omega
    · have positive : 0<j.val := by omega
      have room:=Nat.le_mul_of_pos_left gap positive
      omega
  have maxSlot : p.ballotStart work j+(p.ballot j).span p.sites≤p.controlStart work:=
    extent _ _ j
  have word : p.ballotStart work j+1<2^W := by
    have h : 0<(p.ballot j).span p.sites := by dsimp [Shape.span];omega
    omega
  change 0<len ∧ len<2^W ∧ work+i.val*(3*S)+f.val*S+1+len≤p.ballotStart work j+1
  have address : work+i.val*(3*S)+f.val*S+1+len≤p.ballotStart work j+1 :=after
  exact ⟨nonempty,by omega,address⟩

theorem Dated.role_bank_before_ballot (work : ℕ) (j : Fin T) (i : Fin (T+1))
    (earlier : i.val≤j.val+1) (dates : 2≤T)
    (columns : p.roleCount≤(p.ballot j).columns)
    (range : p.workEnd work<2^W) (f : Fin 3) :
    (DatedRoleSheets.bank p.physical (p.roleStart work i) p.roleWords
      (ProtocolRAMPurchaseSampler.bits p.roleWords) f).Fits W (p.ballotStart work j+1) :=
  p.role_bank_before_ballot_control work j i earlier dates columns (lt_of_le_of_lt
    (by dsimp only [Dated.workEnd,Dated.slotStart,Dated.maskStart,endOf];omega) range) f

/-- Public party and field ordinals fit the very word used by the actual
scatter, from its already billed output and candidate count. -/
theorem Dated.ballot_ordinals_control (work : ℕ) (j : Fin T) (sites : 0<p.sites) (rows : 0<(p.ballot j).candidates)
    (columns : 0<(p.ballot j).columns) (range : p.controlStart work<2^W) :
    (p.ballot j).parties≤2^W ∧ (p.ballot j).columns≤2^W := by
  have runPage : p.ballotStart work j+(p.ballot j).span p.sites≤p.controlStart work:=extent _ _ j
  have raw:=Nat.le_mul_of_pos_left ((p.ballot j).parties*(p.ballot j).columns) rows
  have fields:=Nat.le_mul_of_pos_left (p.ballot j).columns sites
  have groups:=Nat.le_mul_of_pos_right (p.ballot j).parties columns
  dsimp only [Shape.span,Shape.count] at runPage
  constructor <;> omega

theorem Dated.ballot_ordinals (work : ℕ) (j : Fin T) (sites : 0<p.sites) (rows : 0<(p.ballot j).candidates)
    (columns : 0<(p.ballot j).columns) (range : p.workEnd work<2^W) :
    (p.ballot j).parties≤2^W ∧ (p.ballot j).columns≤2^W :=
  p.ballot_ordinals_control work j sites rows columns (lt_of_le_of_lt
    (by dsimp only [Dated.workEnd,Dated.slotStart,Dated.maskStart,endOf];omega) range)

end WideCPU
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
