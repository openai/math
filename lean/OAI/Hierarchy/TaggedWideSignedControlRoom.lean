import OAI.Hierarchy.TaggedWideSpillDates
import OAI.Hierarchy.TaggedWideCalendarPartyWords

namespace OAI
/-! # Word ranges used on an actual corrected signed date -/
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles
open scoped BigOperators
namespace WideCPU
theorem SpillDates.signed_control_room {T : ℕ} (z : SpillDates T) (start : ℕ) (j : Fin T)
    {native : ℕ} (room : z.endAt start<2^native) :
    z.original.physical<2^native ∧ z.original.roleWords<2^native ∧
    z.original.sites*(z.original.ballot j).columns<2^native := by
  let p:=z.original
  let work:=z.roleRoot start 2
  have next : p.controlStart work ≤ z.endAt start := by
    dsimp only [SpillDates.endAt,Dated.maskStart,endOf,p,work]; omega
  have roles : p.rolesEnd work ≤ p.controlStart work := by
    dsimp only [Dated.controlStart,endOf];omega
  have one : p.roleSpan ≤ p.rolesEnd work := by
    calc
      p.roleSpan ≤ 3*p.roleSpan := by omega
      _ ≤ (T+1)*(3*p.roleSpan) := Nat.le_mul_of_pos_left _ (Nat.succ_pos T)
      _ ≤ work+(T+1)*(3*p.roleSpan) := Nat.le_add_left _ _
  have span := (((one.trans roles).trans next).trans_lt room)
  have each : (p.ballot j).span p.sites ≤ stride (fun i=>(p.ballot i).span p.sites) :=
    Finset.single_le_sum (fun i _=>Nat.zero_le ((p.ballot i).span p.sites)) (Finset.mem_univ j)
  have cell : p.sites*(p.ballot j).columns ≤ (p.ballot j).span p.sites := by
    unfold Shape.span
    omega
  have ballots : stride (fun i=>(p.ballot i).span p.sites) ≤ p.controlStart work := by
    change _ ≤ p.rolesEnd work+T*stride (fun i=>(p.ballot i).span p.sites)
    exact (Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt j.isLt)).trans (Nat.le_add_left _ _)
  change p.physical<2^native ∧ p.roleWords<2^native ∧ p.sites*(p.ballot j).columns<2^native
  dsimp only [Dated.roleSpan,DatedRoleSheets.span] at span
  exact ⟨by omega,by omega,(((cell.trans each).trans ballots).trans next).trans_lt room⟩

end WideCPU

namespace FixedProtocolFormat
open ProbeStage Tagged
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
theorem signed_double_room (h width unitCost : ℕ) (a : Attempt)
    (paid : v.PartyWordBounds h width unitCost) :
    2*v.wideNeighborCap width unitCost<2^Native.wordBits h (2^v.W) Native.copies := by
  have fit:=(v.party_lane_room h width a unitCost).1
  have above := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (paid.lane a)
  have two:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.succ_le_of_lt above)
  rw [pow_succ] at two
  omega
end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar

end OAI
