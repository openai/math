import OAI.Hierarchy.DescentTerminalEpochHeader
import OAI.Hierarchy.DescentTerminalEpochOrders
import OAI.Hierarchy.DescentTerminalEpochCapacity

namespace OAI
/-! # Extent of the emitted fixed physical selector prefix on every branch -/
namespace Hierarchy.DescentTerminalEpochDecoder
open DescentTerminalEpochChart DescentTerminalEpochBits DescentSixParty DescentInitialHost
open DescentCompiler Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {portBits : P→ℕ} {u ε : ℝ}
variable (G : PoweredGadget F) (hu : 0 ≤ u) (he : 0 ≤ ε)
variable {S Z : Type} {bits : Z→S→Bool} {ok : (S→Bool)→Prop}


theorem extend_layout {H : Histories F d P portBits} (a : SubroundInput H G (u:=u) he)
    (order : OrdersAt G he a) {root : H.Choice→Z} (old : Chart bits ok root) :
    (extendWith G he a order old).layout.length=old.layout.length+1 ∧
      seatBill (extendWith G he a order old).layout=seatBill old.layout+maxSeats G he a := by
  change (extendedLayout (C:=G.C) (seats:=maxSeats G he a) old).length=_ ∧
    seatBill (extendedLayout (C:=G.C) (seats:=maxSeats G he a) old)=_
  simp [extendedLayout,seatBill,Source.map,List.map_map,Function.comp_def]

theorem schedule_layout {H : Histories F d P portBits} {t : ℕ} (run : Schedule G (u:=u) he t H)
    (order : ScheduleOrders G he run) {source : H.Choice→Z} (old : Chart bits ok source) :
    (scheduledWith G he run order old).layout.length=old.layout.length+t ∧
      seatBill (scheduledWith G he run order old).layout=seatBill old.layout+scheduleSeats G he run := by
  induction t generalizing H with
  | zero=>simp [scheduleSeats,scheduledWith]
  | succ t ih=>
    have r:=ih run.2 order.2 (extendWith G he run.1 order.1 old)
    have e:=extend_layout G he run.1 order.1 old
    simpa only [scheduledWith,scheduleSeats,e.1,e.2,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using r

theorem epochs_layout {H : Histories F d P portBits} {t h C Ht J : ℕ}
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H) (order : EpochOrders G hu he run)
    {source : H.Choice→Z} (old : Chart bits ok source) :
    (epochsWith G hu he run order old).layout.length=old.layout.length+J*t ∧
      seatBill (epochsWith G hu he run order old).layout=seatBill old.layout+epochSeats G hu he run := by
  induction J generalizing H with
  | zero=>simp [epochSeats,epochsWith]
  | succ J ih=>
    let mid:=scheduledWith G he run.1.subrounds order.1 old
    have r:=ih run.2 order.2 mid
    have e:=schedule_layout G he run.1.subrounds order.1 old
    simpa only [mid,epochsWith,epochSeats,e.1,e.2,Nat.succ_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using r

variable {k p : ℕ} (X : Catalyst.Approximation F k p) (R s w : ℕ) (word : s < 2^w)
variable (sched : AtomSchedule) {h C Ht : ℕ}
variable (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=sched.rounds) sched.height (initialGroup X R s))

theorem physical_extent (order : EpochOrders G hu he run)
    (paid : epochSeats G hu he run ≤ sched.length*sched.batch) :
    DescentTerminalEpochHeader.extent (actualWith G hu he X R s w word run order).layout ≤
      2*(sched.length*sched.batch)+sched.length := by
  let b:=actualWith G hu he X R s w word run order
  have data:=epochs_layout G hu he run order (seedChart X R s w word)
  have n : b.layout.length=sched.height*sched.rounds := by simpa [b,actualWith,seedChart] using data.1
  have u : seatBill b.layout=epochSeats G hu he run := by simpa [b,actualWith,seatBill,seedChart] using data.2
  have upper:=DescentTerminalEpochHeader.extent_le b.layout
  change _ ≤ 2*seatBill b.layout+b.layout.length at upper
  rw [u,n] at upper
  have t : sched.height*sched.rounds ≤ sched.length := by
    unfold AtomSchedule.length
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm sched.rounds]
    omega
  exact upper.trans (Nat.add_le_add (Nat.mul_le_mul_left 2 paid) t)

end
end Hierarchy.DescentTerminalEpochDecoder

end OAI
