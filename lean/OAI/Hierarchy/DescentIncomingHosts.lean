import OAI.Hierarchy.DescentAtomSchedule
import OAI.Hierarchy.DescentPrivateDonorBillNumbers

namespace OAI
/-! # Actual incoming host rows for ordinary, reset, and frozen terminal dates -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentCompiler.TerminalScale

/-- The ordinary matcher uses a dyadic host atlas. Both reset and the terminal
frozen roster use the exact host envelope at their own date. -/
def incomingHosts (S : AtomSchedule) (i : ℕ) : ℕ :=
  if i<S.length then
    if i%(S.rounds+1)=S.rounds then S.hostSize i else hostRows (S.hostSize i)
  else S.hostSize S.length

theorem hosts_ordinary (S : AtomSchedule) (e j : ℕ) (row : j<S.rounds)
    (time : e*(S.rounds+1)+j<S.length) :
    incomingHosts S (e*(S.rounds+1)+j)=hostRows (S.hostSize (e*(S.rounds+1)+j)) := by
  have rem : (e*(S.rounds+1)+j)%(S.rounds+1)=j := by
    rw [Nat.mul_comm e,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (by omega)]
  simp only [incomingHosts,ite_eq_left time,rem,ite_eq_right (Nat.ne_of_lt row)]

theorem hosts_reset (S : AtomSchedule) (e : ℕ) (time : e*(S.rounds+1)+S.rounds<S.length) :
    incomingHosts S (e*(S.rounds+1)+S.rounds)=S.hostSize (e*(S.rounds+1)+S.rounds) := by
  have rem : (e*(S.rounds+1)+S.rounds)%(S.rounds+1)=S.rounds := by
    rw [Nat.mul_comm e,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (by omega)]
  rw [incomingHosts,ite_eq_left time,ite_eq_left rem]

theorem hosts_final (S : AtomSchedule) : incomingHosts S S.length=S.hostSize S.length := by
  simp only [incomingHosts,lt_self_iff_false,ite_false]

theorem hosts_bounds (S : AtomSchedule) (i : ℕ) (active : i≤S.length) :
    S.hostSize i≤ incomingHosts S i ∧ incomingHosts S i≤hostRows (S.hostSize i) := by
  by_cases inside : i<S.length
  · unfold incomingHosts
    rw [ite_eq_left inside]
    split <;> exact ⟨by first | apply le_rfl | apply hostPad,by first | apply le_rfl | apply hostPad⟩
  · obtain rfl : i=S.length:=by omega
    rw [hosts_final];exact ⟨le_rfl,hostPad _⟩

end Hierarchy.DescentSixParty.NativePitch

end OAI
