import OAI.Hierarchy.DescentAtomSchedule
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # The original selector seats fit every actual dated host and group rectangle -/
namespace Hierarchy.DescentCompiler.TerminalScale
noncomputable section

theorem selector_seats (S : AtomSchedule) {i seats : ℕ} (age : i≤S.length) (maxSeats : seats≤S.length*S.batch) :
    seats≤S.hostSize i*(S.groupCount i*S.radix)*scale S.height
      ((S.rounds+1)*(S.hostGain+S.capGain+1)+11) := by
  have rows : S.hostSize i*(S.groupCount i*S.radix)=(S.initialSites*S.copies)*(2^S.hostGain)^i := by
    have eqn : S.radix^i*S.radix^(S.length-i)=S.radix^S.length := by rw [←pow_add,Nat.add_sub_of_le age]
    calc
      _ = (S.initialSites*(S.baseGroups*((S.radix^i*S.radix^(S.length-i))*S.radix)))*(2^S.hostGain)^i := by
        dsimp only [AtomSchedule.hostSize,AtomSchedule.groupCount]
        rw [mul_pow];ring
      _ = _ := by rw [eqn,AtomSchedule.copies,pow_succ]
  have base : S.initialSites*S.copies≤S.hostSize i*(S.groupCount i*S.radix) := by
    rw [rows]
    exact Nat.le_mul_of_pos_right _ (pow_pos (Nat.two_pow_pos _) _)
  have periods : S.length≤2^S.length := (Nat.lt_two_pow_self).le
  have expo : S.length+S.hostGain*S.length+(11+S.capGain*S.length)≤
      ((S.rounds+1)*(S.hostGain+S.capGain+1)+11)*(S.height+1) := by unfold AtomSchedule.length; nlinarith
  calc
    seats ≤ S.length*((S.initialSites*S.copies)*(2^S.hostGain)^S.length*2^(11+S.capGain*S.length)) := maxSeats
    _ ≤ 2^S.length*((S.hostSize i*(S.groupCount i*S.radix))*(2^S.hostGain)^S.length*2^(11+S.capGain*S.length)) :=
      Nat.mul_le_mul periods (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ base))
    _ = S.hostSize i*(S.groupCount i*S.radix)*2^(S.length+S.hostGain*S.length+(11+S.capGain*S.length)) := by
      simp only [pow_add,pow_mul];ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) expo)

end
end Hierarchy.DescentCompiler.TerminalScale

end OAI
