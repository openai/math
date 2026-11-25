import OAI.Hierarchy.DescentDatePortArchiveWidths
import OAI.Hierarchy.DescentSeedInitialArgumentCapacity
import OAI.Hierarchy.DescentRetainedOperandCounts

namespace OAI
/-! The argument count on an actual registered cut occupies one operand digit. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage

variable {F : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule} {op : RotorSpec}
    {ports : DatePorts} {k tail p drift degree payload age : ℕ}

theorem ArchiveWidths.posted_arguments (a : ArchiveWidths G S op ports k tail p drift degree payload age)
    (posted : ports.argumentsPerNode=if age=0 then 3*(S.firstWidth G.b p/p) else S.retainedArgumentsAt G drift)
    (hp : 0<p) (height : 0<S.height) (gain : G.b≤2^S.capGain) :
    0<ports.argumentsPerNode ∧ ports.argumentsPerNode<2^ports.operandBits := by
  have first : p≤S.firstWidth G.b p :=
    (Nat.le_mul_of_pos_right p (pow_pos G.base_pos (S.rounds*S.height-S.ordinaryDone 0))).trans
      (Nat.le_mul_of_pos_right _ G.base_pos)
  have live : 0<S.retainedNodes :=
    pow_pos (Nat.two_pow_pos _) _
  have liveArgs : 0<S.retainedArgumentsAt G drift :=
    Nat.mul_pos (Nat.succ_pos _) (pow_pos (Nat.two_pow_pos _) _)
  have bound : ports.argumentsPerNode ≤ S.retainedArgumentsAt G drift := by
    rw [posted]
    split
    · exact S.seed_argument_capacity G p drift height gain
    · exact le_rfl
  constructor
  · rw [posted]
    split
    · exact Nat.mul_pos (by decide) (Nat.div_pos first hp)
    · exact liveArgs
  · rw [a.digits]
    exact (bound.trans (Nat.le_mul_of_pos_left _ live)).trans_lt
      (DescentOperandWidth.retained_rectangle_lt G S k tail drift degree p)

end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
