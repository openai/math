import OAI.Hierarchy.DescentRegisteredWindowRooms
import OAI.Hierarchy.DescentResetReceiverPitch

namespace OAI
/-! # The named reset receiver's lane count fits the physical word -/

namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentCompiler DescentPacking.PackedMatch.Local.Stage

/-- The reset cutoff is computed using the width of the same named date's receiver.
Its lane count fits a word whenever that date's receiver fits the payload. -/
theorem Menu.receiverCut_pow_le {F : Type} [Field F] {n degree : ℕ}
    (b : Menu n degree) (G : PoweredGadget F) (S : AtomSchedule) (k i : ℕ)
    (ports : DatePorts) (w : ℕ)
    (short : 8*b.receiverWidth G S k i ports≤b.payload) (bus : b.payload≤w) :
    2^(PhysicalReset.receiverCut G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload
      (NativePitch.resetCut S k b.tail b.p b.f b.payload i)
      (NativePitch.incoming S k b.tail b.p b.f b.payload b.ordinary (i+1))
      b.op.C b.op.w ports.operandLanes ports.roleLanes
      (DescentPrimitivePalette.printedBits G (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) b.op)
      ports.venue)≤w := by
  let width := b.receiverWidth G S k i ports
  have positive : 0 < width := ResetOutput.groupWidth_pos _
  have quotient : 0 < b.payload/(8*width) := Nat.div_pos short (by omega)
  have byLog := Nat.pow_log_le_self 2 quotient.ne'
  change 2^(DescentPackedWalsh.laneBits _ b.payload width)≤w
  exact ((Nat.pow_le_pow_right (by decide : 0<2) (Nat.min_le_right _ _)).trans byLog).trans
    ((Nat.div_le_self _ _).trans bus)


end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
