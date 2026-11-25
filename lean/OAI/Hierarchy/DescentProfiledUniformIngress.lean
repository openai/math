import OAI.Hierarchy.DescentProfiledResetArea
import OAI.Hierarchy.DescentResetCanvasIngressRate

namespace OAI
/-! The signed-token and amount collectors share the measured pitch of the preceding reset venue. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline.ResetArea
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler TerminalScale Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g reset drift degreeMax : ℕ)
local notation "Cut" h:arg => ResetArea G board op t f g reset drift degreeMax h
local notation "Allowed" h:arg => {x : Cut h // x.Verified ∧ x.frozen≤Nat.log 2 h}

theorem uniform_ingress :
    DescentResetCanvasIngress.Layout.ScalarRoom (fun h (i : Allowed h) => i.val.stage.ingress) := by
  have dimension (h) (i : Allowed h) :
      i.val.sched.groupWidth i.val.k i.val.frozen i.val.v.age+i.val.k ≤ h :=
    (Nat.le_mul_self _).trans (i.property.1.matrix.trans (Nat.div_le_self ..))
  have word (h) (i : Allowed h) :
      i.val.stage.ingress.signed.bits = DescentSignedCableCodec.width (atRound t) i.val.old.venue.cap := by
    let x := i.val
    change DescentSignedCableCodec.width x.old.venue.degree
      (((capCalendar G.b x.sched.rounds g x.sched.height).take x.v.age).prod*256) = _
    exact congrArg₂ DescentSignedCableCodec.width x.reached_degree x.v.geometry.capacity.symm
  have signed (h) (i : Allowed h) :
      i.val.stage.ingress.signed.bits*i.val.old.venue.lanes ≤ h/2 := by
    rw [word]
    exact i.property.1.previousWords.1
  have amount (h) (i : Allowed h) :
      i.val.stage.ingress.oldBits*i.val.old.venue.lanes ≤ h/2 := i.property.1.previousWords.2
  have source (h) (i : Allowed h) : i.val.stage.ingress.sourceLanes=i.val.old.venue.lanes := rfl
  have target (h) (i : Allowed h) : i.val.stage.ingress.targetLanes=i.val.old.venue.lanes :=
    i.val.previous_pitch.symm
  have lane (h) (i : Allowed h) : i.val.old.venue.lanes ≤ 2^h :=
    i.property.1.paid.2.trans (Nat.lt_two_pow_self (n:=h)).le
  refine ⟨⟨1,Eventually.of_forall fun h i => ?_⟩,⟨3,Eventually.of_forall fun h i => i.property.1.oldHost⟩,
    ⟨1,Eventually.of_forall fun h i => ?_⟩,⟨1,Eventually.of_forall fun h i => ?_⟩,
    ⟨1,Eventually.of_forall fun h i => ?_⟩,⟨1,Eventually.of_forall fun h i => ?_⟩,
    ⟨1,Eventually.of_forall fun h i => ?_⟩,⟨1,Eventually.of_forall fun h i => ?_⟩,
    ⟨1,Eventually.of_forall fun h i => ?_⟩⟩
  · rw [Nat.one_mul]
    exact Nat.pow_le_pow_right (by decide : 0<2) ((Nat.le_add_left ..).trans (dimension h i))
  · rw [Nat.one_mul]
    exact Nat.pow_le_pow_right (by decide : 0<2) ((Nat.le_add_right ..).trans (dimension h i))
  · rw [Nat.one_mul]
    apply i.property.1.localNumbers
    change ((capCalendar G.b i.val.sample.sched.rounds g i.val.sample.sched.height).take i.val.sample.age).prod*256 ∈ _
    simp [ResetOutput.Sample.localNumbers]
  · simpa only [Nat.one_mul,source] using lane h i
  · simpa only [Nat.one_mul,target] using lane h i
  · simpa only [Nat.one_mul,source] using (signed h i).trans (Nat.div_le_self ..)
  · simpa only [Nat.one_mul,source] using (amount h i).trans (Nat.div_le_self ..)
  · rw [Nat.one_mul,target]
    rcases le_total i.val.stage.ingress.oldBits i.val.stage.ingress.signed.bits with le | le
    · rw [max_eq_right le]
      exact (signed h i).trans (Nat.div_le_self ..)
    · rw [max_eq_left le]
      exact (amount h i).trans (Nat.div_le_self ..)

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline.ResetArea

end OAI
