import OAI.Hierarchy.DescentNamedReceiverInputs
import OAI.Hierarchy.DescentWalshPrecision

namespace OAI
/-! # A common bound on the local numerical inputs of every purchased calendar -/
namespace Hierarchy.DescentDatedAddressBook
open DescentCompiler DescentSixParty DescentCompiler.TerminalScale Filter
noncomputable section

/-- The exponent in an individual polynomial may depend on the calendar. The
coefficient of the external word height in its exponential upper bound is one. -/
theorem SmallAt.absolutely_short {ι : ℕ→Type*} {a : ∀h,ι h→ℕ} {J : ℕ→ℕ}
    (q : SmallAt J a) (level : ∀h,J h≤Nat.log 2 h) :
    ∀ᶠ h : ℕ in atTop,∀i,a h i≤2^h :=by
  obtain ⟨E,room⟩:=q
  filter_upwards [room,DescentWalshPrecision.eventually_log_square E] with h bound carry
  intro i
  apply (bound i).trans
  apply Nat.pow_le_pow_right (by decide)
  have first := Nat.mul_le_mul_left E (Nat.succ_le_succ (level h))
  have square : Nat.log 2 h+1≤(Nat.log 2 h+1)^2:=by nlinarith
  exact first.trans ((Nat.mul_le_mul_left E square).trans carry)

namespace ResetOutput
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (D f g C packet : ℕ)

def Sample.localNumbers (a : Sample) : List ℕ :=
  let v:=a.output G board D f g C packet
  [v.sheets.blocks, v.front.peer.shapes, v.sheets.candidates,
   v.sheets.jobs, v.sheets.contacts, v.sheets.privates,
   v.sheets.metaBits, v.sheets.stemBits, v.sheets.selectorBits,
   v.sheets.shortBits, v.sheets.zeroBits, v.sheets.haloBits,
   v.sheets.argBits, v.sheets.stemSources.width, v.ticketBits,
   ((capCalendar G.b a.sched.rounds g a.sched.height).take a.age).prod*256, a.sched.groupWidth a.k a.tail a.age+a.k, v.middle.rootControlBits v.front.donor.cap,
   v.rootOutputBits, v.venue.census.broadcast, a.prior.venue.paidBits,
   DescentOperandWidth.recordBits G a.sched a.k a.tail a.drift a.degree a.p, a.prior.printedBits, a.sched.retainedArgumentsAt G a.drift,
   a.sched.retainedNodes]

variable {ι : ℕ→Type*} (z : ∀h,ι h→Sample)
local notation "keys" h:arg i:arg => Sample.localNumbers G board D f g C packet (z h i)
set_option maxHeartbeats 1600000 in
theorem CalendarInputs.local_numbers (J : ℕ→ℕ) (r : CalendarInputs G board D f g C packet J z)
    (level : ∀h,J h≤Nat.log 2 h) : ∀ᶠ h : ℕ in atTop,∀i,∀m∈keys h i,m≤2^h :=by
  filter_upwards [
    r.sheets.block.absolutely_short level, r.sheets.shapes.absolutely_short level,
    r.sheets.slots.absolutely_short level, r.sheets.jobs.absolutely_short level,
    r.sheets.contact.absolutely_short level, r.sheets.private_.absolutely_short level,
    r.sheets.meta.absolutely_short level, r.sheets.old.absolutely_short level,
    r.sheets.select_.absolutely_short level, r.sheets.short.absolutely_short level,
    r.sheets.blank.absolutely_short level, r.sheets.halo.absolutely_short level,
    r.sheets.argument.absolutely_short level, r.sheets.stem.absolutely_short level,
    r.sheets.original_.absolutely_short level, r.previousCap.absolutely_short level,
    r.dimension.absolutely_short level, r.controls.absolutely_short level,
    r.rootOutput.absolutely_short level, r.funded.absolutely_short level,
    r.paid.absolutely_short level, r.coefficient.absolutely_short level,
    r.primitive.absolutely_short level, r.arguments.absolutely_short level,
    r.nodes.absolutely_short level] with h
    a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
  intro i m found
  simp only [Sample.localNumbers,List.mem_cons,List.not_mem_nil,or_false] at found
  rcases found with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24 <;> subst m
  · exact a0 i
  · exact a1 i
  · exact a2 i
  · exact a3 i
  · exact a4 i
  · exact a5 i
  · exact a6 i
  · exact a7 i
  · exact a8 i
  · exact a9 i
  · exact a10 i
  · exact a11 i
  · exact a12 i
  · exact a13 i
  · exact a14 i
  · exact a15 i
  · exact a16 i
  · exact a17 i
  · exact a18 i
  · exact a19 i
  · exact a20 i
  · exact a21 i
  · exact a22 i
  · exact a23 i
  · exact a24 i

/-- Different calendars can now occupy different entries at the same height. -/
theorem CalendarInputs.of_local_numbers
    (q : ∀h i,∀m∈keys h i,m≤2^h)
    (fibres : ∀h i,((z h i).output G board D f g C packet).setup.retained.donors=2^(z h i).k) :
    CalendarInputs G board D f g C packet id z :=by
  have axis (a : ∀h,ι h→ℕ) (mem : ∀h i,a h i∈keys h i) : SmallAt id a :=by
    refine ⟨1,Eventually.of_forall fun h i=>?_⟩
    change a h i≤2^(1*(h+1))
    exact (q h i _ (mem h i)).trans (Nat.pow_le_pow_right (by decide) (by omega))
  constructor
  · constructor <;> apply axis <;> intro h i <;> simp [Sample.localNumbers]
  · apply axis
    intro h i
    simp [Sample.localNumbers]
  · apply axis
    intro h i
    simp [Sample.localNumbers]
  · apply axis
    intro h i
    simp [Sample.localNumbers]
  · apply axis
    intro h i
    simp [Sample.localNumbers]
  · apply axis
    intro h i
    simp [Sample.localNumbers]
  · apply axis
    intro h i
    simp [Sample.localNumbers]
  · apply axis
    intro h i
    simp [Sample.localNumbers]
  · apply axis
    intro h i
    simp [Sample.localNumbers]
  · apply axis
    intro h i
    simp [Sample.localNumbers]
  · apply axis
    intro h i
    simp [Sample.localNumbers]
  · exact fibres

end ResetOutput
end
end Hierarchy.DescentDatedAddressBook

end OAI
