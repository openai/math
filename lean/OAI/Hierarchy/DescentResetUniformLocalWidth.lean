import OAI.Hierarchy.DescentNamedReceiverInputs

namespace OAI
/-! # A common exponent chosen before the word-height multiplier -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (board : NonlinearExpanders.Graph n d)
variable (D f g C packet : ℕ)

structure Sample.LocalAt (z : Sample) (j E : ℕ) : Prop where
  block : 2^z.k≤ scale j E
  cap : ((capCalendar G.b z.sched.rounds g z.sched.height).take z.age).prod*256≤ scale j E
  dim : z.sched.groupWidth z.k z.tail z.age+z.k≤ scale j E
  root : let v:=z.output G board D f g C packet;v.middle.rootControlBits v.front.donor.cap≤ scale j E
  primaries : (z.output G board D f g C packet).rootOutputBits≤ scale j E
  quantities : (z.output G board D f g C packet).venue.census.broadcast≤ scale j E
  paid : z.prior.venue.paidBits≤ scale j E
  coefficient : DescentOperandWidth.recordBits G z.sched z.k z.tail z.drift z.degree z.p≤ scale j E
  token : z.prior.printedBits≤ scale j E
  «arguments» : z.sched.retainedArgumentsAt G z.drift≤ scale j E
  nodes : z.sched.retainedNodes≤ scale j E
  fibres : (z.output G board D f g C packet).setup.retained.donors=2^z.k

/-- The exponent is independent of the machine height, the choice of its asymptotic
multiplier, the original data, previous field addresses, and the absolute date. -/
theorem uniform_width (A : ℕ) :
    ∃E : ℕ,∀ᶠ j : ℕ in atTop,∀z : Sample,z.LocalAt G board D f g C packet j A →
      (z.output G board D f g C packet).groupWidth≤ scale j E :=by
  let ι (j : ℕ):={s : Sample // s.LocalAt G board D f g C packet j A}
  let z (j : ℕ) (i : ι j):=i.val
  let p (j : ℕ) (i : ι j):=(z j i).output G board D f g C packet
  have localFields : CalendarInputs G board D f g C packet id z :=by
    have window : SmallAt id (fun j (i:ι j)=>2^(z j i).k):=⟨A,Eventually.of_forall fun _ i=>i.property.block⟩
    have cap : SmallAt id (fun j (i:ι j)=>let b:=z j i;
        ((capCalendar G.b b.sched.rounds g b.sched.height).take b.age).prod*256) :=
      ⟨A,Eventually.of_forall fun _ i=>i.property.cap⟩
    exact {
      sheets:=CandidateSheets.local_fields id board D f g (fun j i=>(z j i).sched)
        (fun j i=>(z j i).k) (fun j i=>(z j i).tail) (fun j i=>(z j i).age)
        (fun j i=>let b:=z j i;((capCalendar G.b b.sched.rounds g b.sched.height).take b.age).prod*256)
        (fun j i=>(z j i).lanes) window cap
      previousCap:=cap,dimension:=⟨A,Eventually.of_forall fun _ i=>i.property.dim⟩,
      controls:=⟨A,Eventually.of_forall fun _ i=>i.property.root⟩,
      rootOutput:=⟨A,Eventually.of_forall fun _ i=>i.property.primaries⟩,
      funded:=⟨A,Eventually.of_forall fun _ i=>i.property.quantities⟩,
      paid:=⟨A,Eventually.of_forall fun _ i=>i.property.paid⟩,
      coefficient:=⟨A,Eventually.of_forall fun _ i=>i.property.coefficient⟩,
      primitive:=⟨A,Eventually.of_forall fun _ i=>i.property.token⟩,
      «arguments» :=⟨A,Eventually.of_forall fun _ i=>i.property.arguments⟩,
      nodes:=⟨A,Eventually.of_forall fun _ i=>i.property.nodes⟩,fibres:=fun _ i=>i.property.fibres }
  obtain ⟨E,room⟩:=group_width_scale id p (from_calendar_inputs G board D f g C packet id z localFields)
  exact ⟨E,room.mono fun j atj a ha=>atj ⟨a,ha⟩⟩

theorem uniform_half (A : ℕ) :
    ∃E : ℕ,∀B : ℕ,0<B→2*E≤B→∀ᶠ h:ℕ in atTop,
      let j:=Nat.log 2 h/(2*B);∀z:Sample,z.LocalAt G board D f g C packet j A →
        8*(z.output G board D f g C packet).groupWidth≤h :=by
  obtain ⟨E,cut⟩:=uniform_width G board D f g C packet A
  obtain ⟨j₀,late⟩:=eventually_atTop.1 cut
  refine ⟨E,fun B pos bought=>?_⟩
  filter_upwards [eventually_home 0 0 E B pos (by simpa using bought),
    eventually_ge_atTop (2^(2*B*j₀))] with h room hh
  let j:=Nat.log 2 h/(2*B)
  have hh':2*B*j₀≤Nat.log 2 h:=Nat.le_log_of_pow_le (by decide) hh
  have hj:j₀≤j:=by rw [Nat.le_div_iff_mul_le (by omega : 0<2*B)];simpa [Nat.mul_comm] using hh'
  dsimp only
  intro z ready
  have w:=late j hj z ready
  have m:=room.2 0 1 _ (by simp [tail]) (by simp) w
  omega

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
