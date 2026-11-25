import OAI.Hierarchy.DescentProfiledOrdinaryEntry
import OAI.Hierarchy.DescentProfiledOrdinaryUniformPrimitive

namespace OAI
/-! The original predecessor operand and role pages have common address coefficients
even when the offers in a family use different logarithmic divisors and tails. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage Filter
open DescentRawCablePanel DescentPacking.PackedMatch.Local
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (t f g reset drift degreeMax : ℕ)
local notation "offer" τ:arg B:arg h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "prev" x:arg => (x).slot.position.ports

variable {G board op t f g reset drift degreeMax} in
structure EntryAdmission {τ B h : ℕ} (x : offer τ B h) : Prop where
  raw : RawLimits G board op t f g reset τ drift degreeMax B h x
  low : x.model.vector.lows ≤ 2^h
  nodes : (prev x).nodes ≤ 2^h
  args : (prev x).argumentsPerNode ≤ 2^h
  freshNodes : x.model.resolver.nodes ≤ 2^h
  freshArgs : x.model.vector.operands ≤ 2^h

theorem entry_admission (τ drift degreeMax B : ℕ) (den : 0 < B) :
    ∀ᶠ h : ℕ in atTop, ∀ x : ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h, x.EntryAdmission := by
  let localRate := OrdinaryBooks.primitiveLocalRate G t f g reset
  let argsRate := (drift+1)+operandExponent G (stageNumbers G t 0 f g reset 0 0)
  filter_upwards [raw_limits G board op t f g reset τ drift degreeMax B,
    OrdinaryBooks.primitive_date_local G op t f g reset τ B drift degreeMax den,
    dyadic_log_room localRate 1,dyadic_log_room argsRate 1] with h limits size localRoom argsRoom
  intro x
  let J := Nat.log 2 h/(2*B)
  let S := stageNumbers G t J f g reset x.slot.sites (tail τ J)
  have cap {r : ℕ} (room : r*(Nat.log 2 h+1)^1 ≤ h) : scale J r ≤ 2^h := by
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    exact (Nat.mul_le_mul_left r (Nat.add_le_add_right (Nat.div_le_self ..) 1)).trans
      (by simpa only [pow_one] using room)
  have controls := size x.slot.sites x.slot.age x.slot.p x.slot.degree (x.slot.menu.seats x.slot.age)
    (prev x) x.slot.grainLimit x.slot.degreeLimit
    (previous_nodes G board op t f g reset τ drift degreeMax B h x) x.firstWidth
  have driftFit : drift+1 ≤ scale J (drift+1) :=
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans Nat.lt_two_pow_self.le
  have newArgs : S.retainedArgumentsAt G drift ≤ scale J argsRate :=
    (S.capacities_at_scale G drift (drift+1) driftFit).2
  have priorArgs := x.slot.geometry.room.args.trans newArgs
  exact ⟨limits x,x.primitive_shape.lows.le.trans (controls.2.2.2.2.2.2.trans (cap localRoom)),
    controls.2.2.2.2.1.trans (cap localRoom),priorArgs.trans (cap argsRoom),
    controls.2.2.2.1.trans (cap localRoom),
    (max_le x.slot.geometry.room.args (le_refl (S.retainedArgumentsAt G drift))).trans (newArgs.trans (cap argsRoom))⟩

variable {ι : ℕ → Type*} (tau denom : ∀ h, ι h → ℕ)
  (point : ∀ h (i : ι h), ProfiledOrdinaryOffer G f g board op t reset (tau h i) drift degreeMax (denom h i) h)
attribute [local irreducible] Origin.source Origin.archivePackage

set_option maxHeartbeats 1000000 in
theorem uniform_entry (admission : ∀ h i, (point h i).EntryAdmission) :
    PhysicalOrdinary.EntryAddressInputs (F := F) (ι := ι) (fun h (i : ι h) => (point h i).base) (fun h i => (point h i).slot.position.ports)
      (fun h i => (point h i).stageFloor) := by
  let epoch (h : ℕ) (i : ι h) := Nat.log 2 h/(2*denom h i)
  let sched (h : ℕ) (i : ι h) :=
    stageNumbers G t (epoch h i) f g reset (point h i).slot.sites (tail (tau h i) (epoch h i))
  let bits (h : ℕ) (i : ι h) :=
    groupBits t (epoch h i) (hostRate t reset) (capRate G t g) (cutRate t f g)
  let donor (h : ℕ) (i : ι h) :=
    DonorDate.atDate G (sched h i) g (bits h i) (point h i).slot.age (point h i).slot.p
  have bound {v : ∀ h, ι h → ℕ} (n : ℕ) (fit : ∀ h i, v h i ≤ 2^(n*h)) : Bounded v :=
    ⟨n,Eventually.of_forall fit⟩
  have single {v : ∀ h, ι h → ℕ} (fit : ∀ h i, v h i ≤ 2^h) : Bounded v :=
    bound 1 (by simpa only [one_mul] using fit)
  have area (h : ℕ) (i : ι h) :
      (point h i).base.area=(donor h i).schedule h ((point h i).slot.menu.seats (point h i).slot.age)
        ((sched h i).censusBits (point h i).slot.p) :=
    congrArg PhysicalOrdinary.StaticCore.area (point h i).core
  have socket (h : ℕ) (i : ι h) : ((point h i).base.registeredEntry (point h i).slot.position.ports (point h i).stageFloor).clip.venue.socket=(donor h i).format :=
    congrArg PhysicalOrdinary.StaticCore.format (point h i).core
  have host : Bounded (fun h i => hostRows ((sched h i).hostSize (point h i).slot.age)) :=
    (bound 4 (v:=fun h i => (sched h i).hostSize (point h i).slot.age)
      (fun h i => (admission h i).raw.oldHost)).padded
  apply PhysicalOrdinary.registered_entry_source_bounds
  · exact host.of_le (fun h i => (congrArg Dated.Ordinary.H (area h i)).le)
  · exact single (fun h i => (congrArg Dated.Ordinary.G (area h i)).le.trans (admission h i).raw.oldGroup)
  · exact single (fun h i => (congrArg DepotRAM.Shape.degree (socket h i)).le.trans (admission h i).raw.degree)
  · exact single (fun h i => (congrArg DepotRAM.Shape.blocks (socket h i)).le.trans (admission h i).raw.blocks)
  · exact single (fun h i => (congrArg DepotRAM.Shape.cap (socket h i)).le.trans (admission h i).raw.wires)
  · exact single (fun h i => (admission h i).low)
  · exact single (fun h i => (congrArg (fun a : Dated.Ordinary => 2^a.k) (area h i)).le.trans (admission h i).raw.blocks)
  · exact single (fun h i => (admission h i).nodes)
  · exact single (fun h i => (admission h i).args)
  · exact host.of_le (fun h i => (point h i).slot.geometry.room.population.earlier.trans
      (point h i).slot.geometry.room.population.venue_high)
  · exact single (fun h i => (point h i).slot.geometry.room.population.groups.le.trans (admission h i).raw.oldGroup)
  · intros; rfl
  · exact Eventually.of_forall fun h i => (point h i).entry_words

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
