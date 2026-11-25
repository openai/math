import OAI.Hierarchy.DescentProfiledOrdinaryUniformAxes
import OAI.Hierarchy.DescentRegisteredOrdinarySurvivors
import OAI.Hierarchy.DescentSeedNumberRates

namespace OAI
/-! A common address bound for the material and signed output of an ordinary date.
The index may choose both the tail rate and the logarithmic divisor. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open DescentDatedSeedStartup DescentInitialHost DescentResetInvoice
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset drift degreeMax : ℕ)

section Point
variable (τ B h : ℕ) (x : ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h)
local notation "epoch" => Nat.log 2 h/(2*B)
local notation "S" => stageNumbers G t epoch f g reset x.slot.sites (tail τ epoch)
local notation "k" => groupBits t epoch (hostRate t reset) (capRate G t g) (cutRate t f g)

structure SignedAdmission : Prop where
  axes : RawLimits G board op t f g reset τ drift degreeMax B h x
  packed : 2*(SignedStage.atDate G S g k x.slot.age (NativePitch.incomingHosts S (x.slot.age+1))).unit ≤ h

theorem signed_admission (slack : SignedStage.unitRate G t f g reset < B) :
    ∀ᶠ height : ℕ in atTop, ∀ y : ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B height,
      SignedAdmission G board op t f g reset drift degreeMax τ B height y := by
  filter_upwards [raw_limits G board op t f g reset τ drift degreeMax B,
    SignedStage.unitRate_cofinal G t f g reset B slack] with height axes room
  exact fun y => ⟨axes y, room _ _ _ _ y.slot.active.le⟩
end Point

section Family
variable {ι : ℕ → Type*} (tailRate budget : ∀ h, ι h → ℕ)
    (point : ∀ h (i : ι h), ProfiledOrdinaryOffer G f g board op t reset (tailRate h i) drift degreeMax (budget h i) h)
local notation "x_" h:arg i:arg => point h i
local notation "v_" h:arg i:arg => (point h i).model
local notation "age_" h:arg i:arg => (point h i).slot.age
local notation "J_" h:arg i:arg => Nat.log 2 h/(2*budget h i)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h i) f g reset (point h i).slot.sites (tail (tailRate h i) (J_ h i))
local notation "k_" h:arg i:arg => groupBits t (J_ h i) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "d_" h:arg i:arg => DonorDate.atDate G (S_ h i) g (k_ h i) (age_ h i) (point h i).slot.p
local notation "H_" h:arg i:arg => NativePitch.incomingHosts (S_ h i) (age_ h i+1)
local notation "q_" h:arg i:arg => SignedStage.atDate G (S_ h i) g (k_ h i) (age_ h i) (H_ h i)

theorem material_and_survivor
    (admitted : ∀ h i, SignedAdmission G board op t f g reset drift degreeMax (tailRate h i) (budget h i) h (x_ h i)) :
    MaterialExtent.ScalarRoom (fun h i => (v_ h i).material) ∧ Bounded (fun h i => (v_ h i).survivorWords) := by
  have host : Bounded (fun h i => (S_ h i).hostSize (age_ h i)) :=
    ⟨4,Eventually.of_forall fun h i => (admitted h i).axes.oldHost⟩
  have nextHost : Bounded (fun h i => (S_ h i).hostSize (age_ h i+1)) :=
    ⟨4,Eventually.of_forall fun h i => (admitted h i).axes.newHost⟩
  have axis {a : ∀ h, ι h → ℕ} (ha : ∀ h i, a h i ≤ 2^h) : Bounded a :=
    ⟨1,Eventually.of_forall fun h i => by simpa only [Nat.one_mul] using ha h i⟩
  have oldGroups : Bounded (fun h i => (S_ h i).groupCount (age_ h i)) := axis fun h i => (admitted h i).axes.oldGroup
  have groups : Bounded (fun h i => (S_ h i).groupCount (age_ h i+1)) := axis fun h i => (admitted h i).axes.newGroup
  have blocks : Bounded (fun h i => 2^(k_ h i)) := axis fun h i => (admitted h i).axes.blocks
  have degrees : Bounded (fun h i => (d_ h i).degree) := axis fun h i => (admitted h i).axes.degree
  have caps : Bounded (fun h i => (d_ h i).cap) := axis fun h i => (admitted h i).axes.wires
  have old (h) (i : ι h) : (v_ h i).ticket.donorDate=d_ h i := congrArg PhysicalOrdinary.StaticCore.donor (point h i).core
  have area (h) (i : ι h) : (v_ h i).area=(d_ h i).schedule h
      ((point h i).slot.menu.seats (age_ h i)) ((S_ h i).censusBits (point h i).slot.p) :=
    congrArg PhysicalOrdinary.StaticCore.area (point h i).core
  have output (h) (i : ι h) : (v_ h i).signed=(q_ h i).format h :=
    congrArg PhysicalOrdinary.StaticCore.signed (point h i).core
  have H : Bounded (fun h i => H_ h i) := nextHost.padded.of_le fun h i =>
    (NativePitch.hosts_bounds _ _ (point h i).slot.active).2
  have oldH : Bounded (fun h i => (v_ h i).area.H) := host.padded.of_le fun h i => by rw [area]; rfl
  have cap (h) (i : ι h) : (v_ h i).prior.placement.cap=(d_ h i).cap := congrArg DonorDate.cap (old h i)
  have positive (h) (i : ι h) : 256 ≤ (v_ h i).prior.placement.cap := by
    rw [cap]
    exact Nat.le_mul_of_pos_left _ (DonorDate.prefix_cap_pos G.b t g (J_ h i) (age_ h i) (by have := G.paid; omega))
  have material := PhysicalOrdinary.material_extent_room (fun h i => v_ h i) (fun _ _ => rfl)
    (fun h i => Branch.signed_at (point h i).cut.original G (S_ h i) (point h i).cut.branch
      (point h i).cut.ticket (point h i).cut.before (point h i).cut.after (point h i).cut.joined h)
    positive oldH (oldGroups.of_le fun h i => by rw [area]; rfl)
    (H.of_le fun h i => by rw [output]; rfl)
    (groups.of_le fun h i => by rw [output]; rfl)
    (blocks.of_le fun h i => by rw [show (v_ h i).k=k_ h i from congrArg DonorDate.exponent (old h i)])
    (degrees.of_le fun h i => (congrArg DonorDate.degree (old h i)).le)
    (caps.of_le fun h i => (cap h i).le)
  have nextDegree : Bounded (fun h i => (v_ h i).venue.degree) := by
    let limit := (Finset.range (initialDegreeMax t+1)).sup ordinaryDegree
    apply (Bounded.const limit).of_le
    intro h i
    change ordinaryDegree (d_ h i).degree ≤ limit
    exact Finset.le_sup (s := Finset.range (initialDegreeMax t+1)) (f := ordinaryDegree)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (seed_degree t G.b _)))
  have oldDegree : Bounded (fun h i => (v_ h i).area.D) :=
    degrees.of_le fun h i => by rw [area]; rfl
  have peer := DescentOrdinaryVenueReturn.rate oldH oldDegree
    (H.of_le fun h i => (congrArg (fun c : PhysicalOrdinary.StaticCore => c.prefixProgram.nextHosts) (point h i).core).le) nextDegree
  have mark := VenueProgram.Registered.atAge_mark_room G (fun h i => S_ h i) (fun _ _ => g)
    (fun h i => k_ h i) (fun h i => age_ h i) (fun h i => (point h i).slot.p)
    (fun h i => (point h i).slot.active) host nextHost groups blocks degrees caps
  have marks : Bounded (fun h i => (v_ h i).markShape.endAddress 0) :=
    (DescentOrdinaryMarkProject.Shape.extent_rate _ mark).of_le fun h i =>
      (congrArg (fun c : PhysicalOrdinary.StaticCore => c.prefixProgram.marked.endAddress 0) (point h i).core).le
  have signed := SignedStage.format_scalar_room (fun h i => q_ h i) host.padded H groups (fun h i => (admitted h i).packed)
  have roof : Bounded (fun h i => (v_ h i).signed.roof 0) :=
    (SignedExtent.rate _ signed).of_le fun h i => by rw [output]
  have reverse := PhysicalOrdinary.reverse_from_material (fun h i => v_ h i) material
  exact ⟨material,(((reverse.add (MaterialExtent.extent_rate _ material)).add peer).add marks).add roof⟩
end Family
end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
