import OAI.Hierarchy.DescentProfiledOrdinaryEntry
import OAI.Hierarchy.DescentProfiledOrdinaryBookRooms
import OAI.Hierarchy.DescentRegisteredReferenceAddress
import OAI.Hierarchy.DescentRegisteredOrdinaryResultRoom

namespace OAI
/-! The native origin, reference, and mouth banks on the original offered cut have one address exponent. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open DescentPacking.PackedMatch.Local.Stage Filter
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset τ drift degreeMax B : ℕ)
local notation "idx" h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "tb_" h:arg => tail τ (J_ h)
local notation "S_" h:arg x:arg => stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tb_ h)
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "date_" h:arg x:arg => DonorDate.atDate G (S_ h x) g (k_ h) (x).slot.age (x).slot.p
local notation "v_" => fun h (x : idx h) => x.model
local notation "prior_" x:arg => (x).slot.position.ports
local notation "seats_" x:arg => (x).slot.menu.seats (x).slot.age

private theorem signed_digits (q : SignedStage) :
    32 ≤ q.unit ∧ q.fieldBits ≤ q.unit ∧ DescentSharedCableNames.Packed.bits (DescentHaloWalkRAM.breadth q.oldDegree) ≤ q.unit := by
  have l := show 32*(1+q.template.fieldBits+
      DescentSharedCableNames.Packed.bits q.template.oldKey+DescentSharedCableNames.Packed.bits q.template.shortPeerKinds+
      DescentSharedCableNames.Packed.bits q.template.reach+DescentSharedCableNames.Packed.bits q.template.lowSites+
      DescentSharedCableNames.Packed.bits (q.template.reach*q.template.lowSites))≤q.template.feedUnit from le_max_right ..
  have a : q.template.fieldBits=q.fieldBits := rfl
  have b : q.template.reach=DescentHaloWalkRAM.breadth q.oldDegree := rfl
  have u : q.template.feedUnit≤q.unit:=le_max_left ..
  rw [a,b] at l
  omega

theorem short_digits (slack : SignedStage.unitRate G t f g reset < B) :
    ∀ᶠ h : ℕ in atTop,∀x : idx h,x.model.operandShortBits ≤ h := by
  let r:=SignedStage.unitRate G t f g reset
  have zero:=SignedStage.unitRate_atDate G t f g reset 0 0 0 0 0 (Nat.zero_le _)
  have high : 3≤r := by
    by_contra! small
    have ur : 2^r≤2^2:=Nat.pow_le_pow_right (by decide) (by omega)
    rw [TerminalScale.scale,Nat.zero_add,Nat.mul_one] at zero
    have bottom := (signed_digits _).1.trans zero
    change 32≤2^r at bottom
    omega
  filter_upwards [AgeBound.payload_room r B slack, DescentOperandWidth.issued G drift degreeMax t f g reset τ B (by omega)] with h wide record
  intro x
  have allotted : scale (J_ h) r ≤ h :=
    (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)).trans wide
  let v:=x.model
  have width:=OrdinaryBooks.record_width G (S_ h x) op g (k_ h) (x).slot.age (x).slot.p (tb_ h) drift x.slot.degree h
    (seats_ x) (prior_ x)
  have fitted:=record x.slot.sites x.slot.p x.slot.degree x.slot.grainLimit x.slot.degreeLimit
  have grow : scale (J_ h) 3≤ scale (J_ h) r :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ high)
  have small : v.resolver.size+2≤h := width.1.trans_le (fitted.trans (grow.trans allotted))
  have bwidth : v.bornBook.bits=v.resolver.size+2:=width.2.2.1
  have raw := Branch.signed_stage_eq x.cut.original G (S_ h x) x.cut.branch x.cut.ticket x.cut.before x.cut.after x.cut.joined
    (NativePitch.incomingHosts (S_ h x) (x.slot.age+1))
  have issued:=SignedStage.unitRate_atDate G t f g reset (J_ h) x.slot.sites (tb_ h) x.slot.age
    (NativePitch.incomingHosts (S_ h x) (x.slot.age+1)) x.slot.active.le
  have room : v.signedLayout.unit≤h := (congrArg SignedStage.unit raw).le.trans (issued.trans allotted)
  have sz := (signed_digits v.signedLayout).2
  have field : v.material.fieldBits=v.signedLayout.fieldBits :=congrArg SignedStage.fieldBits raw.symm
  exact max_le (max_le (field.le.trans (sz.1.trans room)) small) (max_le (bwidth.le.trans small) (sz.2.trans room))

set_option maxHeartbeats 1000000 in
theorem reference (slack : SignedStage.unitRate G t f g reset < B) (tailRoom : τ ≤ B) :
    Bounded (fun h (x : idx h) => x.model.referenceWords) := by
  have den : 0 < B := by omega
  have geo := geometry G board op t f g reset τ drift degreeMax B
  have pr := primitive_room G board op t f g reset τ drift degreeMax B den
  have area (h : ℕ) (x : idx h) : x.base.area=(date_ h x).schedule h (seats_ x) ((S_ h x).censusBits x.slot.p) :=
    congrArg PhysicalOrdinary.StaticCore.area x.core
  apply PhysicalOrdinary.registered_reference_rate (ι := fun h => idx h) (Pin := fun h (x : idx h) => x.Pins)
    (fun h (x : idx h) => x.base) (fun h (x : idx h) => prior_ x) (fun h (x : idx h) => x.stageFloor)
  refine ⟨entry G board op t f g reset τ drift degreeMax B den,
    (survivor_cost G board op t f g reset τ drift degreeMax B slack tailRoom).1,
    (operand_room G board op t f g reset τ drift degreeMax B den).resolver,?_,?_,pr.cap,pr.old,
    pr.hosts,pr.donorHosts,?_,Eventually.of_forall (fun _ _ => le_rfl),?_,⟨1,by
      filter_upwards [short_digits G board op t f g reset τ drift degreeMax B slack] with h good
      intro x
      rw [Nat.one_mul]
      exact good x⟩⟩
  · exact geo.degree.of_le (fun h x => (congrArg Dated.Ordinary.D (area h x)).le)
  · exact geo.blocks.of_le (fun h x => (congrArg (fun a : Dated.Ordinary => 2^a.k) (area h x)).le)
  · intro h x
    exact ((prior_ x).ordinary_header_dimensions x.cut.ticket op g (tb_ h) x.slot.p f drift x.slot.degree h
      (seats_ x) x.slot.position.floor x.slot.menu.ordinary x.slot.active x.cut.radix).2.2.2
  · intro h x
    exact (Branch.signed_at x.cut.original G (S_ h x) x.cut.branch x.cut.ticket x.cut.before
      x.cut.after x.cut.joined h).symm

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
