import OAI.Hierarchy.DescentNamedOrdinaryVenue
import OAI.Hierarchy.DescentSignedCableFields

namespace OAI
/-! # Density and field capacity of the original ordinary signed return bank -/
namespace Hierarchy.DescentDatedAddressBook.SignedStage
open DescentSIMDLookup DescentSharedCableNames
variable (q : SignedStage)

/-- Both signed cable ordinals, their opposite end and its degree are read at
the widths of the successor placement used to issue the signed fields. -/
theorem cable_width_le_unit : DescentSignedCableCodec.width q.newDegree q.newCap≤q.unit := by
  have alphabet:=q.field_room.2.1
  have degree : Packed.bits q.newDegree≤q.fieldBits :=
    Nat.clog_le_of_le_pow (((le_max_left ..).trans_lt alphabet).le)
  have cap : Packed.bits q.newCap≤q.fieldBits :=
    Nat.clog_le_of_le_pow (((le_max_right ..).trans_lt alphabet).le)
  have feed : 32*(1+q.template.fieldBits+Packed.bits q.template.oldKey+Packed.bits q.template.shortPeerKinds+
      Packed.bits q.template.reach+Packed.bits q.template.lowSites+Packed.bits (q.template.reach*q.template.lowSites))≤
      q.template.feedUnit := le_max_right ..
  have base : q.template.fieldBits=q.fieldBits := rfl
  rw [base] at feed
  have all : q.template.feedUnit≤q.unit := le_max_left ..
  unfold DescentSignedCableCodec.width
  omega

theorem venue_signed_caps (payload : ℕ) (room : 2*q.unit≤payload) :
    let M:=(q.format payload).lanes
    0<M ∧ payload≤M*(4*q.unit) ∧ M≤payload/2 ∧
      DescentSignedCableCodec.width q.newDegree q.newCap*M≤payload/2 := by
  intro M
  have occ:=occupancy payload q.unit q.positive room
  have paid : q.unit*M≤payload/2 := by rw [Nat.mul_comm];exact lanes_fit payload q.unit
  have oneLower : M≤q.unit*M := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right M q.positive
  exact ⟨occ.1,occ.2.trans_eq (by change 4*M*q.unit=M*(4*q.unit);ring),oneLower.trans paid,
    (Nat.mul_le_mul_right _ q.cable_width_le_unit).trans paid⟩
end Hierarchy.DescentDatedAddressBook.SignedStage

namespace Hierarchy.DescentSixParty.StageVenueTail.Date
open DescentCompiler DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage.Dated
variable {F : Type} [Field F]

/-- The signed source is filled by the issued ordinary format. Its pitch may
differ from the paid and alive input pitches and the destination pitch. -/
theorem atOrdinary_signed_caps (G : PoweredGadget F) (S : AtomSchedule) (gain k tail p f payload : ℕ)
    (ordinary : ℕ→Ordinary) (i sourceLanes : ℕ) :
    let q:=SignedStage.atDate G S gain k i (NativePitch.incomingHosts S (i+1))
    let d:=atOrdinary G S gain k tail p f payload ordinary i sourceLanes
    2*q.unit≤payload → 0<d.signedLanes ∧ payload≤d.signedLanes*(4*q.unit) ∧ d.signedLanes≤payload/2 ∧
      DescentSignedCableCodec.width d.degree d.cap*d.signedLanes≤payload/2 := by
  intro q d room
  exact q.venue_signed_caps payload room

end Hierarchy.DescentSixParty.StageVenueTail.Date

end OAI
