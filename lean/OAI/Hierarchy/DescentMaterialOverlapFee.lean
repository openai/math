import OAI.Hierarchy.DescentDatedMaterialPhase
import OAI.Hierarchy.DescentPhysicalSignedLayout
import OAI.Hierarchy.DescentOverlapLaneBill

namespace OAI
/-! # Repacking the ordinary donor observations for the signed successor -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentSIMDLookup DescentStaticWordColumn
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

/-- The occupied host rows are those of the actual donor sheets. The shared
literal tables are charged once for every possible source-word displacement. -/
theorem material_overlap_fee (base w ratio : ℕ)
    (width : v.signedLayout.fieldBits+1 ≤ v.ticket.installedDonorWidth v.short v.profile)
    (oldRoom : 2*v.ticket.installedDonorWidth v.short v.profile ≤ v.payload)
    (newRoom : 2*v.signedLayout.unit ≤ v.payload) (machine : w ≤ ratio*v.payload) :
    let x:=v.withIssuedSigned
    let e:=x.material
    let j:=x.materialJob base
    let p:=j.phase (e.overlapStart base) w
    let U:=v.ticket.installedDonorWidth v.short v.profile
    (p.ticks+7*names p.program)*w ≤
      2048*((4*U*e.blocks+3)*2^(v.payload/2) +
        (e.fields*e.oldHosts)*chunks e.oldGroups e.oldLanes +
        (e.fields*e.oldHosts)*chunks e.oldGroups (e.lanes*e.blocks)+1)*(ratio*v.payload) := by
  let x:=v.withIssuedSigned
  let e:=x.material
  let j:=x.materialJob base
  let U:=v.ticket.installedDonorWidth v.short v.profile
  have blockPos : 0<e.blocks := Nat.two_pow_pos v.k
  exact Overlap.lane_bill (e.overlapStart base) (e.fields*e.oldHosts) e.oldGroups
    v.payload U v.signedLayout.unit e.blocks e.fieldBits w ratio j.src width oldRoom
    v.signedLayout.positive newRoom blockPos machine

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
