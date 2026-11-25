import OAI.Hierarchy.DescentSignedBitCeiling
import OAI.Hierarchy.DescentMaterialDigitSpace
import OAI.Hierarchy.DescentPhysicalSignedFormat

namespace OAI
/-! # The signed group retile reads the true old donor pitch without an extra setup -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentHostDegree DescentCompiler
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem signed_digit_fits (cap : 256≤v.prior.placement.cap) :
    v.signedLayout.fieldBits+1≤v.ticket.installedDonorWidth v.short v.profile := by
  let s:=v.ticket.depotShape v.short
  let q:=v.signedLayout
  have bpos : 0<q.radix:=by have paid:=v.gadget.paid;change 0<v.gadget.b;omega
  have newD : q.newDegree=ordinaryDegree q.oldDegree:=by
    change v.target.placement.degree=ordinaryDegree v.prior.placement.degree
    rw [v.target.branch,v.ticket.nextDegree,v.prior.branch]
  have newCap : q.newCap=2^gainExponent 20 q.oldDegree*q.radix*q.oldCap:=by
    change v.target.placement.cap=2^gainExponent 20 v.prior.placement.degree*v.gadget.b*v.prior.placement.cap
    rw [v.prior.branch,v.ticket.capacity]
  have top:=q.fieldBits_ceiling newD newCap bpos
  have baseSize : 256≤q.donorUnits:=by
    exact (cap.trans (Nat.le_mul_of_pos_right q.oldCap bpos)).trans (le_max_left ..)
  have lowerWidth : 9≤ s.widths:=by
    have space:=Nat.le_pow_clog (by decide : 1<2) (q.donorUnits+1)
    change q.donorUnits+1≤2^s.widths at space
    by_contra! small
    have lim : 2^s.widths≤256:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show s.widths≤8 by omega)
    omega
  have bottom:=DepotRAM.material_digit_space s v.k rfl cap lowerWidth
  change q.fieldBits≤1000+1900*logDegree s.degree+2*v.k+3*s.widths at top
  have installed:= (v.ticket.installed_donor_widths v.short v.profile).2.2
  change 2*DepotRAM.totalBits s+1≤_ at installed
  change q.fieldBits + 1 ≤ v.ticket.installedDonorWidth v.short v.profile
  omega

end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
