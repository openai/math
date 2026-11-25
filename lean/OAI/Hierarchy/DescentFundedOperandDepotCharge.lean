import OAI.Hierarchy.DescentDatedOperandPageTariff
import OAI.Hierarchy.DescentDatedOperandOriginalHeads
import OAI.Hierarchy.DescentMaterialIssuedDigit
import OAI.Hierarchy.DescentNativePhaseInvoice

namespace OAI
/-! # Direct price of the raw immutable operand-page scans on the original material panel -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedOperandPages DescentDatedAddressBook DescentSIMDLookup DescentRawCablePanel
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
local notation "fmt" => v.ticket.depotShape v.short
local notation "h" => v.payload
local notation "q" => v.signedLayout
local notation "U" => v.ticket.installedDonorWidth v.short v.profile

def operandDepotCharge (ratio : ℕ) :=
  let N:=count fmt
  let H:=v.material.oldHosts
  let G:=v.material.oldGroups
  2048*ratio*(N+1)*(h+H*h+H*G*(4*U))+2048*ratio*(N+1)*2^(h/2)*h+
  2048*ratio*(h+2*(N*H)*h+(N*H)*G*(4*U+4*(q).unit))+(2048*ratio)*(2*(h+1)^2*2^(h/2))*h

theorem operand_depot_charge (A : v.ArgumentEntry) (floor w ratio : ℕ)
    (selected : v.signed=(q).format h) (cap : 256≤ v.prior.placement.cap)
    (oldRoom : 2*U≤ h) (newRoom : 2*(q).unit≤ h) (bus : w≤ ratio*h) :
    (v.operandDepot floor w A).wordInvoice≤ v.operandDepotCharge ratio :=by
  have wide:=v.signed_digit_fits cap
  have upos : 0<U:=by omega
  have one : 0<lanes h U:=Nat.div_pos oldRoom (by omega)
  have two : 0<lanes h (q).unit:=Nat.div_pos newRoom (by have u:=(q).positive;omega)
  have active : 0<(fmt).blocks:=Nat.two_pow_pos _
  have code : 0<(q).fieldBits:=by
    unfold SignedStage.fieldBits
    apply Nat.clog_pos (by decide : 1<2)
    omega
  have keys : DepotRAM.totalBits fmt≤ U :=by
    have t : 2*DepotRAM.totalBits fmt+1≤ U:=(le_max_right ..).trans (le_max_right ..)
    omega
  have oldLimit (n : ℕ) (bound : n≤ U) : n*lanes h U≤ h/2:=by
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_left _ bound).trans (lanes_fit h U)
  have blocks : (fmt).blocks=2^(q).k:=rfl
  have newLimit : lanes h (q).unit*(fmt).blocks≤ h:=by
    have k : (fmt).blocks≤(q).fieldBits*(fmt).blocks+(q).fieldBits:=by
      have m:=Nat.mul_le_mul_right (fmt).blocks code
      omega
    have cap₂:=(q).material_width h
    change ((q).fieldBits*2^(q).k+(q).fieldBits)*lanes h (q).unit≤ h/2 at cap₂
    rw [←blocks] at cap₂
    have z:= (Nat.mul_le_mul_right (lanes h (q).unit) k).trans cap₂
    rw [Nat.mul_comm]
    omega
  have hOld : h≤ lanes h U*(4*U):=(occupancy _ _ upos oldRoom).2.trans_eq (by ring)
  have hNew : h≤(lanes h (q).unit*(fmt).blocks)*(4*(q).unit):=by
    have fit:=(occupancy _ _ (q).positive newRoom).2.trans_eq (by ring : _=lanes h (q).unit*(4*(q).unit))
    apply fit.trans
    gcongr
    exact Nat.le_mul_of_pos_right _ active
  have retile:=phase_word_bill fmt v.operandDepotLayout (v.originMouthEnd floor) w h (4*U) (4*(q).unit) ratio A.venue.panel
  apply retile
  · exact Nat.div_le_self ..
  · change v.signed.lanes*(fmt).blocks≤ h
    rw [selected];exact newLimit
  · exact one
  · change 0<v.signed.lanes*(fmt).blocks
    rw [selected];exact Nat.mul_pos two active
  · exact oldLimit _ keys
  · change v.signed.fieldBits*lanes h U≤ h/2
    rw [selected]
    exact oldLimit (q).fieldBits (Nat.le_of_succ_le wide)
  · exact hOld
  · change h≤(v.signed.lanes*(fmt).blocks)*(4*(q).unit)
    rw [selected];exact hNew
  · exact bus

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
