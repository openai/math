import OAI.Hierarchy.DescentFundedBaseNumber
import OAI.Hierarchy.DescentFundedClipChoice

namespace OAI
/-! The ordinary geometric and pricing registers before the argument pitch is purchased. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCompiler DescentRawCablePanel DescentDatedAddressBook DescentHostDegree DescentOrdinaryVenueIngress
noncomputable section
variable {F Pin:Type} [Field F] (v:PhysicalOrdinary F Pin)

theorem initial_unit (short:v.short=max (v.k+3) (Nat.clog 2 (v.area.D+1)))
    (profile:v.profile=DescentTerminalEpochBits.width v.gadget.C)
    (paid:v.venue.paidBits≤v.ticket.donorDate.amount)
    (unit:v.area.unit≤v.ticket.donorDate.amount) :
    v.fundedMaxUnit 0 ≤ NativePitch.FundedBase.upper v.area.D (2^v.area.k) v.area.cap v.ticket.donorDate.amount :=by
  let a:=v.area
  let d:=v.ticket.donorDate
  let r:=2^a.k
  let money:=d.amount
  let P:=(a.D+1)^4
  let slots:=2^packExponent 20 a.D+2
  let span:=(2^(a.k+1)-1)*slots
  let raw:=2^(a.k+1)*slots
  let names:=Nat.clog 2 (span+1)
  let rawBits:=Nat.clog 2 (raw+1)
  let donors:=P*r
  let actors:=donors*(1+a.cap*6)
  have panel:v.fundedPanelUnit=money:=by unfold fundedPanelUnit;rw [short,profile]; rfl
  have total:DepotRAM.totalBits d.format≤ money:=le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  have calcClip:=v.fundedClip_named 0 short profile
  rw [fundedMaxUnit,panel,calcClip]
  let controls:=max ((Nat.clog 2 (P+1))+1)
    (max rawBits (max (1+rawBits) (names*actors+names)))
  change max money (max a.unit
    (max (max 2 (max (DepotRAM.totalBits d.format+1*r) controls))
      (max (max (v.venue.paidBits*donors+v.venue.paidBits)
         (max (names*actors) (1*actors+v.venue.paidBits*donors))) 0)))≤_
  have quant:v.venue.paidBits*donors≤ money*donors:=Nat.mul_le_mul_right donors paid
  have numeral:=Nat.add_le_add quant paid
  have live:=Nat.add_le_add_left quant (1*actors)
  have point: max (v.venue.paidBits*donors+v.venue.paidBits)
      (max (names*actors) (1*actors+v.venue.paidBits*donors))≤
      max (money*donors+money) (max (names*actors) (1*actors+money*donors)) :=
    max_le_max numeral (max_le_max le_rfl live)
  let bound:=max money (max money (max (max 2 (max (money+1*r) controls))
    (max (max (money*donors+money) (max (names*actors) (1*actors+money*donors))) 0)))
  apply le_trans (b:=bound)
  · exact max_le_max le_rfl (max_le_max unit (max_le_max
      (max_le_max le_rfl (max_le_max (Nat.add_le_add_right total _) le_rfl))
      (max_le_max point le_rfl)))
  · apply le_of_eq
    simp only [bound,controls,names,rawBits,span,raw,actors,donors,slots,P,r,money,d,a,
      NativePitch.FundedBase.upper,pow_succ 2 v.area.k]

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
