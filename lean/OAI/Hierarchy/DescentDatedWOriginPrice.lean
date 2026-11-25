import OAI.Hierarchy.DescentDatedWOrigin
import OAI.Hierarchy.DescentFundedOriginReturn

namespace OAI
/-! # Charge the original W actor stamp and its six retained coordinate lookups -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryOriginPorts DescentOrdinaryReferenceInputs DescentStaticWordColumn
open DescentOrdinaryAtomFieldRAM DescentPacking.PackedMatch.Local
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (extra : ℕ)
local notation "e" => v.withFundedClip extra
local notation "R" => (e).originChart
local notation "h" => v.payload
local notation "r" => (v.fundedClip extra).radix
local notation "J" => v.vector.groups
local notation "Q" => v.vector.lows
local notation "H" => v.vector.hosts
local notation "K₁" => (e).resolver.nodes

theorem originPort_work (floor outBits : ℕ) (block : Fin v.vector.radix) (node : Fin v.resolver.nodes) (field : Fin 6) :
    (v.originPort floor outBits block node field).work≤32 :=
  DescentOperandFamilyBook.expr_work (law v.originChart outBits) v.vector.lanes (v.originPortFloor floor)
    (finProdFinEquiv (node,field)) _ 7 (fun _=>le_rfl)

theorem funded_origin_chart :
    v.originReturn extra (e).reference (e).vector K₁ (e).originBits=(R):=rfl

theorem funded_origin_ports (selection : (R).peak≤extra) :
    words (R)≤(1+K₁*6)*(2*2^(h/2)):=by
  have cap: (R).ordinalBits*(R).newNodes≤extra :=(Nat.le_max_right ..).trans selection
  have quarter:=(v.funded_extra_fit extra ((R).ordinalBits*(R).newNodes) cap).2.2
  have both: (((R).ordinalBits*(R).newNodes)*1+(R).ordinalBits*(R).newNodes)*(R).lanes≤h/2:=by
    rw [Nat.mul_one,Nat.add_mul]
    change _*(v.fundedClip extra).postPitch+_*(v.fundedClip extra).postPitch≤h/2
    omega
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (n:=2) (by decide) both))

theorem funded_w_origin_at (refBase : ℕ) (D : Directory ((e).reference.withBase refBase) (e).vector) (pg : Fin (e).vector.pageCount)
    (floor bits w ratio : ℕ) (selection : (R).peak≤extra)
    (paid : 0<v.venue.paidBits) (input : v.venue.paidBits≤v.area.unit)
    (room : 4*v.fundedMaxUnit extra*2^v.area.k≤h) (bus : w≤ratio*h) :
    let code:=(e).originPrefix floor bits w (D.refs pg)
    (code.ticks+7*names code.program)*w≤ratio*(2600*(Q+1)*h+
      (160+300*r)*((H*Q)*h+(H*Q)*J*(r*v.fundedWorkingUnit extra))+
      115*((4+r)*2^(h/2))*h+(109+115*((1+K₁*6)*(2*2^(h/2))))*h) :=by
  intro code
  have origin:=v.funded_origin_scaled D extra K₁ (e).originBits ((e).routedStart floor) w ratio pg
    selection paid input room bus
  have names_ : names (DescentOrdinaryOriginPorts.program (R) bits ((e).originPortFloor floor) w)=15*(words (R)+1):=by
    apply names_mount
  have ops : code.ticks+7*names code.program =
      ((R).ticks (D.refs pg) ((e).routedStart floor)+7*names ((R).program (D.refs pg) w ((e).routedStart floor))) +
      (109+115*words (R)) :=by
    change ((R).ticks (D.refs pg) ((e).routedStart floor)+(4+10*words (R)))+7*names (((R).program (D.refs pg) w ((e).routedStart floor)).seq
      (DescentOrdinaryOriginPorts.program (R) bits ((e).originPortFloor floor) w))=_
    rw [names_seq,names_]
    omega
  have ports:=Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 115 (v.funded_origin_ports extra selection)) 109) bus
  rw [ops,Nat.add_mul]
  apply (Nat.add_le_add origin ports).trans_eq
  simp only [show (e).vector.lows=Q from rfl,show (e).vector.hosts=H from rfl,
    show (e).vector.groups=J from rfl]
  ring

theorem funded_w_origin (D : Directory (e).reference (e).vector) (pg : Fin (e).vector.pageCount)
    (floor bits w ratio : ℕ) (selection : (R).peak≤extra)
    (paid : 0<v.venue.paidBits) (input : v.venue.paidBits≤v.area.unit)
    (room : 4*v.fundedMaxUnit extra*2^v.area.k≤h) (bus : w≤ratio*h) :
    let code:=(e).originPrefix floor bits w (D.refs pg)
    (code.ticks+7*names code.program)*w≤ratio*(2600*(Q+1)*h+
      (160+300*r)*((H*Q)*h+(H*Q)*J*(r*v.fundedWorkingUnit extra))+
      115*((4+r)*2^(h/2))*h+(109+115*((1+K₁*6)*(2*2^(h/2))))*h) :=by
  exact v.funded_w_origin_at extra (e).reference.base D pg floor bits w ratio selection paid input room bus

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
