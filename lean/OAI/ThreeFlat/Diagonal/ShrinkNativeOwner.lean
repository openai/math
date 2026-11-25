import OAI.ThreeFlat.Diagonal.ShrinkPublishedHalves
import OAI.ThreeFlat.Diagonal.CompressorChildBits

namespace OAI
/-! # Old site numbering and the persisted physical parent map -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.ChildRows

open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalPinsExpr Placement Resident
open scoped Classical Fin.NatCast Fin.CommRing
variable {w N t l : ℕ} {B H : Type} [AddCommGroup H] {S : Graph.Stage}
variable (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (b : B ≃ Fin N) (E : Codec B w S.colors t l)
set_option quotPrecheck false
local notation "X" => dims S N t l
section
variable {d c : ℕ} (Q : PackingData B H (BitWord t) (BitWord l) d c)
abbrev Actual (_Q : PackingData B H (BitWord t) (BitWord l) d c) :=
  Computability.VPVNP.Compression.Position B H (BitWord t) (BitWord l) c

def oldLane (u : Actual Q) : BitWord c × H × BitWord t × BitWord l :=
  (u.2.1,u.2.2,u.1.2.1,u.1.2.2)

def oldNumber (b : B ≃ Fin N) (u : Actual Q) :=
  SlotImage.siteOrdinal b (Demand.laneOrdinal Q) (u.1.1,oldLane Q u)

omit [AddCommGroup H] in
theorem oldNumber_lt (b : B ≃ Fin N) (u : Actual Q) : oldNumber Q b u<N*(2^l*2^t*d*2^c) := by
  exact DescriptorSpan.half_index_lt (b u.1.1).isLt ((Demand.laneOrdinal Q) (oldLane Q u)).isLt
end

variable (cur : Word w) (mem : Memory w) (vs : Fin 1→Word w)
local notation "V" => Formula.value (fun _=>cur) mem vs
variable (code : ∀u,E.base u=((b u).val:Word w))
variable (bits : 2^S.colors<2^w) (deg : S.degree<2^w)

include code bits deg in
omit [AddCommGroup H] in
theorem unpack_code (z : F) (u : Actual P) (value : (V z).val=oldNumber P b u)
    (radix : (V (Template.f oldLanes)).val=(X).originalLanes)
    (tagsR : (V (Template.f tags)).val=2^t) :
    (unpackOld Template.ptr S z).map V=posCode P E u := by
  let a:=oldLane P u
  let all:=(Demand.laneOrdinal P a).val
  have lt : all<(X).originalLanes := (Demand.laneOrdinal P a).isLt
  have val : (V z).val=(X).originalLanes*(b u.1.1).val+all := by
    rw [value];change (b u.1.1).val*(X).originalLanes+all=_;rw [Nat.mul_comm]
  let z0:=Formula.op .mod z (Template.f oldLanes)
  let lo:=Formula.op .div z0 (.lit (2^S.colors))
  let hi:=Formula.op .div lo (.lit S.degree)
  have rem0 : (V z0).val=all := by
    change (V (.op .mod z (Template.f oldLanes))).val=_
    rw [Incidents.mod_value,radix,val,Nat.mul_add_mod,Nat.mod_eq_of_lt lt]
  have lval : (V lo).val=all/2^S.colors := by
    change (V (.op .div z0 (.lit (2^S.colors)))).val=_
    rw [Incidents.div_value,rem0,show (V (.lit (2^S.colors))).val=2^S.colors from Fin.val_cast_of_lt bits]
  have hval : (V hi).val=all/2^S.colors/S.degree := by
    change (V (.op .div lo (.lit S.degree))).val=_
    rw [Incidents.div_value,lval,show (V (.lit S.degree)).val=S.degree from Fin.val_cast_of_lt deg]
  have bx : V (.op .div z (Template.f oldLanes))=E.base u.1.1 := by
    apply Fin.ext
    have pos : 0<(X).originalLanes := Nat.zero_lt_of_lt lt
    have ord := Nat.le_mul_of_pos_left (b u.1.1).val pos
    have full : (X).originalLanes*(b u.1.1).val+all<2^w := val ▸ (V z).isLt
    have fits : (b u.1.1).val<2^w :=
      ord.trans_lt ((Nat.le_add_right _ all).trans_lt full)
    rw [Incidents.div_value,radix,val,Nat.mul_add_div pos,Nat.div_eq_of_lt lt,Nat.add_zero,
      code,Fin.val_cast_of_lt fits]
  have bv : V (.op .mod z0 (.lit (2^S.colors)))=tagWord E.colors u.2.1 := by
    apply Fin.ext
    rw [Incidents.mod_value,rem0,show (V (.lit (2^S.colors))).val=2^S.colors from Fin.val_cast_of_lt bits]
    exact StoredColumns.digit_lane P a 0
  have sv : V (.op .mod lo (.lit S.degree))=((P.slotLabel u.2.2).val:Word w) := by
    apply Fin.ext
    rw [Incidents.mod_value,lval,show (V (.lit S.degree)).val=S.degree from Fin.val_cast_of_lt deg,
      Fin.val_cast_of_lt ((P.slotLabel _).isLt.trans deg)]
    exact StoredColumns.digit_lane P a 1
  have tv : V (.op .mod hi (Template.f tags))=tagWord E.tags u.1.2.1 := by
    apply Fin.ext; rw [Incidents.mod_value,hval,tagsR]; exact StoredColumns.digit_lane P a 2
  have lv : V (.op .div hi (Template.f tags))=tagWord E.lanes u.1.2.2 := by
    apply Fin.ext; rw [Incidents.div_value,hval,tagsR]; exact StoredColumns.digit_lane P a 3
  change Placement.Position.mk (.mk (V (.op .div z _)) (V (.op .mod hi _)) (V (.op .div hi _)))
    (V (.op .mod z0 _)) (V (.op .mod lo _))=_
  rw [bx,tv,lv,bv,sv]; rfl

include code in
theorem packNew_code (v : Placement.Site F) (s : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))
    (a : v.map V=siteCode E s) (tagsR : V (Template.f tags)=(2^t:ℕ)) (lanesR : V (Template.f remaining)=(2^l:ℕ)) :
    V (packNew Template.ptr v)=(Incidents.siteNumber b s:Word w) := by
  have ba:=congrArg Placement.Site.base a
  have ta:=congrArg Placement.Site.tag a
  have la:=congrArg Placement.Site.lane a
  simp only [Placement.Site.map,siteCode] at ba ta la
  change (V v.base*V (Template.f tags)+V v.tag)*V (Template.f remaining)+V v.lane=_
  rw [ba,ta,la,code,tagsR,lanesR,←Demand.tag_cast,←Demand.tag_cast]
  simp only [Incidents.siteNumber,Nat.cast_add,Nat.cast_mul]
  ring

include code bits deg in
omit [AddCommGroup H] in
theorem parent_code (lay : Bool) (R : GraphReads P E ((oldColumns (Demand.formulaOps 1) Template.ptr).map
      (Formula.value (fun _ => cur) mem vs)).toColumns mem) (z : F) (u : Actual P)
    (v : (V z).val=oldNumber P b u) (radix : (V (Template.f oldLanes)).val=(X).originalLanes)
    (tagsR : (V (Template.f tags)).val=2^t) (laneR : (V (Template.f remaining)).val=2^l) :
    V (parent Template.ptr S lay z)=(Incidents.siteNumber b (P.placement lay u):Word w) := by
  have old:=unpack_code P b E cur mem vs code bits deg z u v radix tagsR
  apply packNew_code b E cur mem vs code _ _ _ (by rw [←tagsR,Fin.cast_val_eq_self]) (by rw [←laneR,Fin.cast_val_eq_self])
  rw [(Template.valueOps cur mem vs).placed,old]
  exact owner_code R lay u

include code in
omit [AddCommGroup H] in
theorem packOld_code (v : Placement.Position F) (u : Actual P) (val : v.map V=posCode P E u)
    (radix : V (Template.f oldLanes)=((X).originalLanes:Word w))
    (tagsR : V (Template.f tags)=((2^t:ℕ):Word w)) :
    V (packOld Template.ptr S v)=(oldNumber P b u:Word w) := by
  have ba:=congrArg (fun z=>z.site.base) val
  have ta:=congrArg (fun z=>z.site.tag) val
  have la:=congrArg (fun z=>z.site.lane) val
  have bi:=congrArg Placement.Position.bits val
  have sl:=congrArg Placement.Position.slot val
  simp only [Placement.Position.map,Placement.Site.map,posCode,siteCode] at ba ta la bi sl
  change V v.site.base*V (Template.f oldLanes)+(V v.bits+((2^S.colors:ℕ):Word w)*
    (V v.slot+(S.degree:Word w)*(V v.site.tag+V (Template.f tags)*V v.site.lane)))=_
  rw [ba,ta,la,bi,sl,code,radix,tagsR,←Demand.tag_cast E.colors u.2.1,
    ←Demand.tag_cast E.tags u.1.2.1,←Demand.tag_cast E.lanes u.1.2.2]
  change _=(((b u.1.1).val*(X).originalLanes+((tagOrdinal S.colors u.2.1).val+2^S.colors*
    ((P.slotLabel u.2.2).val+S.degree*((tagOrdinal t u.1.2.1).val+2^t*(tagOrdinal l u.1.2.2).val))):ℕ):Word w)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow, Nat.cast_ofNat]


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.ChildRows

end OAI
