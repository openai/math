import OAI.ThreeFlat.Diagonal.ShrinkNativeInsert

namespace OAI
/-! # The numbered native child list of an actual shrinking site -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.ChildRows
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalPinsExpr Placement Resident
open scoped Classical Fin.NatCast Fin.CommRing
variable {w N t l c : ℕ} {B H : Type} [AddCommGroup H]

/-- A binary stage with one distinguished color and `c` free digits. -/
abbrev withFree (S : Graph.Stage) (c : ℕ) : Graph.Stage := {S with colors:=c+1}

variable (S₀ : Graph.Stage)
set_option quotPrecheck false
local notation "childStage" => withFree S₀ c
local notation "d" => S₀.degree
variable (P : PackingData B H (BitWord t) (BitWord l) S₀.degree (c+1))
variable (b : B ≃ Fin N) (E : Codec B w (c+1) t l)
variable (cur : Word w) (m : Memory w) (vs : Fin 1→Word w)
local notation "V" => Formula.value (fun _=>cur) m vs
local notation "T" => Template.g.toColumns
local notation "X" => dims childStage N t l
variable (R : GraphReads P E (((oldColumns (Demand.formulaOps 1) Template.ptr).map (Formula.value (fun _ => cur) m vs)).toColumns) m) (code : ∀u,E.base u=((b u).val:Word w))
variable (radix : Formula.value (fun _ => cur) m vs (Template.f oldLanes)=
  ((dims (withFree S₀ c) N t l).originalLanes : Word w))
variable (tagsR : Formula.value (fun _ => cur) m vs (Template.f tags)=((2^t:ℕ):Word w))

include R code radix tagsR in
omit [AddCommGroup H] in
theorem child_value (lay thin : Bool) (v : Placement.Site F) (i u : F)
    (s : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l)) (h : Fin d) (bits : BitWord (c+1))
    (site : v.map V=siteCode E s) (port : V i=(h.val:Word w))
    (free : (V u).val=Owner.removeDigit (tagOrdinal _ bits).val (Owner.chosenColor P lay s thin h).val)
    (ok : Owner.valid P lay s (thin,h,bits)) :
    V (childValue Template.ptr childStage lay thin v i u)=
      (oldNumber P b (Owner.child P lay s (thin,h,bits)):Word w) := by
  let base:=Owner.child P lay s (thin,h,0)
  let raw:=child Template.o T d lay thin v i (.lit 0)
  let atColor:=row Template.o (T).color raw.site.base
  have baseCode : raw.map V=posCode P E base := by
    rw [show raw.map V=child (words m) ((T).map V) d lay thin (v.map V) (V i) (V (.lit 0)) from
      (Template.valueOps cur m vs).fromParent T d lay thin v i (.lit 0),site,port]
    have zeroWord : V (.lit 0)=0 := by
      change ((0 : ℕ) : Word w) = 0
      exact Nat.cast_zero
    rw [zeroWord]
    have cols : (T).map V=((oldColumns (Demand.formulaOps 1) Template.ptr).map V).toColumns := rfl
    rw [cols]
    dsimp only [base]
    have oldRead := child_code R lay thin s h (0 : BitWord (c+1))
    rw [tagWord_zero] at oldRead
    exact oldRead
  have colorCode : V atColor=((Owner.chosenColor P lay s thin h).val:Word w) := by
    have bv:=congrArg (fun j=>j.site.base) baseCode
    change V raw.site.base=E.base base.1.1 at bv
    change row (words m) (V (T).color) (V raw.site.base)=_
    rw [bv];exact R.color _
  have cw : (Owner.chosenColor P lay s thin h).val<2^w :=
    (Owner.chosenColor P lay s thin h).isLt.trans_le (E.colors.trans Nat.lt_two_pow_self.le)
  have inserted:=insert_value cur m vs u atColor E.colors bits (Owner.chosenColor P lay s thin h) thin free
    (by rw [colorCode]; exact Fin.val_cast_of_lt cw) ((Owner.valid_bit P lay s thin h bits).mp ok)
  apply packOld_code (S:=childStage) P b E cur m vs code _ _ _ radix tagsR
  change {raw.map V with bits:=V (insert u atColor thin)}=_
  rw [baseCode,inserted]
  cases thin <;> rfl

private theorem high {r i : ℕ} (a : ℕ) (h : i<r) : (a*r+i)/r=a := by
  rw [Nat.mul_comm a,Nat.mul_add_div (by omega : 0<r),Nat.div_eq_of_lt h,Nat.add_zero]

private theorem low {r i : ℕ} (a : ℕ) (h : i<r) : (a*r+i)%r=i := by
  rw [Nat.mul_comm a,Nat.mul_add_mod,Nat.mod_eq_of_lt h]

include R code radix tagsR in
omit [AddCommGroup H] in
theorem entry_value (lay : Bool) (linear : F) (s : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))
    (thin : Bool) (h : Fin d) (bits : BitWord (c+1)) (ok : Owner.valid P lay s (thin,h,bits))
    (baseId : ℕ) (first : V (Template.f firstNode)=(baseId:Word w))
    (tagCount : (V (Template.f tags)).val=2^t) (lanes : (V (Template.f remaining)).val=2^l)
    (degreeRoom : d<2^w) (capFits : d*2^(c+1)<2^w) (bitsFit : 2^c<2^w)
    (addr : (V linear).val=Incidents.siteNumber b s*(d*2^(c+1))+
      (Owner.indexOrder P lay s ⟨(thin,h,bits),ok⟩).val) :
    V (entry Template.ptr childStage lay linear)=
      ((baseId+oldNumber P b (Owner.child P lay s (thin,h,bits)):ℕ):Word w) := by
  let cap:=d*2^(c+1)
  let freeRadix:=2^((childStage).colors-1)
  let site:=Incidents.siteAt Template.ptr (.op .div linear (.lit cap))
  let i:=Formula.op .mod linear (.lit cap)
  let n:=Formula.op .div i (.lit freeRadix)
  let slot:=Formula.op .mod n (.lit d)
  let u:=Formula.op .mod i (.lit freeRadix)
  let number:=Owner.indexOrder P lay s ⟨(thin,h,bits),ok⟩
  let del:=Owner.removeDigit (tagOrdinal _ bits).val (Owner.chosenColor P lay s thin h).val
  let block:=(if thin then d else 0)+h.val
  have digit : del<2^c := by
    exact (Owner.freeOrdinal_value P lay s thin h ⟨bits,ok⟩).symm.trans_lt
      (Owner.freeOrdinal P lay s thin h ⟨bits,ok⟩).isLt
  have digits : number.val=block*2^c+del := Owner.indexOrder_value P lay s ⟨(thin,h,bits),ok⟩
  have freeRad : freeRadix=2^c := by simp [freeRadix]
  have room : (V (.lit cap)).val=cap:=Fin.val_cast_of_lt capFits
  have roomF : (V (.lit freeRadix)).val=2^c := by rw [freeRad];exact Fin.val_cast_of_lt bitsFit
  have roomD : (V (.lit d)).val=d:=Fin.val_cast_of_lt degreeRoom
  have atSite : site.map V=siteCode E s := by
    apply Incidents.siteAt_code (S := childStage) (fun _ => cur) m vs E b Template.ptr _ s code tagCount lanes
    rw [Incidents.div_value,room,addr,high _ number.isLt]
  have iv : (V i).val=number.val := by
    change (V (.op .mod linear (.lit cap))).val=_
    rw [Incidents.mod_value,room,addr,low _ number.isLt]
  have nv : (V n).val=block := by
    change (V (.op .div i (.lit freeRadix))).val=_
    rw [Incidents.div_value,iv,roomF,digits,high _ digit]
  have uv : (V u).val=del := by
    change (V (.op .mod i (.lit freeRadix))).val=_
    rw [Incidents.mod_value,iv,roomF,digits,low _ digit]
  have slotv : V slot=(h.val:Word w) := by
    apply Fin.ext
    change (V (.op .mod n (.lit d))).val=_
    rw [Incidents.mod_value,nv,roomD,Fin.val_cast_of_lt (h.isLt.trans degreeRoom)]
    cases thin <;> simp [block,Nat.mod_eq_of_lt h.isLt]
  have vk:=child_value S₀ P b E cur m vs R code radix tagsR
    lay thin site slot u s h bits atSite slotv uv ok
  change V (Template.f firstNode)+(if decide ((V n).val<(V (.lit d)).val) then
    V (childValue Template.ptr childStage lay false site slot u) else V (childValue Template.ptr childStage lay true site slot u))=_
  rw [first,Nat.cast_add,nv,roomD]
  cases thin <;> simp [block,h.isLt,vk]


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.ChildRows

end OAI
