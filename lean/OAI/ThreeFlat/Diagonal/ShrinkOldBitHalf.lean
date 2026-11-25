import OAI.ThreeFlat.Diagonal.CompressorBitOrigins
import OAI.ThreeFlat.Diagonal.CompressorChildBits
import OAI.ThreeFlat.Diagonal.CompressorResidentInput
import OAI.ThreeFlat.Diagonal.CompressorOpsMap

namespace OAI
/-! # Physical source half of a bit on an arbitrary old shrinking-stage arc -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.CommRing
variable {B H : Type} [AddCommGroup H] {w c t l n N : ℕ} {S : Graph.Stage}
variable (P : PackingData B H (BitWord t) (BitWord l) S.degree (c+1))
variable (E : Codec B w (c+1) t l) (pub : Param→Word w) (mem : Memory w) (vs : Fin n→Word w)
variable (ptr : F n)
set_option quotPrecheck false
local notation "V" => Formula.value pub mem vs
local notation "o" => Demand.formulaOps n
local notation "g" => oldColumns o ptr
local notation "d" => S.degree

/-- The source-major mate column, omitted by the backward-only traversal interface. -/
def MateReads : Prop := ∀ (v : B) (i : Fin d) (x j : F n),V x=E.base v → V j=(i.val:Word w) →
  V (mate ptr S x j)=((P.slots.target (v,i)).2.val:Word w)

omit [AddCommGroup H] in
theorem mate_from_stored (b : B≃Fin N) (C : SlotImage.Columns)
    (width : SlotImage.Edge B (BitWord (c+1) × H × BitWord t × BitWord l) d→ℕ)
    (stored : SlotImage.Stored (StageAddress.packedGraph P) b (Demand.laneOrdinal P) C (fun a=>(mem a).val) width)
    (number : ∀v,E.base v=((b v).val:Word w))
    (origin : V (atField o ptr oldGraph)=(C.graph:Word w)) (rows : V (atField o ptr oldSlots)=(C.rows:Word w))
    (room : C.graph+6*C.rows≤2^w) : MateReads (S:=S) P E pub mem vs ptr := by
  intro v i x j vertex port
  let pp:=(v,i)
  let a:=SlotImage.cell C b pp false 1
  have bound : a<2^w := (SlotImage.cell_range stored pp false 1).2.trans_le room
  have read:=stored.mate pp false
  have val : mem a=((P.slots.target pp).2.val:Word w) := by
    rw [←Fin.cast_val_eq_self (mem a)]
    exact congrArg (fun k : ℕ=>(k:Word w)) read
  change mem ((V (atField o ptr oldGraph)+V (atField o ptr oldSlots)*1)+(V x*(d:Word w)+V j)).val=_
  rw [origin,rows,vertex,number,port,mul_one,←Nat.cast_mul,←Nat.cast_add,←Nat.cast_add,←Nat.cast_add]
  have addr : C.graph+C.rows+((b v).val*d+i.val)=a := by simp [a,pp,SlotImage.cell,SlotImage.column,SlotImage.ordinal]
  rw [addr,Fin.val_cast_of_lt bound];exact val

private theorem valOps : OpMap (Demand.formulaOps n) (words mem) (Formula.value pub mem vs) where
  lit _ := rfl
  bin _ _ _ := rfl
  load _ := rfl
  choose _ _ _ _ := by simp [Demand.formulaOps,words,Formula.value,DescriptorExpr.Comparison.test]

private theorem removed (x color : F n) (u : BitWord (c+1)) (i : Fin (c+1))
    (value : (V x).val=(tagOrdinal _ u).val) (atColor : (V color).val=i.val) (cw : c+1<w) :
    let step:=Formula.op .shiftLeft (.lit 1) color
    let hi:=Formula.op .div x (.op .mul (.lit 2) step)
    V (.op .add (.op .mod x step) (.op .mul step hi)) =
      (Owner.removeDigit (tagOrdinal _ u).val i.val:Word w) := by
  let step:=Formula.op .shiftLeft (.lit 1) color
  let k:=2^i.val
  have iw : i.val<w:=i.isLt.trans cw
  have small : k<2^w := Nat.pow_lt_pow_right (by decide) iw
  have big : 2*k<2^w := by
    rw [show 2*k=2^(i.val+1) by dsimp [k];rw [pow_succ,Nat.mul_comm]]
    exact Nat.pow_lt_pow_right (by decide) (by have:=i.isLt;omega)
  have one : 1<2^w:=Nat.one_lt_two_pow (by omega)
  have stepVal : (V step).val=k := by
    change (BinaryOp.shiftLeft.eval (1:Word w) (V color)).val=_
    simp only [BinaryOp.eval, atColor, ite_eq_left iw, Fin.val_ofNat, Nat.shiftLeft_eq]
    have oneVal : (1 : Word w).val = 1 := Fin.val_cast_of_lt one
    rw [oneVal, one_mul]
    exact Nat.mod_eq_of_lt small
  have stepWord : V step=(k:Word w) := by rw [←stepVal,Fin.cast_val_eq_self]
  have twice : (V (.op .mul (.lit 2) step)).val=2*k := by
    change ((2:Word w)*V step).val=_
    rw [stepWord]
    change (((2:ℕ):Word w)*(k:Word w)).val=_
    rw [←Nat.cast_mul,Fin.val_cast_of_lt big]
  let bits:=(tagOrdinal _ u).val
  have lo : V (.op .mod x step)=((bits%k:ℕ):Word w) := by
    change (((V x).val%(V step).val:ℕ):Word w)=_
    rw [value,stepVal]
  have hi : V (.op .div x (.op .mul (.lit 2) step))=((bits/(2*k):ℕ):Word w) := by
    change (((V x).val/(V (.op .mul (.lit 2) step)).val:ℕ):Word w)=_
    rw [value,twice]
  change V (.op .mod x step)+V step*V (.op .div x (.op .mul (.lit 2) step))=_
  rw [lo,hi,stepWord,←Nat.cast_mul,←Nat.cast_add]
  congr 1
  simp only [Owner.removeDigit,pow_succ,k,bits,Nat.mul_comm (2^i.val) 2]

variable {P E pub mem vs ptr}
theorem childNumber_native (R : ArcReads P E ((oldColumns (Demand.formulaOps n) ptr).map (Formula.value pub mem vs)) mem) (M : MateReads (S:=S) P E pub mem vs ptr)
    (colors : S.colors=c+1) (cw : c+1<w) (lay : Bool) (x : Placement.Position (F n))
    (u : Computability.VPVNP.Compression.Position B H (BitWord t) (BitWord l) (c+1))
    (code : x.map V=posCode P E u) :
    V (childNumber ptr S lay x)=
      (((Owner.childOrder P lay (P.placement lay u)).symm ⟨u,rfl⟩).val:Word w) := by
  let color:=row o (g).toColumns.color x.site.base
  let step:=Formula.op .shiftLeft (.lit 1) color
  let hi:=Formula.op .div x.bits (.op .mul (.lit 2) step)
  let free:=Formula.op .add (.op .mod x.bits step) (.op .mul step hi)
  let i:=if lay then mate ptr S x.site.base x.slot else x.slot
  let slotIndex:=(o).choose (thickBit o (g).toColumns x) (.lit 1) x.slot (.op .add (.lit d) i)
  have ba : V x.site.base=E.base u.1.1 := congrArg (fun z=>z.site.base) code
  have sl : V x.slot=((P.slotLabel u.2.2).val:Word w) := congrArg Placement.Position.slot code
  have bits : (V x.bits).val=(tagOrdinal _ u.2.1).val := congrArg (fun z=>z.bits.val) code
  have colorWord : V color=((P.color u.1.1).val:Word w) := by
    change row (words mem) (V (g).toColumns.color) (V x.site.base)=_
    rw [ba];exact R.color _
  have colorFit : (P.color u.1.1).val<2^w :=
    (P.color u.1.1).isLt.trans (cw.trans Nat.lt_two_pow_self)
  have deletion : V free=(Owner.removeDigit (tagOrdinal _ u.2.1).val (P.color u.1.1).val:Word w) :=
    removed pub mem vs x.bits color u.2.1 (P.color _) bits (by rw [colorWord,Fin.val_cast_of_lt colorFit]) cw
  have thick : V (thickBit o (g).toColumns x)=1 ↔ P.thick u := by
    rw [(valOps pub mem vs).bit,code];exact thick_bit R.toGraphReads u
  have mateId : V i=((Owner.port P lay (P.assignedBundle u)).2.val:Word w) := by
    cases lay with
    | false => exact sl
    | true => exact M _ _ _ _ ba sl
  have block : V slotIndex=((if P.thick u then (P.slotLabel u.2.2).val
      else d+(Owner.port P lay (P.assignedBundle u)).2.val:ℕ):Word w) := by
    change (if DescriptorExpr.Comparison.eq.test (V (thickBit o (g).toColumns x)) 1 then V x.slot else (d:Word w)+V i)=_
    by_cases h : P.thick u
    · simp [DescriptorExpr.Comparison.test,thick.mpr h,h,sl]
    · simp [DescriptorExpr.Comparison.test,mt thick.mp h,h,mateId]
  rw [Owner.childNumber_physical]
  change V slotIndex*((2^(S.colors-1):ℕ):Word w)+V free=_
  rw [block,deletion,colors,Nat.add_sub_cancel]
  simp only [Nat.cast_add,Nat.cast_mul]

section
variable {d0 c0 : ℕ} (Q : PackingData B H (BitWord t) (BitWord l) d0 c0)

def oldEndpoint (a : Arc B H (BitWord t) (BitWord l) d0 c0) (back : Bool) :=
  sourcePosition (if back then Q.actual a else a)

def endpointHalf (a : Arc B H (BitWord t) (BitWord l) d0 c0) (back : Bool) :=
  if back then d0+(Q.actual a).1.2.val else a.1.2.val

end

theorem oldHalf_native (R : ArcReads P E ((oldColumns (Demand.formulaOps n) ptr).map (Formula.value pub mem vs)) mem) (M : MateReads (S:=S) P E pub mem vs ptr)
    (colors : S.colors=c+1) (cw : c+1<w) (lay back : Bool)
    (e : Ends (F n)) (inc bit : F n) (a : Arc B H (BitWord t) (BitWord l) d (c+1))
    (ends : e.map V=encodeEnds P E a) (side : V inc=(back.toNat:Word w)) (k : Fin 4) :
    let u:=oldEndpoint P a back
    V (oldHalf ptr S lay e inc bit k)=
      ((![1,((Owner.childOrder P lay (P.placement lay u)).symm ⟨u,rfl⟩).val,
        endpointHalf P a back,(V bit).val] : Fin 4→ℕ) k:Word w) := by
  let u:=oldEndpoint P a back
  let x:=Placement.Position.select o inc e.target e.source
  have src : e.source.map V=posCode P E (sourcePosition a) := congrArg Ends.source ends
  have dst : e.target.map V=posCode P E (sourcePosition (P.actual a)) := congrArg Ends.target ends
  have orig : V e.originalSlot=(a.1.2.val:Word w) := congrArg Ends.originalSlot ends
  have nonzero : (0:Word w)≠1 := by
    intro eqv
    have v:=congrArg Fin.val eqv
    have small : 1<2^w:=Nat.one_lt_two_pow (by omega)
    have vv : (1:Word w).val=1 := Fin.val_cast_of_lt small
    rw [vv] at v;contradiction
  have chosen : x.map V=posCode P E u := by
    rw [show x.map V=Placement.Position.select (words mem) (V inc) (e.target.map V) (e.source.map V)
      from (valOps pub mem vs).positionIf inc e.target e.source,src,dst,side]
    cases back <;> simp [words,Placement.Position.select,Placement.Site.select,u,oldEndpoint,nonzero]
  have child:=childNumber_native R M colors cw lay x u chosen
  have addr : V (mate ptr S e.source.site.base e.originalSlot)=
      ((P.slots.target (a.1.1.1,a.1.2)).2.val:Word w) :=
    M _ _ _ _ (congrArg (fun z=>z.site.base) src) orig
  let half:=(o).choose inc (.lit 1) (.op .add (.lit d) (mate ptr S e.source.site.base e.originalSlot)) e.originalSlot
  have halfWord : V half=(endpointHalf P a back:Word w) := by
    change (if DescriptorExpr.Comparison.eq.test (V inc) 1 then (d:Word w)+V (mate ptr S e.source.site.base e.originalSlot) else V e.originalSlot)=_
    rw [side,addr,orig]
    cases back <;> simp [DescriptorExpr.Comparison.test,endpointHalf,nonzero,Nat.cast_add]; rfl
  fin_cases k
  · rfl
  · exact child
  · exact halfWord
  · exact (Fin.cast_val_eq_self _).symm


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

end OAI
