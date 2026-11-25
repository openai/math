import OAI.ThreeFlat.Diagonal.ShrinkBitLookup
import OAI.ThreeFlat.Diagonal.ShrinkDemandPointer

namespace OAI
/-! # Native AB/CD selection at an occupied party's raw demand edge -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.NatCast
variable {n w : ℕ} {data : Param → Word w} {mem : Memory w} {regs : Fin n → Word w}
local notation "V" => Formula.value data mem regs

def abAddress (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n)) (party j : F n) : Address n :=
  let o := Demand.formulaOps n
  let g := oldColumns o ptr
  let p := layout ptr S
  let thick := thickBit o g.toColumns e.source
  let c := Position.select o thick e.target e.source
  let a := toggle o g.toColumns c.site
  let key := Demand.physical p e.source e.originalSlot
  let total := Demand.thickWidth g p a c.slot
  let start := startPiece total (3*(2^S.colors*S.degree)/4) (Demand.bundleNumber g p a c.slot key)
  locate (thickBlocks ptr S lay a c.slot party) (.op .add start j)

def cdSide (ptr : F n) (e : Ends (F n)) (party : F n) : F n :=
  let o := Demand.formulaOps n
  let thick := thickBit o (oldColumns o ptr).toColumns e.source
  o.choose party (.lit 2) thick (.op .bitXor thick (.lit 1))

theorem demand_path (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (party edge j : F n) (i : Fin 2) (side : Bool) (k : Fin 4) (fit : 4≤2^w)
    (partyVal : (V party).val=2*i.val+side.toNat) (edgeVal : (V edge).val=i.val) :
    V (demandAddress ptr S lay e party edge j k) =
      if i=0 then V (abAddress ptr S lay e party j k)
      else V (oldHalf ptr S lay e (cdSide ptr e party) j k) := by
  have lit (a : ℕ) (small : a<4) : (V (.lit a)).val=a := Fin.val_cast_of_lt (by omega)
  have eqAt (a : ℕ) (small : a<4) (x yes no : F n) :
      V (.select .eq x (.lit a) yes no) = if (V x).val=a then V yes else V no := by
    have eqv : V x = V (.lit a) ↔ (V x).val=a := by rw [Fin.ext_iff, lit a small]
    change (if (V x == V (.lit a)) = true then V yes else V no) = _
    simp only [beq_iff_eq, eqv]
  have ltAt (a : ℕ) (small : a<4) (x yes no : F n) :
      V (.select .lt x (.lit a) yes no) = if (V x).val<a then V yes else V no := by
    change (if decide (V x < V (.lit a)) = true then V yes else V no) = _
    simp only [decide_eq_true_eq, Fin.lt_def, lit a small]
  change V (.select .eq edge (.lit 0) (.select .lt party (.lit 2) (abAddress ptr S lay e party j k) (.lit 0))
    (.select .eq edge (.lit 1) (.select .eq party (.lit 2) (oldHalf ptr S lay e (cdSide ptr e party) j k)
      (.select .eq party (.lit 3) (oldHalf ptr S lay e (cdSide ptr e party) j k) (.lit 0))) (.lit 0))) = _
  simp only [eqAt 0 (by decide), eqAt 1 (by decide), eqAt 2 (by decide), eqAt 3 (by decide),
    ltAt 2 (by decide), edgeVal, partyVal]
  fin_cases i <;> cases side <;> rfl

variable {B H : Type*} [AddCommGroup H] {S : Graph.Stage} {t l : ℕ}
variable {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors} {E : Codec B w S.colors t l}

theorem thick_word (g : ArcColumns (F n)) (R : ArcReads P E (g.map V) mem) (x : Position (F n))
    (z : Computability.VPVNP.Compression.Position B H (BitWord t) (BitWord l) S.colors)
    (enc : x.map V=posCode P E z) :
    V (thickBit (Demand.formulaOps n) g.toColumns x)=(if P.thick z then 1 else 0) := by
  rw [Demand.eval_thick,enc]
  change BinaryOp.bitAnd.eval (BinaryOp.shiftRight.eval (tagWord E.colors z.2.1)
    (row (words mem) (g.map V).color (E.base z.1.1))) 1 = _
  rw [R.color,read_bit]
  unfold PackingData.thick
  have bitValue (bit : ZMod 2) :
      (bit.val : Word w)=(if bit=1 then 1 else 0) := by
    fin_cases bit
    · change ((0:ℕ):Word w)=(if (0:ZMod 2)=1 then 1 else 0)
      rw [ite_eq_right (by decide),Nat.cast_zero]
    · change ((1:ℕ):Word w)=(if (1:ZMod 2)=1 then 1 else 0)
      rw [ite_eq_left rfl,Nat.cast_one]
  exact bitValue (z.2.1 (P.color z.1.1))

theorem cdSide_word (ptr : F n) (e : Ends (F n)) (a : Arc B H (BitWord t) (BitWord l) S.degree S.colors)
    (enc : e.map V=encodeEnds P E a) (R : ArcReads P E ((oldColumns (Demand.formulaOps n) ptr).map V) mem)
    (party : F n) (side : Bool) (partyVal : (V party).val=2+side.toNat) (fit : 4≤2^w) :
    V (cdSide ptr e party) =
      ((if P.thick (sourcePosition a) then (!side).toNat else side.toNat : ℕ):Word w) := by
  let flag := thickBit (Demand.formulaOps n) (oldColumns (Demand.formulaOps n) ptr).toColumns e.source
  have val : V flag=(if P.thick (sourcePosition a) then 1 else 0) :=
    thick_word _ R _ _ (congrArg Ends.source enc)
  simp only [cdSide,Demand.eval_choose]
  change (if V party=(2:Word w) then V flag else BinaryOp.bitXor.eval (V flag) 1)=_
  have one : (1 : ℕ) < 2^w := by omega
  have two : (2 : ℕ) < 2^w := by omega
  cases side <;> by_cases mark : P.thick (sourcePosition a) <;>
    simp [Fin.ext_iff,partyVal,val,mark,BinaryOp.eval,Nat.mod_eq_of_lt one,Nat.mod_eq_of_lt two]


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

end OAI
