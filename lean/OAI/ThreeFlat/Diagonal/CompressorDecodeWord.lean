import OAI.ThreeFlat.Diagonal.CompressorShrinkWidthDecode
import OAI.ThreeFlat.Diagonal.CompressorDemandROM

namespace OAI
/-! # Exact word evaluation of the inverse rooted-edge identifier -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.CommRing
variable {w n d c t l : ℕ} {B H : Type*} [AddCommGroup H]
variable {data : Param → Word w} {m : Memory w} {vs : Fin n → Word w}
local notation "V" => Formula.value data m vs

private theorem prefix_fit {q N : ℕ} (b : Fin N) (hb : appendKey q b<2^w) : q<2^w :=
  ((Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt b.isLt)).trans (Nat.le_add_right ..)).trans_lt hb

private theorem divDigit {q N : ℕ} (b : Fin N) (hb : appendKey q b<2^w) (hn : N<2^w) :
    BinaryOp.div.eval ((appendKey q b):Word w) (N:Word w) = (q:Word w) := by
  rw [op_cast (w:=w) .div _ _ ⟨hb,hn⟩]
  simp only [natOp,appendKey,Nat.mul_comm q N,Nat.mul_add_div (Nat.zero_lt_of_lt b.isLt),
    Nat.div_eq_of_lt b.isLt,Nat.add_zero]

private theorem modDigit {q N : ℕ} (b : Fin N) (hb : appendKey q b<2^w) (hn : N<2^w) :
    BinaryOp.mod.eval ((appendKey q b):Word w) (N:Word w) = (b.val:Word w) := by
  rw [op_cast (w:=w) .mod _ _ ⟨hb,hn⟩]
  simp [natOp,appendKey,Nat.mod_eq_of_lt b.isLt]

variable (P : PackingData B H (BitWord t) (BitWord l) d c) (E : Codec B w c t l)
variable (base : B ↪ ℕ) (hb : ∀v, E.base v=(base v:Word w))
variable (pieces : Fin 4 → ℕ) (radix live full : ℕ) (bound : ∀i,pieces i≤radix)
local notation "S" => (Graph.Stage.mk d c pieces radix live full)

include hb in
theorem decode_word (tags id : F n) (e : ShrinkEdge P pieces)
    (ht : V tags=((2^t:ℕ):Word w))
    (hkey : V id=((1+edgeKey P base (tagOrdinal t).toEmbedding pieces radix bound e:ℕ):Word w))
    (fit : 1+edgeKey P base (tagOrdinal t).toEmbedding pieces radix bound e<2^w)
    (dims : radix<2^w ∧ 4<2^w ∧ d<2^w ∧ 2^c<2^w ∧ 2^t<2^w) :
    let a := decode S tags id
    let r := e.2.1.val.val
    a.old.map V=posCode P E (sourcePosition r) ∧ V a.oldPort=(r.1.2.val:Word w) ∧
      V a.survivor=(e.1.val:Word w) ∧ V a.copy=(e.2.2.val:Word w) := by
  let r := e.2.1.val.val
  let i0 := tagOrdinal t r.1.1.2.1
  let i1 := r.1.2
  let i2 := tagOrdinal c r.2.1
  let i3 := P.slotLabel r.2.2
  let i4 := e.1
  let i5 := e.2.2.castLE (bound e.1)
  let a0 := appendKey (base r.1.1.1) i0
  let a1 := appendKey a0 i1
  let a2 := appendKey a1 i2
  let a3 := appendKey a2 i3
  let a4 := appendKey a3 i4
  let a5 := appendKey a4 i5
  change 1+a5<2^w at fit
  have f5 : a5<2^w := by omega
  have f4 : a4<2^w := prefix_fit i5 f5
  have f3 : a3<2^w := prefix_fit i4 f4
  have f2 : a2<2^w := prefix_fit i3 f3
  have f1 : a1<2^w := prefix_fit i2 f2
  have f0 : a0<2^w := prefix_fit i1 f1
  have code : V (.cut id (.lit 1))=(a5:Word w) := by
    change (if RAM.DescriptorExpr.Comparison.lt.test (V id) 1 then 0 else (V id)-1) = _
    have keyValue : V id = ((1+a5 : ℕ) : Word w) := hkey
    rw [keyValue]
    have one : (1:ℕ)<2^w := by omega
    have oneVal : (1:Word w).val=1 := by
      change 1 % (2^w) = 1
      exact Nat.mod_eq_of_lt one
    have positive : ¬(((1+a5:ℕ):Word w)<1) := by
      change ¬(((1+a5:ℕ):Word w).val < (1:Word w).val)
      rw [Fin.val_cast_of_lt fit,oneVal]
      omega
    simp only [RAM.DescriptorExpr.Comparison.test,decide_eq_true_eq,ite_eq_right positive]
    push_cast; abel
  have op (op : BinaryOp) (a b : F n) : V (.op op a b) = op.eval (V a) (V b) := rfl
  have lit (z : ℕ) : V (.lit z) = ((z : ℕ) : Word w) := rfl
  have lane : (e.2.1.val.val).1.1.2.2 = 0 := e.2.1.property
  have div5 : BinaryOp.div.eval (a5:Word w) ((radix:ℕ):Word w) = (a4:Word w) :=
    divDigit (q:=a4) i5 f5 dims.1
  have mod5 : BinaryOp.mod.eval (a5:Word w) ((radix:ℕ):Word w) = (i5.val:Word w) :=
    modDigit (q:=a4) i5 f5 dims.1
  have div4 : BinaryOp.div.eval (a4:Word w) ((4:ℕ):Word w) = (a3:Word w) :=
    divDigit (q:=a3) i4 f4 dims.2.1
  have mod4 : BinaryOp.mod.eval (a4:Word w) ((4:ℕ):Word w) = (i4.val:Word w) :=
    modDigit (q:=a3) i4 f4 dims.2.1
  have div3 : BinaryOp.div.eval (a3:Word w) ((d:ℕ):Word w) = (a2:Word w) :=
    divDigit (q:=a2) i3 f3 dims.2.2.1
  have mod3 : BinaryOp.mod.eval (a3:Word w) ((d:ℕ):Word w) = (i3.val:Word w) :=
    modDigit (q:=a2) i3 f3 dims.2.2.1
  have div2 : BinaryOp.div.eval (a2:Word w) ((2^c:ℕ):Word w) = (a1:Word w) :=
    divDigit (q:=a1) i2 f2 dims.2.2.2.1
  have mod2 : BinaryOp.mod.eval (a2:Word w) ((2^c:ℕ):Word w) = (i2.val:Word w) :=
    modDigit (q:=a1) i2 f2 dims.2.2.2.1
  have div1 : BinaryOp.div.eval (a1:Word w) ((d:ℕ):Word w) = (a0:Word w) :=
    divDigit (q:=a0) i1 f1 dims.2.2.1
  have mod1 : BinaryOp.mod.eval (a1:Word w) ((d:ℕ):Word w) = (i1.val:Word w) :=
    modDigit (q:=a0) i1 f1 dims.2.2.1
  have div0 : BinaryOp.div.eval (a0:Word w) ((2^t:ℕ):Word w) = (base r.1.1.1:Word w) :=
    divDigit (q:=base r.1.1.1) i0 f0 dims.2.2.2.2
  have mod0 : BinaryOp.mod.eval (a0:Word w) ((2^t:ℕ):Word w) = (i0.val:Word w) :=
    modDigit (q:=base r.1.1.1) i0 f0 dims.2.2.2.2
  dsimp only
  simp only [decode,Position.map,Site.map,op,lit,code,ht,div5,mod5,div4,mod4,div3,mod3,
    div2,mod2,div1,mod1,div0,mod0]
  simp only [posCode,siteCode,sourcePosition,hb,i0,i1,i2,i3,i4,i5,
    Demand.tag_cast E.tags,Demand.tag_cast E.colors,Fin.val_castLE,lane,tagWord_zero,Nat.cast_zero,
    and_true]; repeat' first | constructor

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkWidth

end OAI
