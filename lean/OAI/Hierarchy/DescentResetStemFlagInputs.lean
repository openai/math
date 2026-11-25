import OAI.Hierarchy.DescentResetFieldAssembler
import OAI.Hierarchy.DescentOperandPairBook
import OAI.Hierarchy.DescentPackedSumWords

namespace OAI
/-! # Reading the stem occupancy and the first coarse block from packed RAM -/
namespace Hierarchy.DescentResetStemFlagInputs
open DescentSIMDLookup DescentPackedZip DescentResetFieldAssembler ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {a field G H M t w : ℕ}
def liveLaw (a field : ℕ) : DescentOperandPairBook.Laws 1 (a*7) field :=
  fun _ x=>((decode a (x 0)).live.toNat:Cell field)

theorem blank (a field : ℕ) (s : Bool) : liveLaw a field s (fun _=>0)=0 := by
  have nil : (encode a 7).symm 0=fun _=>0:=by
    apply (encode a 7).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    simp [encode]
  simp [liveLaw,decode,nil]

theorem live_source (book : ℕ) (rx : Expr) (m : Memory w) (v : Fin H→Fin G→Meta)
    (fit : rx.Fits w book) (rows : Source rx (fun h g=>raw a (v h g)) M m)
    (small : ∀h g i,digits (v h g) i<2^a) (room : book+DescentOperandPairBook.words 1 (a*7) M<2^w) :
    let law:=liveLaw a field
    let e:=DescentOperandPairBook.expr law M book false (fun _=>rx)
    let last:=DescentOperandPairBook.memory law M book m
    e.Fits w (book+DescentOperandPairBook.words 1 (a*7) M) ∧
      Source e (fun h g=>((v h g).live.toNat:Cell field)) M last := by
  intro law e last
  obtain ⟨ok,read⟩:=DescentOperandPairBook.issued law (blank a field) false book (fun _=>rx) m
    (fun h g (_:Fin 1)=>raw a (v h g)) (fun _=>fit) (fun _=>rows) room
  refine ⟨ok,?_⟩
  simpa only [law,liveLaw,decode_raw _ (small _ _)] using read

def firstDigit (field x : ℕ) (g : Fin G) : Cell field :=
  ((decide (g.val=0 ∧ x=0)).toNat:Cell field)

def bitAt (t x : ℕ) : Expr :=
  if x=0 then .branch .eq (.op .mask .row (.lit (2^t-1))) (.lit 0) (.lit 1) (.lit 0) else .lit 0

theorem bit_fit (t x out w : ℕ) : (bitAt t x).Fits w out := by
  unfold bitAt
  split <;> simp [Expr.Fits]

theorem bit_work (t x : ℕ) : (bitAt t x).work≤16 := by
  by_cases hx:x=0 <;> simp [bitAt,hx,Expr.work]

theorem first_encoded (x : ℕ) (p : Row H G M) (hm : 0<M) (hg : 0<G) (hf : 0<field) :
    (data (fun (_ : Fin H) g=>firstDigit field x g) p).val=
      if p.2.val=0 ∧ x=0 then 1 else 0 := by
  let : NeZero M:=⟨hm.ne'⟩
  rw [DescentPackedSumWords.lanes_val]
  by_cases live:p.2.val=0 ∧ x=0
  · rw [ite_eq_left live]
    obtain ⟨hr,hx⟩:=live
    rw [Finset.sum_eq_single (0:Fin M)]
    · simp [hr,hx,hg,hf,firstDigit]
    · intro j _ ne
      have jnz : j.val≠0:=by intro v;exact ne (Fin.ext v)
      by_cases ok:p.2.val*M+j.val<G <;> simp [hr,hx,firstDigit,jnz]
    · simp
  · rw [ite_eq_right live]
    apply Finset.sum_eq_zero
    intro j _
    by_cases ok:p.2.val*M+j.val<G
    · by_cases hx : x=0
      · have hr : p.2.val≠0:=fun h=>live ⟨h,hx⟩
        simp [ok,firstDigit,hx,hr,hm.ne']
      · simp [ok,firstDigit,hx]
    · simp [ok]

theorem first_source (x : ℕ) (m : Memory w) (hm : 0<M) (hg : 0<G) (hf : 0<field)
    (shape : chunks G M=2^t) (hosts : H*chunks G M≤2^w) (maskRoom : 2^t≤2^w) :
    Source (bitAt t x) (fun (_ : Fin H) (g : Fin G)=>firstDigit field x g) M m := by
  intro p
  have cPos : p.2.val<2^t:=p.2.isLt.trans_le shape.le
  have mask:2^t-1<2^w:=by have:=Nat.two_pow_pos t;omega
  have rr : (row H G M p).val=p.1.val*2^t+p.2.val:=by
    change p.2.val+chunks G M*p.1.val=_
    exact (congrArg (fun n : ℕ=>p.2.val+n*p.1.val) shape).trans (by ac_rfl)
  have rc : BinaryOp.bitAnd.eval ((row H G M p).val:Word w) ((2^t-1:ℕ):Word w)=(p.2.val:Word w) := by
    change (Nat.land (((row H G M p).val : Word w).val) (((2^t-1 : ℕ) : Word w).val) : Word w)=_
    rw [Fin.val_cast_of_lt ((row H G M p).isLt.trans_le hosts),Fin.val_cast_of_lt mask,rr,
      Nat.land_eq,Nat.and_two_pow_sub_one_eq_mod,Nat.mul_add_mod_of_lt cPos]
  rw [first_encoded x p hm hg hf]
  by_cases hx:x=0
  · have word : ((p.2.val:Word w)=0) ↔ p.2.val=0 := by
      constructor
      · intro h
        have:=congrArg Fin.val h
        simpa only [Fin.val_cast_of_lt (cPos.trans_le maskRoom),Fin.val_zero] using this
      · intro h
        simp [h]
    let pos : Word w:=(row H G M p).val
    let low := (Expr.op .mask .row (.lit (2^t-1))).eval m pos
    let flag := Comparison.eq.test low ((Expr.lit 0).eval m pos)
    have tested : flag=true ↔ p.2.val=0 := by
      change (BinaryOp.bitAnd.eval ((row H G M p).val : Word w) ((2^t-1 : ℕ) : Word w) ==
        ((0 : ℕ) : Word w)) = true ↔ p.2.val=0
      rw [rc,beq_iff_eq,Nat.cast_zero]
      exact word
    rw [bitAt,ite_eq_left hx]
    change (if flag then ((1 : ℕ) : Word w) else ((0 : ℕ) : Word w))=
      ((if p.2.val=0 ∧ x=0 then 1 else 0 : ℕ) : Word w)
    by_cases hc : p.2.val=0
    · rw [ite_eq_left (tested.mpr hc),ite_eq_left ⟨hc,hx⟩]
    · have dead : ¬(p.2.val=0 ∧ x=0):=fun h=>hc h.1
      rw [ite_eq_right (mt tested.mp hc),ite_eq_right dead]
  · simp [bitAt,hx,Expr.eval]

end
end Hierarchy.DescentResetStemFlagInputs

end OAI
