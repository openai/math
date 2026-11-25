import OAI.Hierarchy.DescentPackedVenueOrdinals
import OAI.Hierarchy.DescentRosterOrder
import Mathlib.Order.Interval.Finset.Fin

namespace OAI
/-! # Dense row-major ordinals of the complete physical host roster -/

namespace Hierarchy.DescentHostDirectory
open scoped Classical
noncomputable section

private theorem node_onto (k t : ℕ) (small : t<2^(k+1)-1) :
    ∃d≤k,∃j<2^d,nodeNumber d j=t := by
  induction k with
  | zero =>
    have ht : t=0 := by norm_num at small;omega
    subst t
    exact ⟨0,le_rfl,0,by decide,rfl⟩
  | succ k ih =>
    by_cases early : t<2^(k+1)-1
    · obtain ⟨d,hd,j,hj,eq⟩:=ih early
      exact ⟨d,hd.step,j,hj,eq⟩
    · have twice : (2:ℕ)^(k+1+1)=2^(k+1)*2 := pow_succ _ _
      rw [twice] at small
      have positive := Nat.two_pow_pos (k+1)
      exact ⟨k+1,le_rfl,t-(2^(k+1)-1),by omega,by unfold nodeNumber;omega⟩

def heapIndex (k : ℕ) : ↥(codes k) ≃ Fin (2^(k+1)-1) :=
  Equiv.ofBijective (fun x=>⟨nodeNumber x.1.1 x.1.2,by
    have valid:=codes_valid x.2
    exact (node_range valid.2).2.trans_le (Nat.sub_le_sub_right
      (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ valid.1)) _)⟩) (by
    constructor
    · intro x y h
      apply Subtype.ext
      exact node_inj (codes_valid x.2).2 (codes_valid y.2).2 (congrArg Fin.val h)
    · intro i
      obtain ⟨d,hd,j,hj,eq⟩:=node_onto k i.val i.isLt
      exact ⟨⟨(d,j),mem_codes hd hj⟩,Fin.ext eq⟩)

variable {V : Type} [Fintype V] {k slots : ℕ}

private def fields : ↥(keys (V:=V) k slots) ≃ V × ↥(codes k) × Fin slots where
  toFun x :=
    let h:=Finset.mem_product.mp (Finset.mem_product.mp x.2).2
    (x.1.1,⟨x.1.2.1,h.1⟩,⟨x.1.2.2,Finset.mem_range.mp h.2⟩)
  invFun x := ⟨(x.1,x.2.1.1,x.2.2.val),Finset.mem_product.mpr ⟨Finset.mem_univ _,
    Finset.mem_product.mpr ⟨x.2.1.2,Finset.mem_range.mpr x.2.2.isLt⟩⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

private def dense (rank : V↪Fin (Fintype.card V)) : ↥(keys (V:=V) k slots) ≃
    Fin ((Fintype.card V*(2^(k+1)-1))*slots) :=
  let host:=Equiv.ofBijective rank ((Fintype.bijective_iff_injective_and_card _).mpr ⟨rank.injective,by simp⟩)
  (((fields.trans (host.prodCongr ((heapIndex k).prodCongr (Equiv.refl _)))).trans (Equiv.prodAssoc _ _ _).symm).trans
    (finProdFinEquiv.prodCongr (Equiv.refl _))).trans finProdFinEquiv

private theorem dense_val (rank : V↪Fin (Fintype.card V)) (x : ↥(keys (V:=V) k slots)) :
    (dense rank x).val=((rank x.1.1).val*(2^(k+1)-1)+nodeNumber x.1.2.1.1 x.1.2.1.2)*slots+x.1.2.2 := by
  change x.1.2.2+slots*(nodeNumber x.1.2.1.1 x.1.2.1.2+(2^(k+1)-1)*(rank x.1.1).val)=_
  ring

private theorem digit_lt {a b x y m : ℕ} (hx : x < m) (hy : y < m) :
    a*m+x<b*m+y ↔ a<b ∨ (a=b ∧ x<y) := by
  rcases lt_trichotomy a b with lt|eq|gt
  · have enough:=Nat.mul_le_mul_right m lt
    rw [Nat.succ_mul] at enough
    omega
  · subst b;omega
  · have enough:=Nat.mul_le_mul_right m gt
    rw [Nat.succ_mul] at enough
    omega

private theorem digit_eq {a b x y m : ℕ} (hx : x < m) (hy : y < m) :
    a*m+x=b*m+y ↔ a=b ∧ x=y := by
  have one:=digit_lt (a:=a) (b:=b) hx hy
  have two:=digit_lt (a:=b) (b:=a) hy hx
  omega

private theorem dense_lt (rank : V↪Fin (Fintype.card V)) (x y : ↥(keys (V:=V) k slots)) :
    packedNumber (fun v=>(rank v).val) k slots x.val < packedNumber (fun v=>(rank v).val) k slots y.val ↔
    dense rank x<dense rank y := by
  have xh:=Finset.mem_product.mp (Finset.mem_product.mp x.2).2
  have yh:=Finset.mem_product.mp (Finset.mem_product.mp y.2).2
  let ix : ↥(codes k):=⟨x.val.2.1,xh.1⟩
  let iy : ↥(codes k):=⟨y.val.2.1,yh.1⟩
  have xb : nodeNumber x.1.2.1.1 x.1.2.1.2<2^(k+1)-1:=(heapIndex k ix).isLt
  have yb : nodeNumber y.1.2.1.1 y.1.2.1.2<2^(k+1)-1:=(heapIndex k iy).isLt
  have xs:=Finset.mem_range.mp xh.2
  have ys:=Finset.mem_range.mp yh.2
  rw [Fin.lt_def,dense_val,dense_val]
  simp only [packedNumber,digit_lt xs ys,digit_lt xb yb,digit_eq xb yb,
    digit_lt (lt_of_lt_of_le xb (Nat.sub_le _ _)) (lt_of_lt_of_le yb (Nat.sub_le _ _)),
    digit_eq (lt_of_lt_of_le xb (Nat.sub_le _ _)) (lt_of_lt_of_le yb (Nat.sub_le _ _))]

theorem compact_fullHost (rank : V↪Fin (Fintype.card V)) (x : ↥(keys (V:=V) k slots)) :
    (DescentRosterOrder.compact ((packedEmbedding rank (Function.Embedding.subtype _) (fun v=>v.2)).trans
      Fin.valEmbedding) x).val=
      ((rank x.1.1).val*(2^(k+1)-1)+nodeNumber x.1.2.1.1 x.1.2.1.2)*slots+x.1.2.2 := by
  classical
  rw [DescentRosterOrder.compact_read,←dense_val]
  let e:=dense (k:=k) (slots:=slots) rank
  change (Finset.univ.filter (fun y : ↥(keys (V:=V) k slots)=>
    packedNumber (fun v=>(rank v).val) k slots y.val<packedNumber (fun v=>(rank v).val) k slots x.val)).card=(e x).val
  simp only [dense_lt]
  have image : (Finset.univ.filter (fun y=>(e y)<e x)).map e.toEmbedding=Finset.Iio (e x) := by
    ext j
    simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,
      Equiv.toEmbedding_apply,Finset.mem_Iio]
    constructor
    · rintro ⟨y,lt,rfl⟩;exact lt
    · intro lt
      exact ⟨e.symm j,by simpa only [e.apply_symm_apply] using lt,e.apply_symm_apply _⟩
  exact (Finset.card_map _).symm.trans ((congrArg Finset.card image).trans (Fin.card_Iio _))

/-- The successor roster contains every nominal heap and slot, including unused hosts. -/
theorem card_fullHost (rank : V↪Fin (Fintype.card V)) :
    Fintype.card ↥(keys (V:=V) k slots)=Fintype.card V*(2^(k+1)-1)*slots := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (dense (k:=k) (slots:=slots) rank)

end
end Hierarchy.DescentHostDirectory

end OAI
