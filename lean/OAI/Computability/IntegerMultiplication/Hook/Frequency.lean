import OAI.Computability.IntegerMultiplication.Hook.Epos

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Hook
open Strip Dims Loom Adic Code Net Net.Walsh Haze Earth Phase Packed Axon Staff Dusk Bits
noncomputable section
variable {f k:ℕ}
def refl : Equiv.Perm (Fin (f*k)) :=
  (finProdFinEquiv.symm.trans ((Equiv.refl (Fin f)).prodCongr (Fin.revPerm : Equiv.Perm (Fin k)))).trans finProdFinEquiv
abbrev η (i:Fin f) (j:Fin k) := finProdFinEquiv (i,j)
theorem radiant (i : Fin f) (j : Fin k) : refl (η i j)=η i (Fin.rev j) := by
  simp only [refl,Equiv.trans_apply,η,Equiv.symm_apply_apply,Equiv.prodCongr_apply]
  rfl

private theorem code_ (i : Fin (f*k)) :
    (refl i).val=(i.val/k)*k+(k-(i.val%k+1)) := by
  obtain ⟨⟨i,j⟩,h⟩ := Equiv.surjective (finProdFinEquiv (m:=f) (n:=k)) i
  subst h
  rw [radiant]
  have : k>0 := Nat.pos_of_ne_zero (fun t=> (let k₁ := j.isLt; by omega))
  change k-(j.val+1)+k*i.val= (j.val+k*i.val)/k*k+ (k-((j.val+k*i.val)%k+1))
  simp [Nat.add_mul_div_left j.val i.val this,Nat.div_eq_of_lt j.isLt,Nat.mod_eq_of_lt j.isLt]
  ring
variable {I J W A X: Type} [Codec X] (d₀:X) [Fintype J] [DecidableEq J] [Fintype W] (dl : Guild J W A Motif.sigma) (R₁ : Series W)
variable (p t : I→Tape) (f g j y w U : I→ℕ) {T:I→Type} (z:(i:I)→Series (T i)) {r:Regime I}
variable (h : ArrayCards r p t w)
variable (F: Realizes r f) (G:Realizes r g) (J₁:Realizes r j) (Y:Realizes r y)
variable (u:∀ i,((z i).count+1)*(w i+1)≤U i)
variable (K e m : I→ℕ) (data_ : Slice r (norm f g j y) K e m w)

include F G J₁ Y
theorem refl_told :
    r.Has fun i=> Curtain.paint (@refl (f i) (Ht (g i) (j i) (y i))) := by
  let n i := Ht (g i) (j i) (y i)
  let E := norm f g j y
  have fE := realizes_n F G J₁ Y
  have v := landing E fE n ((G.times J₁).plus Y)
  have j0 := floor_ E fE
  unfold Curtain.paint
  simp_rw [code_]
  exact harvest E fE _ (((j0.dividing v).times v).plus (v.minused ((j0.rem v).plus (Realizes.fix 1))))
include h dl R₁ u data_
-- mirrored logical frequencies using input row representation
abbrev rowL (i:I) : pos p t f g j y i ≃ residue p t f g j y i where
  toFun x := ((x.1,x.2.2),eye _ _ _ _ x.2.1)
  invFun x := (x.1.1,(eye _ _ _ _).symm x.2,x.1.2)
  left_inv x := by simp
  right_inv x := by simp
abbrev crate (x : (i:I)→ residue p t f g j y i→T i→Grain (w i)) :=
  orchid (feild p t f g j y) z w fun i=> x i ∘ rowL p t f g j y i

omit h dl R₁ u data_ F G J₁ Y in
private theorem m_r {f v:ℕ} (x : Fin f→Block 2 v) (i a) :
    let z := atoms f v
    let w := (layBit _).symm ((layBit _ (z.cast x)) ∘ refl)
    (layBit v) (z.cast.symm w i) a = Axon.refl_ ((layBit v) (x i)) a := by
  dsimp only
  let z := atoms f v
  rw [← after ((atoms f v).cast.symm _) i a,Equiv.apply_symm_apply,Equiv.apply_symm_apply,Function.comp_apply,radiant i a,after]; rfl

def reverseR (i:I) (x : Datum p t f g j y w (T:=T) i) : Datum p t f g j y w (T:=T) i :=
  fun a=> x (a.1, reface a.2)

theorem trek (x : (i:I)→ Datum p t f g j y w i (T:=T)) :
    let C := crate p t f g j y w z
    Breeze (feeK K e) r (Globe p t f g j y) U
      (together r.header (C x)) (C fun i=> reverseR p t f g j y w i (x i)) := by
  let n i := norm f g j y i
  let C i := rS p t f g j y i
  let q (i:I) := (@refl (f i) (altitude g j y i))
  let V i := rowL p t f g j y i
  let y0 (i:I) := x i ∘ V i ∘ (C i).cast.symm
  have U1 i : (z i).count*(w i+1) ≤ U i := (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans (u i)
  have e0 := ripple dl R₁ p t n K e m w h data_ z U U1 q (refl_told f g j y F G J₁ Y) y0
  change Breeze _ _ (fun i=> (spec p t n i).count) _
    (together _ (fun i=> stripe (spec p t n i) (fun a=>strip (z i) (Dusk.mark ∘ y0 i a))))
    (fun i=>stripe (spec p t n i) (fun a=>strip (z i) (Dusk.mark ∘ y0 i (Curtain.induce (q i) a)))) at e0
  have W1 i : ∀ f,stripe (spec p t n i) f=stripe (feild p t _ _ _ _ i) (f ∘ (C i).cast) := (C i).packet
  have R1 i : (spec p t n i).count=Globe p t f g j y i := (C i).cost.symm
  simp_rw [W1,R1] at e0
  simp only [Function.comp_def,y0,Equiv.symm_apply_apply] at e0
  convert e0 using 1
  · rfl
  unfold crate orchid cloth stackRun
  funext i; apply congrArg (stripe (feild p t f g j y i)); funext a
  apply congrArg (stripe (z i)); funext B
  suffices t : V i ((C i).cast.symm (Curtain.induce (q i) ((C i).cast a))) =
      ((V i a).1,reface (V i a).2) by
    change send (Dusk.mark (x i _ _)) = send (Dusk.mark (x i (V i _) _))
    rw [t]
  exact Prod.ext rfl (funext fun j=>funext fun v=>m_r a.2.1 _ _)
end
end Hook

end IntegerMultiplication
end Computability
end OAI
