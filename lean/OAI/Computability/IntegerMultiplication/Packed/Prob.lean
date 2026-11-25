import OAI.Computability.IntegerMultiplication.Packed.Off
import OAI.Computability.IntegerMultiplication.Fix.Palace

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Strip Strip.Dims Adic Finset
-- low margin test. excludes 4 guard values each side.
variable {H L i n : ℕ}
def short (x : Block 2 n) := decide (number x < 4)
noncomputable def hazard (x : Seg L H) : Bool :=
  short (guard H L x) || short (mirror (guard H L x))
open Classical in
noncomputable def taint (x : Queue H L i) := decide (∃ j, hazard (x.2.1 j)=true)
noncomputable def spotted (x : Plate H L i) := taint x.2.1 || taint x.2.2
theorem valid (x : Plate H L i) (h : spotted x=false) : good x := by
  simp [spotted,taint] at h
  intro j
  have u {x : Seg L H} (h : hazard x=false) :
      8 ≤ totient x ∧ totient x < (2^width H L:ℕ)-8 := by
    have g : number (mirror (guard H L x)) + number (guard H L x) + 1 = 2^(L+H) := Adic.order .. -- mirrors?
    simp only [hazard,Bool.or_eq_false_iff,short,decide_eq_false_iff_not,not_lt] at h
    have e := parity x
    have ht : 2^width H L=2*(2^(L+H)) := by unfold width; rw [show H+1+L=L+H+1 by omega,Nat.pow_succ]; ring
    rw [ht]
    have hv := x.2.2.isLt
    obtain hr := Adic.order (guard H L x)
    omega
  exact ⟨u (h.1 j),u (h.2 j)⟩

theorem stays (x : Plate H L i) :
    spotted (ideal x)=spotted x := by
  unfold spotted taint
  have e : ∀ j,hazard (((ideal x).2.1).2.1 j)= hazard (x.2.1.2.1 j) := fun _ => rfl
  simp_rw [e]
  rfl

noncomputable def repair : Equiv.Perm (Plate H L i) :=
  (cruise order).symm.trans ideal
theorem valid_repair (x : Plate H L i) (h : spotted x=false) : repair x=x := by
  have ht := stays (ideal.symm x)
  rw [Equiv.apply_symm_apply,h] at ht
  have e := parallel _ (valid _ ht.symm)
  unfold repair
  rw [Equiv.trans_apply,show x=cruise order (ideal.symm x) from (e.trans (Equiv.apply_symm_apply ..)).symm,
    Equiv.symm_apply_apply,e]

-- one segment short count
private theorem few (n : ℕ) :
    (univ.filter fun i : Block 2 n => short i=true).card≤4 := by
  apply le_trans _ (Finset.card_range 4).le
  exact Finset.card_le_card_of_injOn number (by
    intro x e; simp [short] at e; simpa)
    (number_inj _ _ |>.injOn)
private theorem hazards :
    (univ.filter fun i : Seg L H => hazard i=true).card ≤ 16 := by
  classical
  let A : Finset (Block 2 (L+H)) := univ.filter fun i => short i=true
  let B : Finset (Block 2 (L+H)) := univ.filter fun i => short (mirror i)=true
  let f (x : Seg L H) := (guard H L x,x.2.2)
  have he : Function.Injective f := by
    intro x y h
    obtain ⟨v,m⟩ := Prod.mk.inj h
    obtain ⟨u,t⟩ := Prod.mk.inj ((tile 2 L H).cast.injective v)
    exact Prod.ext u (Prod.ext t m)
  have v :
      (univ.filter fun i : Seg L H => hazard i=true).card ≤
        ((A∪B) ×ˢ (univ : Finset (Fin 2))).card :=
    Finset.card_le_card_of_injOn f (by intro i e; simp [hazard] at e; simpa [A,B,f]) he.injOn
  have hb : B.card=A.card := by
    apply Finset.card_equiv mirror; intro; simp [B,A]
  have g := Finset.card_union_le A B
  have t : A.card≤4 := few _
  rw [card_product,Finset.card_univ,Fintype.card_fin] at v
  omega

-- conditional count through cart decomp
private theorem projected {A U V : Type} [Fintype A] [Fintype U] [Fintype V]
    (e : A ≃ U × V) (p : U → Prop) [DecidablePred p] :
    (univ.filter fun a : A => p (e a).1).card * Fintype.card U =
      ((univ : Finset U).filter p).card * Fintype.card A := by
  classical
  rw [Fintype.card_congr e,Fintype.card_prod]
  have u : (univ.filter fun a : A => p (e a).1).card =
      (((univ : Finset U).filter p) ×ˢ (univ:Finset V)).card := by
    apply Finset.card_equiv e; intro; simp
  rw [u,card_product,Finset.card_univ]
  ring

theorem spotted_rate :
    ((univ.filter (fun p : Plate H L i => spotted p=true)).card * 2^(width H L)) ≤
      32*i*Fintype.card (Plate H L i) := by
  classical
  let V := Plate H L i
  let a (b:Bool) (j:Fin i) := (univ:Finset V).filter fun x =>
    hazard ((bif b then x.2.1.2.1 j else x.2.2.2.1 j)) = true
  have e (b) (j) : (a b j).card*Fintype.card (Seg L H) ≤
      16*Fintype.card V := by
    let T := Top H × ({x : Fin i // x≠j}→Seg L H) × Tail L
    let u : Queue H L i ≃ Seg L H × T :=
      ( ((Equiv.refl _).prodCongr ((Equiv.piSplitAt j (fun _ => Seg L H)).prodCongr (Equiv.refl (Tail L)))).trans
        ((Equiv.refl (Top H)).prodCongr (Equiv.prodAssoc (Seg L H) _ _))).trans
          { toFun := fun (x : Top H × Seg L H × ({x:Fin i // x≠j}→Seg L H) × Tail L) => (x.2.1,x.1,x.2.2)
            invFun := fun x => (x.2.1,x.1,x.2.2)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
    let t : V ≃ (Queue H L i × Queue H L i) × Queue H L i :=
      bif b then
        {
        toFun := fun x => ((x.1,x.2.2),x.2.1)
        invFun := fun x => (x.1.1,x.2,x.1.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        }
      else (Equiv.prodAssoc ..).symm
    let s := (t.trans ((Equiv.refl _).prodCongr u)).trans
      {
      toFun := fun x : (Queue H L i × Queue H L i) × Seg L H × T => (x.2.1,x.1,x.2.2)
      invFun := fun x => (x.2.1,x.1,x.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      }
    have d := projected s (fun a=>hazard a=true)
    have h (x:V) : (s x).1=(bif b then x.2.1.2.1 j else x.2.2.2.1 j) := by cases b <;> rfl
    simp_rw [h] at d
    exact le_trans (le_of_eq d) (by gcongr; exact hazards)
  let J := (univ:Finset (Fin i)).biUnion fun j => a false j ∪ a true j
  have q : (univ.filter fun x : V => spotted x=true) ⊆ J := by
    intro x v
    simp [spotted,taint] at v
    simp only [J,Finset.mem_biUnion, Finset.mem_univ,true_and,a,Finset.mem_union,mem_filter,true_and]
    rcases v with ⟨j,e⟩ | ⟨j,e⟩
    exact ⟨j,.inr e⟩
    exact ⟨j,.inl e⟩
  have hs := Finset.card_biUnion_le (s:=univ) (t:=fun j => a false j ∪ a true j)
  have z : Fintype.card (Seg L H)=2^width H L := by
    simpa using ((Fintype.card_congr (furrow H L).cast).trans count)
  rw [← z]
  calc
   _ ≤ (∑ j : Fin i, (a false j ∪ a true j).card)*Fintype.card (Seg L H) :=
     Nat.mul_le_mul_right _ ((Finset.card_le_card q).trans hs)
   _ ≤ ∑ _j : Fin i, (32*Fintype.card V) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum; intro j _
    have u := (e false j); have v := (e true j)
    apply (Nat.mul_le_mul_right _ (Finset.card_union_le ..)).trans
    rw [Nat.add_mul]; omega
   _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,nsmul_eq_mul]; change i*(32*Fintype.card V)=32*i*Fintype.card V; ring
end Packed

end IntegerMultiplication
end Computability
end OAI
