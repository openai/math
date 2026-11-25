import OAI.Hierarchy.ProbeSocketDegree
import OAI.Hierarchy.ProbeReportedGeometry

namespace OAI
/-! # The fixed public party's genuine incident socket count -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.Incident
open AdaptiveProbe ReportSockets
open scoped Classical

variable {h W k attempts : ℕ}
def choose {V : Type} (p : V×V) : Bool→V | false=>p.1 | true=>p.2

theorem choose_injective {V : Type} (p : V×V) (neq : p.1≠p.2) : Function.Injective (choose p) := by
  rintro (_|_) (_|_) e <;> first | rfl | exact (neq e).elim | exact (neq e.symm).elim

abbrev Fiber {V I : Type} (f : I→V) (v : V) := {i // f i=v}

def split {I J V : Type} (f : I→V) (g : J→V) (v : V) :
    Fiber (Sum.elim f g) v ≃ Fiber f v ⊕ Fiber g v where
  toFun | ⟨.inl i,h⟩=>.inl ⟨i,h⟩ | ⟨.inr j,h⟩=>.inr ⟨j,h⟩
  invFun | .inl ⟨i,h⟩=>⟨.inl i,h⟩ | .inr ⟨j,h⟩=>⟨.inr j,h⟩
  left_inv := by rintro ⟨(i|j),_⟩ <;> rfl
  right_inv := by rintro (⟨i,_⟩|⟨j,_⟩) <;> rfl

def lr {I V : Type} (p : I→V×V) (v : V) :
    Fiber (fun a : I×Bool=>choose (p a.1) a.2) v ≃ Fiber (fun i=>(p i).1) v ⊕ Fiber (fun i=>(p i).2) v where
  toFun | ⟨(i,false),h⟩=>.inl ⟨i,h⟩ | ⟨(i,true),h⟩=>.inr ⟨i,h⟩
  invFun | .inl ⟨i,h⟩=>⟨(i,false),h⟩ | .inr ⟨i,h⟩=>⟨(i,true),h⟩
  left_inv := by rintro ⟨⟨i,(_|_)⟩,_⟩ <;> rfl
  right_inv := by rintro (⟨i,_⟩|⟨j,_⟩) <;> rfl

def sumHalf {I J V : Type} (a : I→V×V) (b : J→V×V) (v : V) :
    Fiber (fun t : (I⊕J)×Bool=>choose (Sum.elim a b t.1) t.2) v ≃
      Fiber (fun t : I×Bool=>choose (a t.1) t.2) v ⊕ Fiber (fun t : J×Bool=>choose (b t.1) t.2) v where
  toFun | ⟨(.inl i,s),h⟩=>.inl ⟨(i,s),h⟩ | ⟨(.inr j,s),h⟩=>.inr ⟨(j,s),h⟩
  invFun | .inl ⟨(i,s),h⟩=>⟨(.inl i,s),h⟩ | .inr ⟨(j,s),h⟩=>⟨(.inr j,s),h⟩
  left_inv := by rintro ⟨⟨(i|j),s⟩,_⟩ <;> rfl
  right_inv := by rintro (⟨⟨i,s⟩,_⟩|⟨⟨j,s⟩,_⟩) <;> rfl

private theorem card_halves {I J V : Type} [Fintype I] [Fintype J] [DecidableEq V]
    (f : I→V×V) (g : J→V×V) (v : V) :
    Fintype.card (Fiber (fun a : (I⊕J)×Bool=>choose (Sum.elim f g a.1) a.2) v)=
      Fintype.card (Fiber (fun a : I×Bool=>choose (f a.1) a.2) v)+
        Fintype.card (Fiber (fun a : J×Bool=>choose (g a.1) a.2) v) := by
  classical
  exact (Fintype.card_congr (sumHalf f g v)).trans Fintype.card_sum

private theorem card_sides {I V : Type} [Fintype I] [DecidableEq V] (p : I→V×V) (v : V) :
    Fintype.card (Fiber (fun a : I×Bool=>choose (p a.1) a.2) v)=
      Fintype.card (Fiber (fun i=>(p i).1) v)+Fintype.card (Fiber (fun i=>(p i).2) v) := by
  classical
  exact (Fintype.card_congr (lr p v)).trans Fintype.card_sum

private theorem nat_halves {I J V : Type} [Fintype I] [Fintype J] [DecidableEq V]
    (f : I→V×V) (g : J→V×V) (v : V) :
    Nat.card (Fiber (fun a : (I⊕J)×Bool=>choose (Sum.elim f g a.1) a.2) v)=
      Nat.card (Fiber (fun a : I×Bool=>choose (f a.1) a.2) v)+Nat.card (Fiber (fun a : J×Bool=>choose (g a.1) a.2) v) := by
  simpa only [Nat.card_eq_fintype_card] using card_halves f g v

private theorem nat_sides {I V : Type} [Fintype I] [DecidableEq V] (p : I→V×V) (v : V) :
    Nat.card (Fiber (fun a : I×Bool=>choose (p a.1) a.2) v)=
      Nat.card (Fiber (fun i=>(p i).1) v)+Nat.card (Fiber (fun i=>(p i).2) v) := by
  simpa only [Nat.card_eq_fintype_card] using card_sides p v

def room (k degree attempts : ℕ) := 2*k+4*k*k+2+2*degree+2+2*attempts

variable (S : PurchaseSampler) {d : ℕ}
private def radius (x : Radius h d k) := freeEnds (S:=S) (.inl x)
private def cross (x : Cross h d k) := freeEnds (S:=S) (.inr (.inl x))

private theorem column_card {V A : Type} [Fintype V] [Fintype A] {Z : Type} [Fintype Z]
    (endpoints : V×A→(V×Z)×(V×Z)) (v : V×Z)
    (located : ∀i s,(choose (endpoints i) s).1=i.1)
    (neq : ∀i,(endpoints i).1≠(endpoints i).2) :
    Fintype.card (Fiber (fun t : (V×A)×Bool=>choose (endpoints t.1) t.2) v)≤Fintype.card A := by
  apply Fintype.card_le_of_injective (fun t=>t.val.1.2)
  rintro ⟨⟨⟨i,a⟩,s⟩,hs⟩ ⟨⟨⟨j,b⟩,t⟩,ht⟩ eq
  change a=b at eq
  subst b
  have col : i=j := (located (i,a) s).symm.trans ((congrArg Prod.fst (hs.trans ht.symm)).trans (located (j,a) t))
  subst j
  obtain rfl := choose_injective _ (neq (i,a)) (hs.trans ht.symm)
  rfl

theorem free_card (v : Site h d k) : Fintype.card (Fiber (fun t : Free S h d k×Bool=>choose (freeEnds t.1) t.2) v)
    ≤2*k+4*k*k+2+2*S.degree := by
  have r := column_card (radius (h:=h) (d:=d) (k:=k) S) v (by intro i s;cases s <;>rfl)
    (by rintro ⟨c,a⟩; simp [radius,freeEnds])
  have c := column_card (cross (h:=h) (d:=d) (k:=k) S) v (by intro i s;cases s <;>rfl) (by
    rintro ⟨u,a,s,t⟩ eq
    exact a.2.ne (congrArg Prod.fst (Option.some.inj (congrArg Prod.snd eq))))
  have axis : Fintype.card {a : Fin k×Fin k // a.1<a.2}≤k*k := by
    simpa using Fintype.card_le_of_injective (fun a : {a : Fin k×Fin k // a.1<a.2}=>a.val) Subtype.val_injective
  have f₁ := fixed_fst_card S v
  have f₂ := fixed_snd_card S v
  have s₁ := sample_fst_card S v
  have s₂ := sample_snd_card S v
  have ends : (freeEnds : Free S h d k→Site h d k×Site h d k)=
      Sum.elim (radius S) (Sum.elim (cross S) (Sum.elim (fixedEnds S) (sampleEnds S))) := by
    funext e
    rcases e with e|e|e|e <;> rfl
  rw [←Nat.card_eq_fintype_card,ends,nat_halves (radius S) _ v,nat_halves (cross S) _ v,
    nat_halves (fixedEnds S) _ v,nat_sides (fixedEnds S) v,nat_sides (sampleEnds S) v]
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at r c
  simp only [←Nat.card_eq_fintype_card] at r c axis f₁ f₂ s₁ s₂
  dsimp only [Fiber] at *
  have both := Nat.add_le_add (Nat.add_le_add f₁ f₂) (Nat.add_le_add s₁ s₂)
  have chord := c.trans (Nat.mul_le_mul_right (2*2) axis)
  exact (Nat.add_le_add r (Nat.add_le_add chord both)).trans (by ring_nf;omega)

variable {S}
theorem positive_card (v : Site h (2^W) k) :
    Fintype.card (Fiber (physicalSite (h:=h) (W:=W) (k:=k) (attempts:=attempts)) v)≤1+attempts := by
  let code : Fiber (physicalSite (h:=h) (W:=W) (k:=k) (attempts:=attempts)) v→Unit⊕Fin attempts :=
    fun x=>Sum.elim (fun _=>Sum.inl ()) Sum.inr x.val.2
  have inject : Function.Injective code := by
    rintro ⟨⟨x,(s|a)⟩,hx⟩ ⟨⟨y,(t|b)⟩,hy⟩ eq
    · have pair := hx.trans hy.symm
      have col : x=y := Sum.inl.inj (Sum.inr.inj (congrArg Prod.fst pair))
      exact Subtype.ext (Prod.ext col (congrArg Sum.inl (congrArg Prod.snd pair)))
    · exact (Sum.inl_ne_inr eq).elim
    · exact (Sum.inr_ne_inl eq).elim
    · have col : x=y := Sum.inl.inj (Sum.inr.inj (congrArg Prod.fst (hx.trans hy.symm)))
      exact Subtype.ext (Prod.ext col (congrArg Sum.inr (Sum.inr.inj eq)))
  simpa using Fintype.card_le_of_injective code inject

end Hierarchy.ProbeStage.CoreBoard.Incident

end
end OAI
