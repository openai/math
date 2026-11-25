import OAI.Computability.IntegerMultiplication.Param.Axis

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Param
open Filter Finset

theorem leak {I : Type} [DecidableEq I] (t s : I→ℤ) (D : ℤ)
    (E:Finset I) (v:2*(E.card:ℤ) ≤ D) (h₀:∀ i∈E,0≤t i)
    (h : ∀ i∈E, (D-2)*t i ≤ D*s i) :
    (D-2*E.card)*(∏ i∈E,t i) ≤ D*(∏ i∈E,s i) := by
  by_cases emp : E=∅
  · simp [emp]
  induction E using Finset.induction_on with
  | empty=>simp
  | @insert i E w ih=>
    have V : 2*((E.card:ℤ)+1)≤D := by
      rw [← Nat.cast_add_one]; simpa [card_insert_of_notMem w] using v
    have t0 : ∀ a∈E,0≤t a := fun a e=>h₀ a (mem_insert_of_mem e)
    have sx : ∀ a∈E,(D-2)*t a ≤ D*s a:= fun a e=>h a (mem_insert_of_mem e)
    have iH : (D-2*E.card)*(∏ i∈E,t i) ≤ D*(∏ i∈E,s i) := by
      by_cases z : E=∅
      · simp [z]
      exact ih (by linarith [V]) t0 sx z
    have G : (0:ℤ)≤E.card := by positivity
    have d₁ : 2≤D := by linarith
    have A : 0≤(∏ a∈E,t a) := Finset.prod_nonneg t0
    have x : 0≤t i := h₀ i (mem_insert_self ..)
    have y := h i (mem_insert_self ..)
    have z : 0≤s i := by
      apply nonneg_of_mul_nonneg_right (le_trans (mul_nonneg (by linarith) x) y)
        (by linarith : 0 < D)
    rw [prod_insert w,prod_insert w, card_insert_of_notMem w,Nat.cast_add_one]
    have R := mul_le_mul y iH (by apply mul_nonneg (by linarith) A) (mul_nonneg (by omega) z)
    apply le_of_mul_le_mul_left (a:=D) _ (by linarith)
    calc
     D*((D-2*((E.card:ℤ)+1))*(t i* ∏ a∈E,t a)) ≤
        (D-2)*t i*((D-2*E.card)* ∏ a∈E,t a) := by
        have p : 0 ≤ (E.card:ℤ)*t i*(∏ a∈E,t a) := by positivity
        nlinarith
     _ ≤ _ := R.trans (le_of_eq (by ring))

abbrev Direction n := Fin (lanes n)
def modSize n := ∏ i : Direction n, moduli n i.val
def landscape n := ∏ i : Direction n, side n i.val

theorem lane2 (n):2≤lanes n :=
  (show 2≤2^1 by decide).trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by unfold height; omega : 1≤height n))
def cursor (n):Direction n :=
  ⟨abbreviated n,by have h:=lane2 n; unfold abbreviated; omega⟩

private theorem singular (n) :
    (∑ i : Direction n, axle n i.val) = (lanes n-1)*span_ n+reach n := by
  let d:=lanes n
  let j:=cursor n
  have e (i:Direction n) (h:i∈Finset.univ.erase j): axle n i.val=span_ n := by
    rw [axle,ite_eq_right]
    intro t
    exact (Finset.mem_erase.mp h).1 (Fin.ext (show _ from t))
  have q : (Finset.univ.erase j).card=d-1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), card_univ, Fintype.card_fin]
  have t := Finset.sum_erase_add (s:=Finset.univ) (fun i:Direction n=> axle n i.val) (mem_univ j)
  rw [sum_congr (g:=fun _=>span_ n) rfl e,sum_const,q,nsmul_eq_mul,show axle n j.val= reach n from ite_eq_left rfl] at t
  exact t.symm

theorem load_r :
    Large fun n=> landscape n=load n := by
  filter_upwards [cut_large] with n h
  unfold landscape load side
  rw [Finset.prod_pow_eq_pow_sum,singular] -- orientation
  congr 1
  have w := lane2 n
  have t := slack_part n
  have e : lanes n=lanes n-1+1 := by omega
  have y : lanes n*span_ n=(lanes n-1)*span_ n+span_ n := by
    conv_lhs => rw [e, Nat.add_mul]; rw [one_mul]
  omega

theorem mod_le :
    Large fun n=> modSize n≤load n := by
  filter_upwards [load_r,axis_more] with n h g
  rw [← h]
  unfold modSize landscape
  exact Finset.prod_le_prod (fun i _=> (g i i.isLt).2.1.le)

theorem field_ :
    Large fun n=> load n≤2*modSize n := by
  filter_upwards [axis_margins,load_r] with n h z
  let d:=lanes n
  let D:ℤ:=8*d
  have v := leak (fun i:Direction n=> (side n i.val:ℤ))
    (fun i:Direction n=> (moduli n i.val:ℤ)) D Finset.univ
    (by simp [D,d]; omega) (fun i _=> by positivity) (fun i _=> by
      unfold D
      have y := (h i.val i.isLt).1.above
      change (8*d-2)*side n _ ≤ (8*d)*_ at y
      have x : 2≤8*d := by have t:=lane2 n; unfold d; omega
      exact_mod_cast y)
  simp only [Finset.card_univ,Fintype.card_fin,D] at v
  have e : (8*d:ℤ)-2*d =6*d := by ring
  rw [e] at v
  rw [← z]
  have Q := lane2 n
  have g : (6*d:ℤ) > 0 := by dsimp [d]; positivity
  have G : 8*(d:ℤ) ≤ 2*(6*d) := by linarith
  have f := le_trans v (mul_le_mul_of_nonneg_right G (Finset.prod_nonneg (by intros; positivity)))
  rw [show (2:ℤ)*(6*d)*_= (6*d)*(2*modSize n) from ?_] at f -- shape? mul_assoc first rewrites
  unfold landscape
  rw [← Nat.cast_prod] at f
  exact_mod_cast (le_of_mul_le_mul_left f g)
  unfold modSize; push_cast; ring
end Param

end IntegerMultiplication
end Computability
end OAI
