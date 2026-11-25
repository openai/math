import OAI.Computability.IntegerMultiplication.Garden.Germ

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Garden
open IntegerMultiplication.Fourier Code Brief Finset
noncomputable section
variable {s:ℕ} (t D:ℕ) [NeZero s]
def preset (D s t:ℕ) := 2*D*(s+1)+t
def solar (D s t l:ℕ):= 2*preset D s t+2*l+3
def goal_ (D s t l k:ℕ):= solar D s t l*(k+2)+1

omit [NeZero s] in
private theorem common (f: Spot s→ℤ) (hf:∀i, 0 ≤f i ∧ f i ≤2^(2*D)):
    |∏ x:Spot s,f x| ≤ (2:ℤ)^(2*D*s) := by
  rw [pow_mul]
  rw [abs_of_nonneg (prod_nonneg fun _ _=> (hf _).1)]
  calc
    _ ≤ ∏ i:Spot s,(2:ℤ)^(2*D) := Finset.prod_le_prod₀ (fun i _=> (hf i).1) (fun i _ => (hf i).2)
    _ = _ := by simp [Spot]
omit [NeZero s] in
private theorem valueHold (i:Spot s):
    (0:ℤ) ≤ value_ t D i ∧ (value_ t D i:ℤ) ≤ 2^(2*D) :=
  ⟨by positivity,by exact_mod_cast (jewel_le ..)⟩
omit [NeZero s] in
private theorem blockHold :
    |blocks (s:=s) t D| ≤ (2:ℤ)^(2*D*s) := common _ _ (valueHold t D)
omit [NeZero s] in
private theorem fence (i:Spot s) :
    |left t D i| ≤ (2:ℤ)^(2*D*s) :=
  common _ (fun j=>if j=i then 1 else (value_ t D j:ℤ)) (by
    intro j; split
    · exact ⟨by decide,one_le_pow₀ (by norm_num)⟩
    exact valueHold t D j)

omit [NeZero s] in
theorem baseline_p (v:∀ i:Spot s,(delta s t i).natAbs ≤D) (ht:0<t):
    0 < baseline t D s := by
  unfold baseline blocks
  refine mul_pos (by exact_mod_cast ht) (prod_pos (fun i _=>?_))
  exact_mod_cast (jewel_pos _ _ (v i))
omit [NeZero s] in
theorem baseHold :
    |baseline t D s| ≤ (2:ℤ)^(preset D s t) := by
  unfold baseline
  rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
  have A : (t:ℤ)≤ (2:ℤ)^t := by exact_mod_cast (Nat.lt_pow_self (a:=2) (n:=t) (by decide)).le
  calc
    _ ≤ 2^t*2^(2*D*s) := by gcongr; exact blockHold ..
    _ = (2:ℤ)^(2*D*s+t) := by rw [pow_add,mul_comm]
    _ ≤ _ := by unfold preset; gcongr <;> [norm_num;nlinarith]
omit [NeZero s] in
theorem firstHold (i j:Spot s) :
    |begins t D i j| ≤ (2:ℤ)^(preset D s t) := by
  unfold begins
  split
  · rw [abs_mul,abs_of_nonneg (by positivity : (0:ℤ)≤4^D)]
    calc
      _ ≤ 4^D*(2:ℤ)^(2*D*s) := by gcongr; exact fence ..
      _ = (2:ℤ)^(2*D*(s+1)) := by rw [show (4:ℤ)=(2:ℤ)^2 by norm_num,← pow_mul,← pow_add]; congr 1; ring
      _ ≤ _ := by unfold preset; gcongr <;> [norm_num; omega]
  · simp

omit [NeZero s] in
theorem bentHold (i:Spot s) (a:ℤ) :
    |bends_ t D i a| ≤ (2:ℤ)^(preset D s t) := by
  unfold bends_
  rw [abs_mul,abs_mul, abs_of_nonneg (Int.natCast_nonneg _), abs_of_nonneg (Int.natCast_nonneg _)]
  calc
    _ ≤ (2^t * (2:ℤ)^(2*D*s))*2^(2*D) := by
      gcongr
      · exact_mod_cast (Nat.lt_pow_self (a:=2) (n:=t) (by decide)).le
      · exact fence ..
      · exact_mod_cast jewel_le ..
    _ = _ := by
      unfold preset; rw [← pow_add,← pow_add]; congr 1; ring

def Shield (v:Notes s) (k:ℕ) : Prop :=
  (∀ i:Spot s, |v.1 i| ≤ (2:ℤ)^k) ∧ |v.2| ≤ (2:ℤ)^k
-- curriculum cost
theorem defend (l) (j:Spot s) {v:Notes s} {k} (u:Shield v k) :
    Shield (act (herb t D l j) v) (k+solar D s t l) := by
  let P:= preset D s t
  let Q:= solar D s t l
  have v₀ : 1≤(2:ℤ)^P := one_le_pow₀ (by decide)
  let R : ℤ:= 2^P
  have p : P≤Q := by unfold Q solar P; omega
  have C : (2*(2*l+1):ℤ) ≤ (2:ℤ)^(2*l+2) := by
    have t := Nat.lt_pow_self (a:=2) (n:=2*l+1) (by decide)
    have I : 2*(2*l+1) ≤ (2:ℕ)^(2*l+1)*2 := by omega
    rw [← pow_succ] at I
    exact_mod_cast I
  have hp: (nhood l).card ≤ 2*l+1 :=
    (Finset.card_le_card (Finset.erase_subset 0 (rad l))).trans (by rw [rad_card])
  constructor
  · intro i
    change |begins t D i j * baseline t D _ * v.2 + ∑ j:Spot s, -curves t D l i j * v.1 j| ≤ _
    simp only [neg_mul,sum_neg_distrib,curves_apply]
    apply (abs_add_le _ _).trans
    have v1: |begins t D i j * baseline t D s * v.2| ≤ R*R*2^k := by
      rw [abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (firstHold ..) (baseHold ..) (abs_nonneg _) (by unfold R; positivity))
        u.2 (abs_nonneg _) (by unfold R; positivity)
    have v2: ∀ a:ℤ,|bends_ t D i a * v.1 (wrap s (rep i+a))| ≤ R*R*2^k := by
      intro a
      rw [abs_mul]
      have e:|bends_ t D i a|≤R := bentHold ..
      have t := mul_le_mul e (u.1 (wrap s (rep i+a))) (abs_nonneg _) (by unfold R; positivity)
      unfold R at *; calc
       _ ≤ _ := t
       _ ≤ _ := by gcongr; apply le_mul_of_one_le_right <;> first|positivity|exact v₀
    have v3:= (abs_sum_le_sum_abs (fun a=> bends_ t D i a*v.1 (wrap s (rep i+a))) (nhood l)).trans
      (sum_le_sum fun a _=>v2 a)
    rw [abs_neg]
    apply (add_le_add v1 v3).trans
    rw [Finset.sum_const,nsmul_eq_mul]
    have E: 1+((nhood l).card:ℤ) ≤ (2:ℤ)^(2*l+2) :=
      le_trans (by have t : ((nhood l).card:ℤ) ≤ 2*l+1 := by exact_mod_cast hp
                   omega) C -- whitespace
    calc
     _ = (1+(nhood l).card:ℤ)*(R*R*2^k) := by ring
     _ ≤ (2:ℤ)^(2*l+2)*(R*R*2^k) := by gcongr
     _ ≤ _ := by
       unfold R; rw [← pow_add,← pow_add,← pow_add]
       unfold solar P
       apply pow_le_pow_right₀ (by decide : 1≤(2:ℤ))
       omega
  · change |baseline t D s*v.2| ≤ _
    rw [abs_mul]
    apply (mul_le_mul (baseHold ..) u.2 (abs_nonneg _) (by positivity)).trans
    rw [← pow_add]
    exact pow_le_pow_right₀ (by decide) (by unfold solar; omega)

theorem canon_hat (l k) (j:Spot s) :
    Shield (canon t D l k j) (preset D s t+k*solar D s t l) := by
  induction k with
  | zero=> simp [canon,first,Shield,firstHold,one_le_pow₀ (a:=(2:ℤ)) (by norm_num)]
  | succ k ih=>
    rw [canon,Function.iterate_succ_apply',Nat.add_mul,Nat.one_mul,← Nat.add_assoc]
    exact defend t D _ _ ih

theorem schoolbook (l k:ℕ) (j:Spot s) (a:ℕ) (q:a<k):
    trim (goal_ D s t l k) (canon t D l (a+1) j) := by
  have A:=canon_hat t D l (a+1) j
  let P:=preset D s t
  let V:=solar D s t l
  let w:=P+(a+1)*V
  have t_ : w < goal_ D s t l k := by
    unfold w goal_
    have j:=Nat.mul_le_mul_right V q
    have p : P≤V := by unfold V P solar; omega
    change P+(a+1)*V < V*(k+2)+1
    nlinarith
  have X : (2:ℤ)^w < 2^goal_ D s t l k := by gcongr; norm_num
  have z (n:ℤ) (h: |n| ≤ (2:ℤ)^w) : n.natAbs < 2^goal_ D s t l k := by
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h.trans_lt X
  exact ⟨fun i=> z _ (A.1 i), z _ A.2⟩
end
end Garden

end IntegerMultiplication
end Computability
end OAI
