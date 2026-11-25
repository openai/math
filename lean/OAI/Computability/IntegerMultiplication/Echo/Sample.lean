import OAI.Computability.IntegerMultiplication.Echo.Pad

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Echo
open Finset Scale Param IntegerMultiplication.Fourier Cap
open scoped BigOperators ComplexConjugate
noncomputable section
-- linear forms in padded layout, one axis
variable {s t:ℕ} [NeZero s] [NeZero t]
abbrev Local t:= Spot t→Spot t→ℂ
def page (L: Local t) (x : Arr t ℂ) (i : Spot t) : ℂ :=
  ∑ j,L i j * x j
def after (B A: Local t) : Local t := fun i j=> page B (fun a=> A a j) i
omit [NeZero t] in
@[simp] theorem after_page (B A: Local t) (x:Arr t ℂ):
    page (after B A) x=page B (page A x) := by
  funext i; unfold page after; unfold page
  simp_rw [sum_mul,mul_sum,mul_assoc]; rw [sum_comm]

variable (e:s≤t)
def pk (_k _q : ℕ) (i:Spot s) (a:ℤ):Spot s :=
  wrap s (rep i+a)
def growing (D L : ℕ) : Local t :=
  fun i j=> ∑ a∈rad L, if glue e (nextSample i a)=j then win D i (nextSample i a : Spot s) else 0
def mounting (s:ℕ)(u:Bool):Local t :=
    kernel (bif u then (s:ℕ) else -(s:ℤ))
def closing (D J k : ℕ)(u:Bool):Local t :=
  fun i j=> hair (s:=s) (fun c:Spot s=> ∑ a∈rad (k*J),
    let z:=pk k J c a
    if pick s t e z=j then Garden.climate u (mixTable t D (nhood J) k c z) s else 0) i
def ideal (Q:ℕ) (u:Bool): Local t :=
  fun i j=>hair (s:=s) (fun z:Spot s=> hair (s:=s)
    (fun y:Spot s=> kernel (bif u then -(Q:ℤ) else (Q:ℤ)) z y /
      (bif u then (s:ℂ) else 1)) j) i
-- ideal missing e in args unless include e (hair depends s explicitly but def includes s implicit), e unused.

def port (D L J k : ℕ) (u:Bool):Local t :=
  after (closing e D J k u) (after (mounting (t:=t) s u) (growing e D L))

omit [NeZero t] in
theorem page_A (D L) (x:Arr t ℂ) (i:Spot t):
    page (growing e D L) x i=sample s t D L (x ∘ glue e) i := by
  unfold page growing sample
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a h=> ?_
  dsimp only [Function.comp_apply]
  simp only [ite_mul,zero_mul,sum_ite_eq,mem_univ,ite_true]

omit [NeZero s] [NeZero t] in
theorem page_M (u:Bool) (x:Arr t ℂ) :
    page (mounting s u) x=dft t (bif u then (s:ℕ) else -(s:ℤ)) x := rfl

omit [NeZero t] in
theorem page_B (D J k) (u:Bool) (x:Arr t ℂ):
    page (closing e D J k u) x=hair (fun c:Spot s=> ∑ a∈rad (k*J),
      let z:= pk k J c a
      Garden.climate u (mixTable t D (nhood J) k c z) s*x (pick s t e z)) (t:=t) := by -- ext?
  funext i
  unfold page closing hair
  by_cases h:i.val< s
  · simp only [dite_eq_left h,sum_mul,ite_mul,zero_mul]
    rw [sum_comm]
    refine sum_congr rfl fun a _=>?_
    simp only [sum_ite_eq,mem_univ,ite_true]
  simp only [dite_eq_right h,zero_mul,sum_const_zero]

def shellD (Q:ℤ) (f:Arr t ℂ) : Arr t ℂ :=
  hair (dft s Q (f ∘ glue e))
-- ideal page
omit [NeZero s] [NeZero t] in
theorem page_I (q) (u:Bool) (f:Arr t ℂ):
    page (ideal (s:=s) q u) f = hair
    (fun i:Spot s=> (dft s (bif u then -(q:ℤ) else (q:ℕ)) (f ∘ glue e) i)/(bif u then (s:ℂ) else 1)) := by
  classical
  funext i
  unfold page ideal
  by_cases h:i.val< s
  · simp only [hair,dite_eq_left h]
    rw [sumImage (glue e) (glue_inj e)]
    · unfold dft; rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j hj=> ?_
      dsimp only [glue,Function.comp_apply]
      rw [dite_eq_left j.isLt]
      unfold kernel; ring
    · intro t hx
      have t₁ : ¬t.val< s := fun p=> hx ⟨⟨t.val,p⟩,rfl⟩
      rw [dite_eq_right t₁,zero_mul]
  simp only [hair,dite_eq_right h,zero_mul,sum_const_zero]

omit [NeZero t] in
theorem patience (D L J k) (hk : 2*(k*J) < s) (x:Arr t ℂ):
    page (port e D L J k false) x= hair (restore e D J k
      (dft t (-(s:ℤ)) (sample s t D L (x ∘ glue e)))) := by
  rw [port,after_page,after_page,page_B,page_M,show page (growing e D L) x= sample s t D L (x ∘ glue e) from funext (page_A e D L x)]
  congr 1
  funext i; rw [restore_short ..]; dsimp only [pk,Garden.climate]; simp only [Bool.cond_false]
  exact hk
theorem conjugate (n:ℕ) (a:ℤ):
    conj (phase n a)=phase n (-a) := by
  unfold phase cis
  rw [← Complex.exp_conj]; simp
  rw [map_ofNat]; congr 1; ring

omit [NeZero t] in
theorem twin (D L J k):
    port e D L J k true= fun i j=>conj (port e D L J k false i j)/(s:ℂ) := by
  have A i j: conj (growing e D L i j)=growing e D L i j := by
    unfold growing
    simp only [map_sum]
    apply sum_congr rfl; intro _ _; split; simp only [win,Complex.conj_ofReal]; simp
  have M (i j:Spot t) : mounting s true i j=conj (mounting s false i j) := by
    unfold mounting kernel; simp only [Bool.cond_true,Bool.cond_false,conjugate,neg_neg,neg_mul]
  have B i j : closing e D J k true i j=conj (closing e D J k false i j)/ (s:ℂ) := by
    unfold closing hair; split
    · dsimp only; rw [map_sum,Finset.sum_div]; apply sum_congr rfl; intros; split
      · simp [Garden.climate]
      simp
    · simp
  funext i j; unfold port after page
  simp only [B,M,map_sum,map_mul,A, Finset.sum_div]
  refine sum_congr rfl fun _ _=> ?_
  ring
omit [NeZero s] [NeZero t] in
theorem brothers (i j:Spot t) (Q:ℕ):
    ideal (s:=s) Q true i j=conj (ideal (s:=s) Q false i j)/(s:ℂ) := by
  unfold ideal hair; split
  · dsimp only; split
    · simp only [Bool.cond_false,div_one,Cap.kernel,conjugate,Bool.cond_true,
        neg_neg,neg_mul]
    simp
  simp

end
end Echo

end IntegerMultiplication
end Computability
end OAI
