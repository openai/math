import OAI.Computability.IntegerMultiplication.Halo.Strand

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Halo
open Param Scale Echo Cap IntegerMultiplication.Fourier Finset Cone Grid Axon Dusk
open scoped ComplexConjugate
noncomputable section
variable {n:ℕ} (i:Bool)
def jolt {k:ℕ}(x:Grain k):Grain k:= ⟨x.re,-x.im⟩
def clime (x:G n) := bif i then jolt x else x
def wist (x:ℂ) := bif i then conj x else x
def skirt (x:Farm n):Farm n:=clime i ∘ x
def blush (x:Land n):Land n:=wist i ∘ x
variable (h: Season n) (b:ℕ→ G n)
def opera : Organ n:= ⟨fun i=>skirt i ∘ umi h b ∘ skirt i⟩

private theorem negL {k:ℕ} (x:day k):
    lift (-x)= -lift x := by
  have e := send_lift (t:=-Grid.lift x) (by simpa only [abs_neg] using lift_limit x)
  simpa using e
@[simp] theorem meaningJ (k j : ℕ) (x : Grain j) :
    meaning k j (jolt x) = conj (meaning k j x) := by
  unfold meaning jolt toC Grid.aspect
  simp [negL,map_ofNat]

@[simp] theorem look_s (x:G n):
    look n (clime i x)=wist i (look n x) := by cases i <;> simp [look,clime,wist]
@[simp] theorem wist_n (x:ℂ):‖wist i x‖=‖x‖ := by cases i <;> simp [wist]
@[simp] theorem wist_w (x:ℂ):wist i (wist i x)=x:=by cases i <;> simp [wist]
theorem sMount (x:Land n):
    blush i (strand (criterion n) (Mounting n false) (blush i x))=
      strand (criterion n) (Mounting n i) x := by
  classical
  cases i
  · rfl -- cond false on etc
  funext z
  unfold strand blush
  simp only [Function.comp_apply,wist,Bool.cond_true,map_sum,map_mul,map_prod]
  apply sum_congr rfl; intro y _
  congr 1
  · apply prod_congr rfl; intro j _
    unfold Mounting mounting kernel; simp only [Bool.cond_true,Bool.cond_false,Echo.conjugate,neg_neg,neg_mul]
  simp

@[simp] theorem wist_g (x y:ℂ):
    ‖wist i x-wist i y‖=‖x-y‖ := by
  cases i <;> simp [wist,← map_sub]

theorem organ (a:∀ i:Fin (wall n), ‖Cone.look n (b i)-Axon.R (ell n) (i.val:ℕ)‖ ≤err n):
    Angled n (opera h b) where
  norms B u f V W t := by
    have e:= (career h b a).norm_ B V W (skirt u f) (fun i=> by
      change ‖look n (clime u _)‖≤_
      rw [look_s,wist_n]; exact t i)
    intro i
    change ‖look n (clime u _)‖≤_
    rw [look_s,wist_n]; exact (e i).trans (mul_le_mul_of_nonneg_left (hi_mono _ (by decide)) (by linarith))
  error B u f V W t := by
    have e:= (career h b a).delta B V W (skirt u f) (fun i=> by
      change ‖look n (clime u (f i))‖≤_
      rw [look_s,wist_n]; exact t i)
    rw [← sMount u]
    rw [glen_s h] at e
    have w : array_ n (skirt u f) = blush u (array_ n f):= funext fun i=>look_s u _
    rw [w] at e
    intro i
    change ‖look n (clime u _) - wist u _‖ ≤ _
    rw [look_s,wist_g]; exact (e i).trans (by rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hi_mono n (by decide)) (invp n).le) (by linarith))
end
end Halo

end IntegerMultiplication
end Computability
end OAI
