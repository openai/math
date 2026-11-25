import OAI.Computability.IntegerMultiplication.Grid.Bond
import OAI.Computability.IntegerMultiplication.Axon.Tuple

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Grid
open Net Net.Walsh Net.Tensor Matrix Finset
variable {I J K R : Type} [Fintype I] [DecidableEq I]
variable {k l : ℕ}
noncomputable section
def toC : Cell→+*ℂ where
  toFun x := x.re + Complex.I*(x.im:ℤ)
  map_one' := by simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_zero' := by simp
  map_add' x y := by simp; ring
  map_mul' x y := by
    simp
    have q := Complex.I_mul_I
    linear_combination -(x.im:ℂ)*(y.im:ℂ)*q
-- need noncomputable
def meaning (p:ℕ) (k : ℕ) (x : Dusk.Grain k) : ℂ :=
  toC (aspect x)/(2:ℂ)^p

def inside (s : ℝ) (x : Cell) : Prop :=
  |(x.re:ℝ)|≤ s ∧ |(x.im:ℝ)|≤ s
theorem into (x:Cell) : inside ‖toC x‖ x := by
  suffices e : (toC x).re=(x.re:ℝ) ∧ (toC x).im=x.im by
    unfold inside; rw [← e.1,← e.2]; exact ⟨Complex.abs_re_le_norm _,Complex.abs_im_le_norm _⟩
  simp [toC]
theorem stood (x:Cell) (s t:ℝ) (v:inside s x) (h:s≤ t): inside t x := ⟨v.1.trans h,v.2.trans h⟩
theorem short {s:ℝ} (x:Cell) (h:inside s x) (g:s < (2:ℝ)^k) :
    focus k x := by
  change |x.re| < ((2:ℕ):ℤ)^k ∧ |x.im| < ((2:ℕ):ℤ)^k
  constructor
  · exact_mod_cast (h.1.trans_lt g)
  exact_mod_cast (h.2.trans_lt g)

-- Walsh-H application via retinal. may leverage all input upper values scaled by 2^p, no overflow assuming sum value <2^k. Hom argument via patch
theorem imageLaw [CommRing R] (q : Cell→+*R) (i:Fin l) (x : Axon.Scr I l→Cell) :
    q ∘ (Axon.zoom i Walsh.F *ᵥ x) = Axon.zoom i Walsh.F *ᵥ (q ∘ x) := by
  funext v
  rw [Function.comp_apply, Axon.retinal _,Axon.retinal _]
  simp only [Tensor.app,map_sum,map_mul,map_prod]
  have s (x y : B) : q (Walsh.F x y) = Walsh.F x y := by
    unfold Walsh.F; dsimp only [of_apply]; split <;> simp
  simp only [s,Function.comp_def]

theorem law_norm (i:Fin l) (x : Axon.Scr I l → ℂ) (v:ℝ) (h:∀ i,‖x i‖≤ v) (z : Axon.Scr I l) :
    ‖(Axon.zoom i F *ᵥ x) z‖ ≤ 2^(Fintype.card I)*v := by
  classical
  rw [Axon.retinal _]
  unfold Tensor.mat
  let m (q : Walsh.Addr I) := (∏ j:I,(Walsh.F (Axon.who i z j) (q j):ℂ))*x (Axon.replaceAt i z q)
  change ‖∑ q,m q‖≤_
  have e (q) : ‖m q‖ ≤ v := by
    unfold m; rw [norm_mul,norm_prod] -- v rw? invalid rewrite def
    have z (x y:B) : ‖(F x y:ℂ)‖=1 := by unfold F; dsimp only [of_apply]; split <;> simp
    simp_rw [z]
    simp; exact h _
  calc
   _ ≤ ∑ q : Walsh.Addr I, v := norm_sum_le_of_le _ (fun i _=> e i)
   _ = _ := by simp [Walsh.Addr, Tensor.Vec, Walsh.B]

theorem law_sub (i:Fin l) (x y: Axon.Scr I l→ℂ) :
    Axon.zoom i F *ᵥ x - Axon.zoom i F *ᵥ y=Axon.zoom i F *ᵥ (x-y) :=
  (Matrix.mulVec_sub ..).symm

theorem realH (p k:ℕ) (i : Fin l) (x : Axon.Scr I l→Dusk.Grain k)
    (v:ℝ) (h : ∀ i,‖meaning p k (x i)‖≤ v)
    (d : (2:ℝ)^p*2^(Fintype.card I)*v < 2^k) :
    meaning p k ∘ (Axon.zoom i F *ᵥ x) = Axon.zoom i F *ᵥ (meaning p k ∘ x) := by
  let s := aspect ∘ x
  let C := toC ∘ s
  have e (i): ‖C i‖ ≤ (2:ℝ)^p*v := by
    have g := h i; unfold meaning at g
    rw [norm_div,norm_pow,show ‖(2:ℂ)‖=(2:ℝ) by norm_num] at g
    change ‖C i‖/(2:ℝ)^p≤ v at g
    rw [div_le_iff₀ (by positivity),mul_comm] at g
    exact g
  let y := Axon.zoom i F *ᵥ s
  have sizeY q :
      ‖toC (y q)‖ < (2:ℝ)^k := by
    change ‖(toC ∘ y) q‖ < _
    unfold y; rw [imageLaw]
    exact (law_norm i C _ e q).trans_lt (by nlinarith)
  have ret : x=wrapMap k ∘ s := funext fun t=> (back (x t)).symm
  have scaled :
      meaning p k ∘ x= (((2:ℂ)^p)⁻¹ : ℂ) • (toC ∘ s) := by
    funext t; simp [s,meaning,div_eq_mul_inv,mul_comm]
  rw [scaled,mulVec_smul]
  funext z
  nth_rw 1 [ret]
  rw [← imageLaw]
  change toC (aspect (wrapMap k (y z)))/ _= (((2:ℂ)^p)⁻¹)*(Axon.zoom i F *ᵥ (toC ∘ s)) z
  have a : focus k (y z) := short _ (into _) (sizeY z)
  rw [← imageLaw,recovers _ a]; exact div_eq_mul_inv .. |>.trans (mul_comm ..)
end
end Grid

end IntegerMultiplication
end Computability
end OAI
