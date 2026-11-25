import OAI.Computability.IntegerMultiplication.Scale.Season
import OAI.Computability.IntegerMultiplication.Garden.Burst

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Scale
open Param Net IntegerMultiplication.Fourier Staff IntegerMultiplication.Star
open Finset Real
variable {n:ℕ}

-- binary envelope arithmetic
noncomputable section
def hi (n:ℕ) (a:ℕ) : ℝ := 2^(a*P n)
@[simp] theorem hi0 (n): hi n 0=1 := by simp [hi]
theorem hi1 (n a): 1 ≤ hi n a := one_le_pow₀ (by norm_num)
theorem hi_mono (n) : Monotone (hi n) := fun x y i=> pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right (P n) i)
@[simp] theorem heightA (n a b):
    hi n a * hi n b=hi n (a+b) := by rw [hi,hi,hi, Nat.add_mul,pow_add]
theorem way(n):
    2 ≤ hi n 1 := calc
  _ = (2:ℝ)^(1:ℕ) := by simp
  _ ≤ _ := by unfold hi; have : 1≤P n:=budget_p _; gcongr; norm_num; omega
theorem invp(n):
    err n > 0 := by unfold err; positivity
theorem err1 (n) : err n≤1 := by rw [err]; apply div_le_self zero_le_one; exact hi1 n 3000

theorem stop (n):
    err n * hi n 3000=1 := by rw [err,hi]; field
theorem overhead (a n):
    (2:ℝ)*hi n a ≤ hi n (a+1) := calc
  _ ≤ hi n 1 * hi n a := mul_le_mul_of_nonneg_right (way n) (by linarith [hi1 n a])
  _ = _ := by simp [Nat.add_comm 1 a]
theorem add {a b} (n) (v : a≤b):
    hi n a+hi n b≤hi n (b+1) :=
  le_trans (by linarith [hi_mono n v] : _ ≤ 2*hi n b) (overhead ..)

theorem price (n):
    (2:ℝ)^W n=hi n 8192 := rfl
theorem fraction (n):
    (2:ℝ)^F n=hi n 4096 := rfl

theorem round_n (n) :
    3*drop_ (F n) ≤ err n := by
  unfold drop_ err F
  rw [one_div,inv_pow]
  -- clear denominators
  rw [← div_eq_mul_inv,div_le_div_iff₀ (by positivity) (by positivity),one_mul]
  have v:= budget_p n
  calc
    _ ≤ (2:ℝ)^((2:ℕ)+3000*P n) := by rw [pow_add]; nlinarith [show 0<(2:ℝ)^(3000*P n) by positivity]
    _ ≤ _ := by have t : 1≤P n:=budget_p _; exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem model (n):
    hi n 1000* (2:ℝ)^F n+2 < (2:ℝ)^W n := by
  rw [fraction,heightA,price]
  have A:= way n
  have R:= hi1 n (1000+4096)
  have L: hi n 1 ≤ hi n (1000+4096) := hi_mono _ (by decide)
  have i:=overhead (1000+4096) n
  calc
    _ ≤ hi n (1000+4096+1) := by linarith
    _ < _ := by
      unfold hi; have t:= budget_p n
      apply pow_lt_pow_right₀ (by norm_num)
      change (1000+4096+1)*budget n<8192*budget n
      omega

theorem digitRoom (n):
    P n ≤ W n := by unfold W; omega
theorem fixRoom n : Param.faces n ≤ W n + 1 :=
  ((Param.face_margin n).1.trans (Param.face_margin n).2).trans (Nat.le_trans (digitRoom _) (Nat.le_succ _))

-- envelope weight product
theorem weight1 (n) : 1≤Scale.weight n := one_le_pow₀ (by norm_num)
theorem weightPay (n) :
    Scale.weight n ^ lanes n ≤ hi n 24 := by
  unfold Scale.weight hi slope
  rw [← pow_mul]
  have p := wall_small n
  have a : lanes n ≤ budget n := Nat.le_self_pow (by decide) _
  have b : R n*lanes n ≤ budget n := by
    unfold R paramR budget
    rw [← pow_succ]
    exact pow_le_pow_right₀ (lanes_pos n) (by decide)
  change (2:ℝ)^_≤_
  apply pow_le_pow_right₀ (by norm_num)
  unfold ell P
  nlinarith

theorem weightPrice (n):
    Scale.weight n ≤ hi n 24 :=
  le_trans (le_self_pow₀ (weight1 n) (by have h:=lanes_pos n; omega)) (weightPay n)

theorem localRatio (n) (_i:Direction n):
    ((∏ _j:Fin n, (2:ℕ)) : ℕ)=2^n := by simp -- unused

-- exp unit ≤4 library? search
private theorem exp4 : Real.exp 1≤4 := by have h:=Real.exp_one_lt_d9; linarith

variable (h:Season n)
include h
theorem resonances (i: Direction n):
    ∀ a b:Spot (moduli n i),
    |mixTable (side n i) (D n i) (nhood (J n)) (K n) a b| ≤ (2:ℝ)^(4*(ell n+R n+1)) := by
  let d:=lanes n
  let s:= moduli n i
  let t:= side n i
  let D0:= D n i
  obtain ⟨Q,T,M,_,p,-⟩:= Fourier.param_est (s:=s) (t:=t) (d:=d) (H:=(H0:ℝ)) (by positivity)
    (by exact_mod_cast h.scatter) (h.budget_ i i.isLt) (h.upper i).2 (h.ratio i)
  intro a b
  have e:= Fourier.table_bound (l:=nhood (J n)) (K n) a b M
    (by
      apply mul_nonneg (by positivity) (Real.exp_pos _).le)
    (fun i=> (Q i).trans p)
  apply e.trans
  change (2:ℝ)*((2*D0+1)*Real.exp ((R n:ℕ):ℝ)) ≤ _
  have A : D0 ≤ (wall n)^2 := (Nat.div_le_self ..).trans (Nat.pow_le_pow_left
    ((h.upper i).1.trans (side_le n i).2) _)
  have z : (1:ℝ)≤ (2:ℝ)^ell n := one_le_pow₀ (by norm_num)
  have E : ((R n:ℕ):ℝ)=((R n:ℕ):ℝ)*1 := by ring
  have V : Real.exp ((R n:ℕ):ℝ) ≤ (2:ℝ)^(2*R n) := by
    rw [E,Real.exp_nat_mul, pow_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [exp4]) _
  have P : (D0:ℝ)≤ ((2:ℝ)^ell n)^2 := by exact_mod_cast A
  calc
    _ ≤ (2:ℝ)^3 * (((2:ℝ)^ell n)^2 * (2:ℝ)^(2*R n)) := by
      have B : (2* (2*(D0:ℝ)+1))≤ (2:ℝ)^(3:ℕ)*((2:ℝ)^ell n)^2 := by nlinarith
      nlinarith [mul_le_mul B V (Real.exp_pos ((R n:ℕ):ℝ)).le (by positivity)]
    _ ≤ _ := by
      rw [← pow_mul,← pow_add,← pow_add]
      apply pow_le_pow_right₀ (by norm_num)
      omega

noncomputable def wash (n:ℕ):ℝ := (2:ℝ)^(4*(ell n+R n+1))
omit h
theorem wash1 (n):1 ≤ wash n := one_le_pow₀ (by norm_num)
theorem wash_sq (n):wash n*wash n=Scale.weight n := by unfold wash Scale.weight slope;rw [← pow_add]; congr 1; omega
theorem wash_le (n):wash n ≤ hi n 24 :=
  le_trans (le_mul_of_one_le_right (by linarith [wash1 n] : 0≤wash n) (wash1 n)) (le_trans (le_of_eq (wash_sq n)) (weightPrice n))
theorem well (n):
    (wall n:ℝ) ≤ wash n := by
  unfold wash wall; push_cast
  apply pow_le_pow_right₀ (by norm_num)
  unfold ell; omega

include h
theorem careA (i:Direction n) :
    (2*L n+1:ℝ) ≤ wash n := by
  apply le_trans _ (well _)
  have i:= (h.grass i).1.trans_le ((h.upper i).1.trans (side_le n i).2)
  exact_mod_cast (show 2*L n+1 ≤wall n from i)

theorem careB (i:Direction n) :
    (2*(K n*J n)+1:ℝ) ≤ wash n := by
  apply le_trans _ (well _)
  have i:= (h.grass i).2.1.trans_le ((h.upper i).1.trans (side_le n i).2)
  exact_mod_cast (show 2*(K n*J n)+1 ≤wall n from i)
theorem careWeights (i:Direction n) (u:Bool)(a b:Spot (moduli n i)):
    ‖Garden.climate u (mixTable (side n i) (D n i) (nhood (J n)) (K n) a b) (moduli n i)‖ ≤ wash n := by
  have M : (1:ℝ) ≤ moduli n i := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (moduli n i))
  cases u with
  | false=>simpa only [wash,Garden.climate,Bool.cond_false,Complex.norm_real,Real.norm_eq_abs] using (resonances h i a b)
  | true=>
    unfold Garden.climate
    rw [Bool.cond_true,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_nonneg (show 0 ≤ (moduli n i:ℝ) by positivity)]
    exact (div_le_self (abs_nonneg _) M).trans (resonances h i a b)
end
end Scale

end IntegerMultiplication
end Computability
end OAI
