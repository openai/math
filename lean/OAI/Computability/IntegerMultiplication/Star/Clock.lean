import OAI.Computability.IntegerMultiplication.Star.Arc
import OAI.Computability.IntegerMultiplication.Fourier.Window

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Star
open scoped BigOperators Real
open Complex Finset
noncomputable section
def character (x:ℝ):ℂ := Complex.exp ((x:ℂ)*Complex.I)
theorem char_norm (x):‖character x‖=1 := by simp [character,Complex.norm_exp]
theorem char_add (x y):character (x+y)=character x*character y := by simp [character,add_mul, Complex.exp_add]
theorem char_pow (x) (k:ℕ) : character x ^ k=character (k*x) := by
  induction k with
  | zero=> simp [character]
  | succ k ih=> rw [pow_succ,Nat.cast_add_one,add_mul,char_add,one_mul,ih]
theorem angle_close {x y:ℝ} (h: |x-y|≤1) :
    ‖character x-character y‖ ≤ 2*|x-y| := by
  rw [show character x-character y=character y*(character (x-y)-1) from by rw [mul_sub,← char_add]; simp]
  have q : ‖(((x-y:ℝ):ℂ)*Complex.I)‖=|x-y| := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  rw [norm_mul,char_norm,one_mul,character]
  simpa only [q] using Complex.norm_exp_sub_one_le (x:=((x-y:ℝ):ℂ)*Complex.I) (by rw [q]; exact h)

def emotor (x:ℝ) (n:ℕ):ℂ :=
  ∑ j:Fin n, ((x:ℂ)*Complex.I)^(j.val)/Nat.factorial j.val

theorem arch {x:ℝ} (h:|x|≤1/2) (n:ℕ) (p:0<n) :
    ‖emotor x n - character x‖ ≤ drop_ n * 2 := by
  let z := ((x:ℂ)*Complex.I)
  have v : ‖z‖=|x| := by simp [z,Complex.norm_real,Real.norm_eq_abs]
  have t := Complex.exp_bound (x:=z) (n:=n) (by rw [v]; linarith) p
  unfold emotor character
  let f (j:ℕ) := z^j / Nat.factorial j
  have q : (∑ j:Fin n,f j.val) = ∑ j∈Finset.range n,f j := Fin.sum_univ_eq_sum_range f n
  change ‖∑ j:Fin n,f j.val - Complex.exp z‖ ≤ _
  rw [q,norm_sub_rev]
  refine t.trans ?_
  have u : 1≤(Nat.factorial n:ℝ) := by exact_mod_cast Nat.factorial_pos _
  have e : 1≤(n:ℝ) := by exact_mod_cast p
  rw [v]
  apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg x) h n) _ (by positivity) (by exact (drop_p _).le) -- x_?
  rw [← div_eq_mul_inv, div_le_iff₀ (by nlinarith : (0:ℝ)<Nat.factorial n*n)]
  push_cast
  nlinarith

def inclination (n:ℕ) (x:ℝ) :=
  polestar n*x/16
/-- rational-valued (pair rational) polynomial approximant. -/
def needle (n:ℕ) (x:ℝ) : ℂ :=
  (emotor (inclination n x) n)^32

private theorem motor {n} (h:4≤n) {x:ℝ} (t:|x|≤1) :
    |inclination n x| ≤ 1/2 ∧
    |inclination n x - π*x/16| ≤ drop_ n := by
  unfold inclination
  rw [abs_div, abs_mul,abs_of_pos (by norm_num : (0:ℝ)<16), ← sub_div,← sub_mul,
    abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<16)]
  have a := mul_le_mul (star_le h) t (abs_nonneg _) (by norm_num : (0:ℝ)≤5)
  have b := mul_le_mul (star_est n) t (abs_nonneg _) (mul_nonneg (by norm_num) (drop_p _).le)
  constructor <;> linarith
private theorem gap {n} (h:4≤n) {x:ℝ} (t:|x|≤1) :
    let u := inclination n x
    let v := character (π*x/16)
    ‖emotor u n-v‖ ≤ 4*drop_ n ∧ ‖emotor u n‖ ≤ 2 := by
  obtain ⟨i,e⟩:= motor h t
  have p := arch i n (by omega)
  have w := angle_close (le_trans e (drop1 _))
  let u := inclination n x
  let v := character (π*x/16)
  let a := emotor u n
  let b := character u
  have R := norm_add_le (a-b) (b-v)
  rw [show (a-b)+(b-v)=a-v by ring] at R
  have q := drop_le (m:=2) (n:=n) (by omega)
  change drop_ n ≤ _ at q
  have Q : 4*drop_ n≤1 := le_trans (mul_le_mul_of_nonneg_left q (by norm_num)) (by norm_num [drop_])
  change ‖a-v‖ ≤ 4*drop_ n ∧ ‖a‖ ≤ _
  change ‖a-b‖≤_ at p
  change ‖b-v‖≤_ at w
  constructor
  · linarith
  have m := norm_add_le (a-b) b
  rw [sub_add_cancel] at m
  have y : ‖b‖=1 := char_norm _
  linarith

-- polynomial power Lipschitz over complex unit neighborhood
theorem tower {x y:ℂ} (h: ‖x‖ ≤2) (w: ‖y‖≤1) (k : ℕ) :
    ‖x^k-y^k‖ ≤ 2^k * ‖x-y‖ := by
  induction k with
  | zero=> simp
  | succ k ih=>
    rw [pow_succ x,pow_succ y,
      show x^k*x-y^k*y=x^k*(x-y)+(x^k-y^k)*y by ring]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul,norm_pow]
    have q := pow_le_pow_left₀ (norm_nonneg _) h k
    rw [pow_succ]
    have b := mul_le_mul_of_nonneg_left w (norm_nonneg (x^k-y^k))
    have m := mul_le_mul_of_nonneg_right q (norm_nonneg (x-y))
    nlinarith

theorem tip {n} (h:4≤n) {x:ℝ} (t:|x|≤1) :
    ‖needle n x-Fourier.cis x‖ ≤ (2:ℝ)^34*drop_ n := by
  obtain ⟨i,e⟩:= gap h t
  have q:= tower (x:=emotor (inclination n x) n) (y:=character (π*x/16)) e
    (char_norm _ |>.le) 32
  rw [char_pow] at q
  have g : character (((32:ℕ):ℝ)*(π*x/16))=Fourier.cis x := by
    unfold character Fourier.cis
    congr 2
    push_cast; ring
  rw [g] at q
  apply q.trans
  calc
    _ ≤ (2:ℝ)^32 * (4*drop_ n) := by gcongr
    _ = _ := by ring

end
end Star

end IntegerMultiplication
end Computability
end OAI
