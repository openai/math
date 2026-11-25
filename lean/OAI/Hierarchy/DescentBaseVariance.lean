import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace OAI
/-! # Collision estimates for the exceptional bases in the reset -/

namespace Hierarchy.DescentBaseVariance

open scoped Classical BigOperators
noncomputable section
variable {I P Q : Type*} [Fintype I] [Fintype P] [Fintype Q]
variable [Nonempty P] [Nonempty Q]

/-- The uniform average over the entire layout ensemble. -/
def average (f : P → ℝ) : ℝ := (∑ p, f p) / Fintype.card P

/-- The normalized mass of a single base after choosing a layout. -/
def load (f : I → Q) (x : I → ℝ) (j : Q) : ℝ := ∑ i, if j=f i then x i else 0

def mean (x : I → ℝ) (bins : Type*) [Fintype bins] : ℝ := (∑ i,x i) / Fintype.card bins

def variance (f : I → Q) (x : I → ℝ) := ∑ j, (load f x j - mean x Q)^2

def surplus (f : I → Q) (x : I → ℝ) := (∑ j,(load f x j)^2) - ∑ i,x i^2

/-- The normalized number of ensemble members sending two specified indices
to the same base. -/
def collision (layout : P → I → Q) (i j : I) : ℝ :=
  ((Finset.univ.filter (fun p=>layout p i=layout p j)).card : ℝ) / Fintype.card P

def PairBound (layout : P → I → Q) : Prop :=
  ∀ i j, i≠j → collision layout i j ≤ 1 / Fintype.card Q

omit [Nonempty P] in
theorem average_sum {A : Type*} [Fintype A] (g : P → A → ℝ) :
    average (fun p => ∑ j,g p j) = ∑ j,average (fun p=>g p j) := by
  unfold average
  rw [Finset.sum_comm,Finset.sum_div]

theorem average_const (c : ℝ) : average (fun _ : P => c)=c := by
  have pos : (0:ℝ)<Fintype.card P := by exact_mod_cast Fintype.card_pos
  simp [average,nsmul_eq_mul,mul_div_cancel_left₀ _ pos.ne']

theorem average_sub_const (g : P → ℝ) (c : ℝ) :
    average (fun p=>g p-c)=average g-c := by
  have value := average_const (P:=P) c
  unfold average at *
  rw [Finset.sum_sub_distrib,sub_div,value]

omit [Nonempty P] in
theorem average_mul (k : ℝ) (g : P → ℝ) : average (fun p=>k*g p)=k*average g := by
  unfold average
  rw [←Finset.mul_sum,mul_div_assoc]

omit [Nonempty Q] in
theorem sum_load (f : I → Q) (x : I → ℝ) : (∑ j,load f x j) = ∑ i,x i := by
  unfold load
  rw [Finset.sum_comm]
  simp

theorem variance_eq (f : I → Q) (x : I → ℝ) :
    variance f x = (∑ j,(load f x j)^2) - (∑ i,x i)^2 / Fintype.card Q := by
  have qpos : (0:ℝ)<Fintype.card Q := by exact_mod_cast Fintype.card_pos
  have split (a t : ℝ) : (a-t)^2 = a^2-a*(2*t)+t^2 := by ring
  simp only [variance,split,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,sum_load,mean]
  field_simp
 ; ring

omit [Nonempty Q] in
theorem square_load_sum (f : I → Q) (x : I → ℝ) :
    (∑ b,(load f x b)^2) = ∑ i,∑ j,if f i=f j then x i*x j else 0 := by
  unfold load
  simp_rw [pow_two,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [ite_mul, mul_ite, eq_comm]

omit [Fintype I] [Fintype Q] [Nonempty P] [Nonempty Q] in
private theorem pair_average (layout : P → I → Q) (i j : I) (w : ℝ) :
    average (fun p=>if layout p i=layout p j then w else 0) = collision layout i j * w := by
  unfold average collision
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

/-- Expanding the squared loads counts every ordered pair by its actual
collision frequency. No independence between different pairs is needed. -/
theorem square_average_le (layout : P → I → Q) (pairs : PairBound layout) (x : I → ℝ)
    (positive : ∀ i,0≤x i) :
    average (fun p=>∑ b,(load (layout p) x b)^2) ≤
      (∑ i,x i^2) + (∑ i,x i)^2 / Fintype.card Q := by
  have term (i j : I) :
      average (fun p=>if layout p i=layout p j then x i*x j else 0) ≤
        (if i=j then x i^2 else 0) + x i*x j / Fintype.card Q := by
    by_cases same : i=j
    · subst j
      simp only [ite_true,average_const,pow_two]
      have : 0 ≤ x i*x i/(Fintype.card Q:ℝ) := div_nonneg (mul_nonneg (positive i) (positive i)) (by positivity)
      linarith
    · rw [pair_average,ite_eq_right same,zero_add]
      have step := mul_le_mul_of_nonneg_right (pairs i j same) (mul_nonneg (positive i) (positive j))
      simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul] using step
  calc
    _ = ∑ i,∑ j,average (fun p=>if layout p i=layout p j then x i*x j else 0) := by
      simp_rw [square_load_sum,average_sum]
    _ ≤ ∑ i,∑ j,((if i=j then x i^2 else 0) + x i*x j / Fintype.card Q) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => term i j
    _ = _ := by
      simp [Finset.sum_add_distrib,←Finset.sum_div,←Finset.mul_sum,←Finset.sum_mul,pow_two]

theorem average_deviations (layout : P → I → Q) (pairs : PairBound layout) (x : I → ℝ)
    (positive : ∀ i,0≤x i) :
    average (fun p=>variance (layout p) x) ≤ ∑ i,x i^2 ∧
    average (fun p=>surplus (layout p) x) ≤ (∑ i,x i)^2 / Fintype.card Q := by
  have bound := square_average_le layout pairs x positive
  simp_rw [variance_eq,surplus,average_sub_const]
  constructor <;> linarith

theorem sum_squares_le {M : ℝ} (x : I → ℝ) (pos : ∀ i,0≤x i) (small : ∀ i,x i≤M) :
    (∑ i,x i^2) ≤ M * ∑ i,x i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>by simpa [pow_two] using mul_le_mul_of_nonneg_right (small i) (pos i)

/-- Each overflowing reservation contributes at least one unit after
multiplication by the square of the reciprocal slack. -/
theorem overflow_charge {a m k : ℝ} (hk : 0<k) (overflow : m+1/k<a) :
    1 ≤ k^2*(a-m)^2 := by
  have above : 1/k<a-m := by linarith
  have one : 1<(a-m)*k := (div_lt_iff₀ hk).mp above
  rw [←mul_pow]
  nlinarith [sq_nonneg (k*(a-m)-1)]

/-- The weighted contribution from all neighbor-pair estimates has the
paper's order K² X /(F² B), with pair-specific numbers of bins. -/
theorem capacity_budget {A : Type*} [Fintype A] (bins : A → Type*) [∀ a,Fintype (bins a)]
    [∀ a,Nonempty (bins a)] (layout : ∀ a,P → I → bins a) (pairs : ∀ a,PairBound (layout a))
    (x : A → I → ℝ) {F B K X : ℝ} (hF : 0<F) (hB : 0<B)
    (pos : ∀ a i, 0≤x a i) (small : ∀ a i,x a i≤1/F)
    (quantity : (∑ a,∑ i,x a i) ≤ X/(F*B)) :
    average (fun p=>∑ a,K^2*variance (layout a p) (x a)) ≤ K^2*X/(F^2*B) := by
  rw [average_sum]
  simp_rw [average_mul]
  have each (a : A) := (average_deviations (layout a) (pairs a) (x a) (pos a)).1.trans
    (sum_squares_le (x a) (pos a) (small a))
  calc
    _ ≤ ∑ a,K^2*((1/F)*∑ i,x a i) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (each a) (sq_nonneg _)
    _ = K^2*((1/F)*(∑ a,∑ i,x a i)) := by simp only [Finset.mul_sum]
    _ ≤ K^2*((1/F)*(X/(F*B))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left quantity (by positivity)) (sq_nonneg _)
    _ = _ := by field_simp

/-- At least one of the candidate layouts attains at most its uniform
average; it can be selected for the current summand. -/
theorem exists_layout_le_average (cost : P → ℝ) : ∃ p, cost p≤average cost := by
  by_contra! greater
  have h := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty : (Finset.univ : Finset P).Nonempty)
    fun p _ => greater p
  have pos : (0:ℝ)<Fintype.card P := by exact_mod_cast Fintype.card_pos
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  have identity : (Fintype.card P:ℝ)*average cost = ∑ p,cost p := by
    unfold average
    field_simp
  linarith

end
end Hierarchy.DescentBaseVariance

end OAI
