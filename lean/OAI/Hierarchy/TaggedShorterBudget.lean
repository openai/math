import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI
/-! # Active transport and installed-slot estimates for shorter tagged calls -/

namespace Hierarchy.TaggedShorterBudget

noncomputable section

open Real Finset

/-- The positive-scale branch of the protocol capacity charge. -/
def capacity (p q Q t l : ℝ) : ℝ := t ^ p * max (l ^ (-q)) (l ^ (-Q))

private theorem capacity_nonneg {t l : ℝ} (ht : 0 ≤ t) (hl : 0 ≤ l) (p q Q : ℝ) :
    0 ≤ capacity p q Q t l :=
  mul_nonneg (rpow_nonneg ht _) ((rpow_nonneg hl _).trans (le_max_left _ _))

/-- Interpolation between the two length prices. The branch of the maximum
depends on which side of one the length charge lies. -/
theorem interpolate {p q Q t l y e θ : ℝ} (ht : 0<t) (ht1 : t≤1)
    (hl : 0<l) (hy : 0≤y) (hθ : 0<θ) (he : p*θ≤e)
    (hq : q≤1/θ-1) (hQ : 1/θ-1≤Q) :
    t^e*y^(1-θ) ≤ (capacity p q Q t l)^θ*(l*y)^(1-θ) := by
  let r := 1/θ-1
  have mid : l^(-r) ≤ max (l^(-q)) (l^(-Q)) := by
    rcases le_total 1 l with h|h
    · exact (rpow_le_rpow_of_exponent_le h (neg_le_neg hq)).trans (le_max_left _ _)
    · exact (rpow_le_rpow_of_exponent_ge hl h (neg_le_neg hQ)).trans (le_max_right _ _)
  have cap : (t^p*l^(-r))^θ ≤ (capacity p q Q t l)^θ :=
    rpow_le_rpow (mul_nonneg (rpow_nonneg ht.le _) (rpow_nonneg hl.le _))
      (mul_le_mul_of_nonneg_left mid (rpow_nonneg ht.le _)) hθ.le
  have cancel : -r*θ+(1-θ)=0 := by dsimp [r]; field_simp [hθ.ne']; ring
  calc
    _ ≤ t^(p*θ)*y^(1-θ) := mul_le_mul_of_nonneg_right
      (rpow_le_rpow_of_exponent_ge ht ht1 he) (rpow_nonneg hy _)
    _ = (t^p*l^(-r))^θ*(l*y)^(1-θ) := by
      rw [Real.mul_rpow (rpow_nonneg ht.le _) (rpow_nonneg hl.le _),
        Real.mul_rpow hl.le hy, ←rpow_mul ht.le, ←rpow_mul hl.le]
      calc _ = t^(p*θ)*(l^(-r*θ+(1-θ))*y^(1-θ)) := by rw [cancel,rpow_zero,one_mul]
           _ = _ := by rw [rpow_add hl]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right cap (rpow_nonneg (mul_nonneg hl.le hy) _)

/-- The budget before dyadic rounding. A wide link pays for its normalized
width in whole transports, a narrow link pays the interpolated price. -/
def weight (t y e θ : ℝ) := t^e*(if y≤1 then y^(1-θ) else y)

/-- Scaling by the common lower exponent δ makes each individual charge pay
for its corresponding unsplit transport weight. -/
theorem scaled_weight {p q Q σ L t l y e θ δ : ℝ} (ht : 0<t) (ht1 : t≤1)
    (hl : 0<l) (hy : 0≤y) (hL : 1≤L) (hθ : 0<θ) (hθ1 : θ≤1) (hδ : δ≤θ)
    (he : p*θ≤e) (hq : q≤1/θ-1) (hQ : 1/θ-1≤Q)
    (hσ : σ≤e) (length : L*t^σ≤l) :
    L^δ * weight t y e θ ≤ l*y + L*capacity p q Q t l := by
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hc := capacity_nonneg ht.le hl.le p q Q
  let D := l*y + L*capacity p q Q t l
  have hD : 0 ≤ D := add_nonneg (mul_nonneg hl.le hy) (mul_nonneg hL0.le hc)
  by_cases h : y≤1
  · rw [weight,ite_eq_left h]
    have hw := interpolate ht ht1 hl hy hθ he hq hQ
    calc
      _ ≤ L^θ*((capacity p q Q t l)^θ*(l*y)^(1-θ)) :=
        mul_le_mul (rpow_le_rpow_of_exponent_le hL hδ) hw
          (mul_nonneg (rpow_nonneg ht.le _) (rpow_nonneg hy _)) (rpow_nonneg hL0.le _)
      _ = (L*capacity p q Q t l)^θ*(l*y)^(1-θ) := by rw [Real.mul_rpow hL0.le hc]; ring
      _ ≤ D^θ*D^(1-θ) := mul_le_mul
        (rpow_le_rpow (mul_nonneg hL0.le hc) (le_add_of_nonneg_left (mul_nonneg hl.le hy)) hθ.le)
        (rpow_le_rpow (mul_nonneg hl.le hy) (le_add_of_nonneg_right (mul_nonneg hL0.le hc))
          (sub_nonneg.mpr hθ1)) (rpow_nonneg (mul_nonneg hl.le hy) _) (rpow_nonneg hD _)
      _ = D := by rw [←rpow_add' hD (show θ+(1-θ) ≠ 0 by linarith),show θ+(1-θ)=1 by ring,rpow_one]
  · rw [weight,ite_eq_right h]
    have Lδ : L^δ≤L := by simpa using rpow_le_rpow_of_exponent_le hL (hδ.trans hθ1)
    have small := rpow_le_rpow_of_exponent_ge ht ht1 hσ
    calc
      _ = (L^δ*t^e)*y := by ring
      _ ≤ l*y := mul_le_mul_of_nonneg_right
        ((mul_le_mul Lδ small (rpow_nonneg ht.le _) hL0.le).trans length) hy
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hL0.le hc)

/-- One width menu for all links, with the smallest installed width at index m. -/
def dyadic (i : ℕ) : ℝ := (1/2:ℝ)^i

theorem dyadic_pos (i : ℕ) : 0<dyadic i := pow_pos (by norm_num) _

theorem dyadic_le_one (i : ℕ) : dyadic i≤1 := pow_le_one₀ (by norm_num) (by norm_num)

theorem dyadic_le_half {i : ℕ} (hi : 0 < i) : dyadic i≤1/2 := by
  cases i with
  | zero => omega
  | succ j =>
    change (1/2:ℝ)^(j+1)≤1/2
    rw [pow_succ]
    have bound := dyadic_le_one j
    unfold dyadic at bound
    linarith

def bucket : ℕ → ℝ → ℕ
  | 0, _ => 0
  | m+1, y => if y≤dyadic (m+1) then m+1 else bucket m y

theorem bucket_spec (m : ℕ) {y : ℝ} (hy : y≤1) :
    bucket m y ≤ m ∧ y≤dyadic (bucket m y) ∧
    dyadic (bucket m y)≤max (2*y) (dyadic m) := by
  induction m with
  | zero => exact ⟨le_rfl,by simpa [bucket,dyadic] using hy,le_max_right _ _⟩
  | succ m ih =>
    by_cases h : y≤dyadic (m+1)
    · simp only [bucket,ite_eq_left h]
      exact ⟨le_rfl,h,le_max_right _ _⟩
    · simp only [bucket,ite_eq_right h]
      have d : dyadic m ≤ 2*y := by
        have := lt_of_not_ge h
        simp only [dyadic,pow_succ] at this ⊢
        linarith
      exact ⟨ih.1.trans m.le_succ,ih.2.1,ih.2.2.trans
        ((max_le le_rfl d).trans (le_max_left _ _))⟩

/-- A zero-width link uses no transport. A wide link uses one slot per unit
transport and pads its final slot. -/
def copies (y : ℝ) : ℕ := ⌈y⌉₊
def widthIndex (m : ℕ) (y : ℝ) : ℕ := if y≤1 then bucket m y else 0

theorem widthIndex_spec (m : ℕ) {y : ℝ} :
    widthIndex m y≤m ∧ min y 1≤dyadic (widthIndex m y) := by
  by_cases h : y≤1
  · simpa only [widthIndex,ite_eq_left h,min_eq_left h] using
      And.intro (bucket_spec m h).1 (bucket_spec m h).2.1
  · simp [widthIndex,h,dyadic,min_eq_right (le_of_not_ge h)]

theorem rounded_link {t y e θ : ℝ} (ht : 0<t) (ht1 : t≤1) (hy : 0≤y)
    (he : 0≤e) (hθ : 0≤θ) (hθ1 : θ≤1) (m : ℕ) :
    (copies y:ℝ)*(t^e*dyadic (widthIndex m y)^(1-θ)) ≤
      2*weight t y e θ + dyadic m^(1-θ) := by
  have hs := sub_nonneg.mpr hθ1
  have dt := rpow_le_one ht.le ht1 he
  have dt0 := rpow_nonneg ht.le e
  have df := rpow_nonneg (dyadic_pos m).le (1-θ)
  by_cases h : y≤1
  · have units : copies y ≤ 1 := Nat.ceil_le.mpr (by simpa using h)
    have units' : (copies y:ℝ)≤1 := by exact_mod_cast units
    apply (mul_le_mul_of_nonneg_right units' (mul_nonneg dt0 (rpow_nonneg (dyadic_pos _).le _))).trans
    simp only [widthIndex,weight,ite_eq_left h,one_mul]
    have bound := (bucket_spec m h).2.2
    rcases le_total (dyadic m) (2*y) with h₂|h₂
    · rw [max_eq_left h₂] at bound
      have step := rpow_le_rpow (dyadic_pos _).le bound hs
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hy] at step
      have two : (2:ℝ)^(1-θ)≤2 := by
        simpa using rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (show 1-θ≤1 by linarith)
      have b := mul_le_mul_of_nonneg_right two (rpow_nonneg hy (1-θ))
      nlinarith [mul_le_mul_of_nonneg_left (step.trans b) dt0]
    · rw [max_eq_right h₂] at bound
      have step := mul_le_mul dt (rpow_le_rpow (dyadic_pos _).le bound hs)
        (rpow_nonneg (dyadic_pos _).le _) zero_le_one
      nlinarith [mul_nonneg dt0 (rpow_nonneg hy (1-θ))]
  · simp only [copies,widthIndex,weight,ite_eq_right h,dyadic,pow_zero,one_rpow,mul_one]
    unfold dyadic at df
    have ceil := Nat.ceil_lt_add_one hy
    have two : (⌈y⌉₊ : ℝ) ≤ 2*y := by linarith
    nlinarith [mul_le_mul_of_nonneg_right two dt0]

/-- A protocol below the width floor produces at most one extra floor-weight
per link. The choice of depth follows the choice of protocol. -/
theorem exists_floor {η ξ C : ℝ} (hη : 0<η) (hξ : 0<ξ) (hC : 0≤C) :
    ∃ m : ℕ,C*dyadic m^η≤ξ := by
  let r := (1/2:ℝ)^η
  have hr : r<1 := rpow_lt_one (by norm_num) (by norm_num) hη
  obtain ⟨m,hm⟩ := exists_pow_lt_of_lt_one (show 0<ξ/(C+1) by positivity) hr
  have pos : 0<r^m := pow_pos (rpow_pos_of_pos (by norm_num) _) _
  have h := (lt_div_iff₀ (show 0<C+1 by positivity)).mp hm
  refine ⟨m,?_⟩
  change C*((1/2:ℝ)^m)^η ≤ ξ
  rw [←rpow_pow_comm (by norm_num)]
  change C*r^m ≤ ξ
  nlinarith

/-- The constants in the price estimate work for every positive-scale link
in a summand. Summing the pointwise interpolation is sufficient. -/
theorem rounded_total {ι : Type*} (links : Finset ι) (scale : ι→ℕ) (y l : ι→ℝ)
    {p q Q σ L e θ δ η ξ C n : ℝ} {m : ℕ}
    (hL : 1≤L) (hθ : 0<θ) (hθ1 : θ≤1) (hδ : δ≤θ) (hη : η≤1-θ)
    (he : p*θ≤e) (hq : q≤1/θ-1) (hQ : 1/θ-1≤Q)
    (hσ : σ≤e) (he0 : 0≤e) (_hξ : 0≤ξ) (hn : 0≤n) (hC : 0≤C)
    (large : 11≤ξ*L^δ) (floorPrice : C*dyadic m^η ≤ ξ)
    (number : (links.card:ℝ)≤C*n)
    (length : ∀ i∈links,0<l i ∧ 0≤y i ∧ L*dyadic (scale i)^σ≤l i)
    (budget : ∑ i∈links,(l i*y i+L*capacity p q Q (dyadic (scale i)) (l i))≤11*n) :
    ∑ i∈links,(copies (y i):ℝ)*(dyadic (scale i)^e*dyadic (widthIndex m (y i))^(1-θ))
      ≤ 3*ξ*n := by
  have raw : (∑ i∈links,weight (dyadic (scale i)) (y i) e θ) ≤ ξ*n := by
    apply le_of_mul_le_mul_left (a := L^δ) _ (rpow_pos_of_pos (by linarith) _)
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ i∈links,(l i*y i+L*capacity p q Q (dyadic (scale i)) (l i)) :=
        sum_le_sum fun i hi => scaled_weight (dyadic_pos _) (dyadic_le_one _)
          (length i hi).1 (length i hi).2.1 hL hθ hθ1 hδ he hq hQ hσ (length i hi).2.2
      _ ≤ 11*n := budget
      _ ≤ L^δ*(ξ*n) := by nlinarith [mul_le_mul_of_nonneg_right large hn]
  have floorAt := rpow_le_rpow_of_exponent_ge (dyadic_pos m) (dyadic_le_one m) hη
  have pad := mul_le_mul number floorAt (rpow_nonneg (dyadic_pos _).le _) (mul_nonneg hC hn)
  calc
    _ ≤ ∑ i∈links,(2*weight (dyadic (scale i)) (y i) e θ+dyadic m^(1-θ)) :=
      sum_le_sum fun i hi => rounded_link (dyadic_pos _) (dyadic_le_one _) (length i hi).2.1
        he0 hθ.le hθ1 m
    _ = 2*(∑ i∈links,weight (dyadic (scale i)) (y i) e θ)+links.card*dyadic m^(1-θ) := by
      rw [sum_add_distrib,Finset.mul_sum]; simp
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right floorPrice hn]

/-- The number of transports of an individual dyadic type, including splitting
widths above one, is counted before pooling the physical batches. -/
def active {ι : Type*} (links : Finset ι) (scale : ι→ℕ) (y : ι→ℝ) (m j k : ℕ) : ℕ :=
  ∑ i∈links, if scale i=j ∧ widthIndex m (y i)=k then copies (y i) else 0

/-- The per-type fraction c_* and the uniform positive lower bound used to buy
whole modules. -/
def fraction (ξ e f : ℝ) (j k : ℕ) := 3*ξ/(dyadic j^e*dyadic k^f)

theorem fraction_pos {ξ : ℝ} (hξ : 0<ξ) (e f : ℝ) (j k : ℕ) :
    0<fraction ξ e f j k :=
  div_pos (by positivity) (mul_pos (rpow_pos_of_pos (dyadic_pos _) _) (rpow_pos_of_pos (dyadic_pos _) _))

theorem fraction_lower {ξ e f : ℝ} (hξ : 0≤ξ) (he : 0≤e) (hf : 0≤f) (j k : ℕ) :
    3*ξ ≤ fraction ξ e f j k := by
  apply (le_div_iff₀ (mul_pos (rpow_pos_of_pos (dyadic_pos _) _) (rpow_pos_of_pos (dyadic_pos _) _))).mpr
  have bound := mul_le_mul (rpow_le_one (dyadic_pos j).le (dyadic_le_one _) he)
    (rpow_le_one (dyadic_pos k).le (dyadic_le_one _) hf) (rpow_nonneg (dyadic_pos k).le f) zero_le_one
  simpa using mul_le_mul_of_nonneg_left bound (show 0≤3*ξ by positivity)

theorem active_le {ι : Type*} (links : Finset ι) (scale : ι→ℕ) (y : ι→ℝ)
    (m j k : ℕ) (ξ e f n : ℝ)
    (total : ∑ i∈links,(copies (y i):ℝ)*(dyadic (scale i)^e*dyadic (widthIndex m (y i))^f)
      ≤ 3*ξ*n) :
    (active links scale y m j k : ℝ) ≤ fraction ξ e f j k * n := by
  let d:=dyadic j^e*dyadic k^f
  have hd : 0<d := mul_pos (rpow_pos_of_pos (dyadic_pos _) _) (rpow_pos_of_pos (dyadic_pos _) _)
  have bound : (active links scale y m j k : ℝ)*d ≤ 3*ξ*n := by
    unfold active
    push_cast
    rw [Finset.sum_mul]
    refine (sum_le_sum fun i _ => ?_).trans total
    by_cases h : scale i=j ∧ widthIndex m (y i)=k
    · simp [h,d]
    · simp only [ite_eq_right h,zero_mul]
      exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (rpow_nonneg (dyadic_pos _).le _)
        (rpow_nonneg (dyadic_pos _).le _))
  change _ ≤ (3*ξ/d)*n
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hd).mpr bound

/-- Number of physically installed slots, including every idle batch. -/
def installed (c n : ℝ) (K : ℕ) : ℕ := ⌈6*c*n/K⌉₊*K

theorem installed_bounds {c n : ℝ} (hc : 0≤c) (hn : 0≤n) {K : ℕ}
    (hk : 0<K) (small : (K:ℝ)≤c*n) :
    6*c*n ≤ (installed c n K:ℝ) ∧ (installed c n K:ℝ)≤7*c*n := by
  have hk' : 0<(K:ℝ) := by exact_mod_cast hk
  have up := Nat.ceil_lt_add_one (show 0≤6*c*n/K by positivity)
  have low := Nat.le_ceil (6*c*n/K)
  have eq : 6*c*n/K*K=6*c*n := div_mul_cancel₀ _ hk'.ne'
  unfold installed
  push_cast
  constructor
  · simpa only [eq] using mul_le_mul_of_nonneg_right low hk'.le
  · nlinarith [mul_lt_mul_of_pos_right up hk']

private theorem dyadic_geom {δ : ℝ} (hδ : 0<δ) (d : ℕ) :
    ∑ j∈range d,dyadic j^δ ≤ 1/(1-(1/2:ℝ)^δ) := by
  let r := (1/2:ℝ)^δ
  have hr : r<1 := rpow_lt_one (by norm_num) (by norm_num) hδ
  have g := geom_sum_mul_neg r d
  have rp : 0≤r^d := pow_nonneg (rpow_nonneg (by norm_num) _) _
  dsimp only [dyadic]
  simp_rw [←rpow_pow_comm (by norm_num : (0:ℝ)≤1/2)]
  exact (le_div_iff₀ (sub_pos.mpr hr)).mpr (by linarith)

/-- Geometric summation over the finite dyadic rectangle bounds the total
reserved cost uniformly in its two dimensions. Indices outside a physical menu
can be assigned zero slots. -/
theorem installed_total {ξ n v b δ : ℝ} (hξ : 0≤ξ) (hn : 0≤n) (hδ : 0<δ)
    (J K : ℕ) (S : ℕ→ℕ→ℕ)
    (bought : ∀ j∈range J, ∀ k∈range K,
      (S j k:ℝ)≤7*fraction ξ (v-δ) (1-b-δ) j k*n) :
    ∑ j∈range J,∑ k∈range K,(S j k:ℝ)*(dyadic j^v*dyadic k^(1-b))
      ≤ 21*ξ*n*(1/(1-(1/2:ℝ)^δ))^2 := by
  let c := 21*ξ*n
  have hc : 0≤c := by dsimp [c]; positivity
  have per (j k : ℕ) (hj : j∈range J) (hk : k∈range K) :
      (S j k:ℝ)*(dyadic j^v*dyadic k^(1-b)) ≤ c*(dyadic j^δ*dyadic k^δ) := by
    have same (x z : ℝ) (hx : 0<x) : x^z=x^(z-δ)*x^δ := by
      rw [←rpow_add hx]; congr 1; ring
    apply (mul_le_mul_of_nonneg_right (bought j hj k hk)
      (mul_nonneg (rpow_nonneg (dyadic_pos _).le _) (rpow_nonneg (dyadic_pos _).le _))).trans_eq
    rw [same (dyadic j) v (dyadic_pos j),same (dyadic k) (1-b) (dyadic_pos k)]
    dsimp only [fraction,c]
    field_simp [ne_of_gt (rpow_pos_of_pos (dyadic_pos j) (v-δ)),ne_of_gt (rpow_pos_of_pos (dyadic_pos k) (1-b-δ))]
   ; ring
  have g₁ := dyadic_geom hδ J
  have g₂ := dyadic_geom hδ K
  have hf : 0≤1/(1-(1/2:ℝ)^δ) := by
    exact (one_div_pos.mpr (sub_pos.mpr (rpow_lt_one (by norm_num) (by norm_num) hδ))).le
  calc
    _ ≤ ∑ j∈range J,∑ k∈range K,c*(dyadic j^δ*dyadic k^δ) :=
      sum_le_sum fun j hj => sum_le_sum fun k hk => per j k hj hk
    _ = c*((∑ j∈range J,dyadic j^δ)*(∑ k∈range K,dyadic k^δ)) := by
      simp only [←mul_assoc,←Finset.mul_sum,←Finset.sum_mul]
    _ ≤ _ := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (mul_le_mul g₁ g₂
        (sum_nonneg fun k _=>rpow_nonneg (dyadic_pos _).le _) hf) hc


end
end Hierarchy.TaggedShorterBudget

end OAI
