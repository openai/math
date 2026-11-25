import OAI.Computability.IntegerMultiplication.Fourier.Recover

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier
open Finset Real
variable {s t : ℕ} [NeZero s] [NeZero t]

noncomputable def factor (D : ℕ) (s t : ℕ) (i : Spot s) : ℝ :=
  1 / ((t:ℝ)*coef D (delta s t i))

noncomputable def start (s t D : ℕ) (i j : Spot s) : ℝ :=
  if i=j then factor D s t i else 0

noncomputable def mixTable (t D : ℕ) (l : Finset ℤ) : ℕ → Spot s → Spot s → ℝ
  | 0 => start s t D
  | k+1 => fun i j => start s t D i j -
      ∑ u ∈ l, ratio t D (delta s t i) u * mixTable t D l k (wrap s (rep i+u)) j

omit [NeZero t] in
theorem mixTable_apply (e : s ≤ t) (D : ℕ) (l : Finset ℤ) (w : Arr t ℂ) (k i) :
    iter t D l (pickDiv e D w) k i =
    ∑ j : Spot s, (mixTable t D l k i j : ℂ)*w (pick s t e j) := by
  have eq (i : Spot s) : pickDiv e D w i = ∑ j : Spot s, ((start s t D i j : ℝ):ℂ)*w (pick s t e j) := by
    unfold start pickDiv
    simp only [apply_ite (fun x : ℝ => (x:ℂ)), ite_mul, Complex.ofReal_zero,zero_mul,
      sum_ite_eq, mem_univ,ite_true,factor,
      div_eq_mul_inv,one_mul]
    push_cast
    apply mul_comm
  induction k generalizing i with
  | zero => exact eq _
  | succ k ih =>
    rw [iter, mixTable,Pi.sub_apply,eq i]
    unfold off
    conv_lhs =>
      arg 2; arg 2; ext j
      rw [ih]
    simp only [mul_sum,Complex.ofReal_sub,sub_mul,sum_sub_distrib]
    push_cast
    rw [sum_comm (s := l)]
    simp only [← mul_assoc,sum_mul]

omit [NeZero t] in
theorem table_near {i j : Spot s} {D} {L} (k) (e :
    mixTable t D (nhood L) k i j ≠ 0) :
    j ∈ around s (k*L) (rep i) := by
  -- induction on band growth; find at least one nonzero summand
  have hz (i : Spot s) (n) : i ∈ around s n (rep i) := by
    unfold around
    exact mem_image.mpr ⟨0,by simp,by simp⟩
  induction k generalizing i with
  | zero =>
    by_cases hi : i=j
    · subst j; exact hz _ _
    · simp [mixTable,start,hi] at e
  | succ k ih =>
    by_cases hi : i=j
    · subst j; exact hz _ _
    · simp only [mixTable,start,ite_eq_right hi,zero_sub, neg_ne_zero] at e
      obtain ⟨u,hu,he⟩ := Finset.exists_ne_zero_of_sum_ne_zero e
      have hk := ih (i := wrap s (rep i+u)) (right_ne_zero_of_mul he)
      obtain ⟨v,hv,hh⟩ := mem_image.mp hk
      have hh' := wrap_add s i u v
      unfold nhood at hu
      have ha := mem_rad.mp (mem_erase.mp hu).2
      have hb := mem_rad.mp hv
      apply mem_image.mpr
      refine ⟨u+v,?_,?_⟩
      · simp only [mem_rad, add_mul, one_mul,Nat.cast_add]
        constructor <;> omega
      · exact hh'.symm.trans hh

omit [NeZero t] in
theorem restore_short (e : s≤t) (D J k : ℕ) (hk : 2*(k*J) < s) (w : Arr t ℂ) (i) :
    restore e D J k w i = ∑ u ∈ rad (k*J),
      (mixTable t D (nhood J) k i (wrap s (rep i+u)) : ℂ) * w (pick s t e (wrap s (rep i+u))) := by
  rw [restore, mixTable_apply, ← sum_image (f := fun j => (mixTable t D (nhood J) k i j : ℂ)*w (pick s t e j))
    (s := rad (k*J)) (g := fun u => wrap s (rep i+u))]
  · refine (sum_subset (subset_univ (around s _ _)) (fun x _ hx => ?_)).symm
    rw [show mixTable t D (nhood J) k i x = 0 from by_contra fun h => hx (table_near k h)]
    simp
  · exact inj_near s _ hk

omit [NeZero s] in
private theorem fac_le {D} {C : ℝ} {i : Spot s} (hc : 1 / coef D (delta s t i) ≤ C) :
    |factor D s t i| ≤ C := by
  let z := coef D (delta s t i)
  have hu : 1 ≤ (t:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
  unfold factor
  rw [abs_of_nonneg (show (0:ℝ)≤1 / ((t:ℝ)*coef D (delta s t i)) by
    exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (coef_nonneg ..)))]
  change 1 / ((t:ℝ)*z) ≤ C
  rw [one_div,mul_inv_rev]
  change 1/z ≤ _ at hc
  rw [one_div] at hc
  have he := mul_le_mul_of_nonneg_left (show (t:ℝ)⁻¹ ≤ 1 by simpa using inv_le_one_of_one_le₀ hu) (show 0 ≤ z⁻¹ from by apply inv_nonneg.mpr; exact coef_nonneg ..)
  simpa using he.trans (show z⁻¹*1≤C by simpa using hc)

-- Uniform scalar bound on entries of mixTable.
theorem table_bound {D} {l : Finset ℤ} {C : ℝ} (k) (i j : Spot s)
    (hc : ∀ i : Spot s, 1 / coef D (delta s t i) ≤ C) (he : 0≤C)
    (hd : ∀ i : Spot s, ∑ u ∈ l, ratio t D (delta s t i) u ≤ 1/2) :
    |mixTable t D l k i j| ≤ 2*C := by
  have hs (i : Spot s) : |start s t D i j| ≤ C := by
    unfold start
    split
    · exact fac_le (hc i)
    · simpa
  induction k generalizing i with
  | zero => exact (hs i).trans (by linarith)
  | succ k ih =>
    rw [mixTable]
    apply (abs_sub _ _).trans -- check
    have hsum :
        |∑ u ∈ l, ratio t D (delta s t i) u * mixTable t D l k (wrap s (rep i+u)) j|
        ≤ C := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hq : ∀ u ∈ l, |ratio t D (delta s t i) u * mixTable t D l k (wrap s (rep i+u)) j| ≤
          ratio t D (delta s t i) u * (2*C) :=
        fun u _ => by
          rw [abs_mul, abs_of_nonneg (ratio_nonneg _ _ _ _)]
          exact mul_le_mul_of_nonneg_left (ih _) (ratio_nonneg ..)
      apply (sum_le_sum hq).trans
      rw [← sum_mul]
      have hh := mul_le_mul_of_nonneg_right (hd i) (show 0≤2*C by linarith)
      linarith
    linarith [hs i]

end Fourier

end IntegerMultiplication
end Computability
end OAI
