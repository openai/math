import OAI.Computability.IntegerMultiplication.Fourier.Window
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier
open Finset Real

/-- Reduce to a centered signed residue (either side if a tie). -/
theorem represent_near (n : ℕ) [NeZero n] (i : ℤ) :
    ∃ j u : ℤ, i=j+u*n ∧ 2*|j| ≤ (n:ℤ) := by
  have hh := Int.emod_add_mul_ediv i (n:ℤ)
  let a := i%(n:ℤ)
  have hn : (0:ℤ)<n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hg : 0≤a := Int.emod_nonneg _ (by omega)
  have hm : a < n := Int.emod_lt_of_pos i hn
  change a+_=i at hh
  by_cases h : 2*a≤(n:ℤ)
  · exact ⟨a,i/n,by rw [mul_comm (i/(n:ℤ)),hh],by rwa [abs_of_nonneg hg]⟩
  · refine ⟨a-n,i/n+1,?_,?_⟩
    · rw [add_mul,one_mul,mul_comm (i/(n:ℤ))]
      omega
    rw [abs_of_nonpos (by omega)]
    omega

theorem window_period (n : ℕ) [NeZero n] (i k : ℤ) (D : ℕ) :
    window D n (i+k*n) = window D n i := by
  apply Complex.ofReal_injective
  simp only [window_phase]
  refine sum_congr rfl ?_
  intro r _
  rw [mul_add,← mul_assoc r k,phase_add,phase_divides,mul_one]

private theorem cos_sq_le {x : ℝ} (h : |x|≤1/2) :
    Real.cos (π*x)^2 ≤ Real.exp (-(4*x^2)) := by
  have hh := Real.le_sin_mul (x := 2*|x|) (by positivity) (by linarith)
  rw [show π/2*(2*|x|)=π*|x| by ring] at hh
  have e : (2*|x|)^2 ≤ Real.sin (π*x)^2 := by
    apply (pow_le_pow_left₀ (by positivity) hh 2).trans
    cases le_total 0 x with
    | inl h => simp [abs_of_nonneg h]
    | inr h => simp [abs_of_nonpos h]
  have hk := Real.cos_sq_add_sin_sq (π*x)
  have hp := Real.add_one_le_exp (-(4*x^2))
  nlinarith [sq_abs x]

theorem window_decay {n : ℕ} [NeZero n] {i : ℤ} (h : 2*|i|≤(n:ℤ)) (D : ℕ) :
    |window D n i| ≤ Real.exp (-4*(D:ℝ)*(((i:ℤ):ℝ)/n)^2) := by
  have hn : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  let x : ℝ := i/(n:ℝ)
  have hh : |x|≤ 1/2 := by
    dsimp [x]
    rw [abs_div, abs_of_pos hn, div_le_iff₀ hn]
    have e : 2*|(i:ℝ)|≤(n:ℝ) := by exact_mod_cast h
    linarith
  have he := cos_sq_le hh
  change |Real.cos (π*x)^(2*D)| ≤ Real.exp (-4*↑D*x^2)
  rw [pow_mul, abs_of_nonneg (pow_nonneg (sq_nonneg _) _),
    show (-4 : ℝ)*D*x^2=(D:ℝ)*(-(4*x^2)) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (sq_nonneg _) he _

variable {s t : ℕ} [NeZero s] [NeZero t]

/-- At row k choose y as center. -/
noncomputable def around (s L : ℕ) [NeZero s] (y : ℤ) : Finset (Spot s) :=
  (rad L).image fun i => wrap s (y+i)

theorem extreme (D L : ℕ) (j : Spot s) (k : Spot t) (y δ : ℤ)
    (hy : (s:ℤ)*rep k = t*y+δ) (hδ : |δ|≤(t:ℤ)) (hj : j∉around s L y) :
    |window D (s*t) ((t:ℤ)*rep j - s*rep k)| ≤
    Real.exp (-(4:ℝ)*D*(L:ℕ)^2/(s:ℕ)^2) := by
  have hn : 0<t := Nat.pos_of_ne_zero (NeZero.ne t)
  have hp : 0<s := Nat.pos_of_ne_zero (NeZero.ne s)
  obtain ⟨z,u,he,hm⟩ := represent_near (s*t) ((t:ℤ)*rep j - s*rep k)
  -- its small representative is still a non-covered j shift.
  let v : ℤ := rep j - y - u*s
  have h : z=t*v-δ := by
    dsimp [v]
    simp only [Nat.cast_mul] at he
    rw [hy] at he
    linarith
  have hmem : v∉rad L := by
    intro e
    have hrot : wrap s (y+v)=j := by
      dsimp [v]
      refine Eq.trans ?_ (wrap_rep s j)
      rw [wrap_eq, Int.modEq_iff_dvd]
      exact ⟨u,by ring⟩
    exact hj (mem_image.mpr ⟨v,e,hrot⟩)
  have ht : (L:ℤ) < |v| := by
    by_contra! eq
    exact hmem (mem_rad.mpr (abs_le.mp eq))
  have hw : (↑t:ℤ) * ↑L ≤ |z| := by
    have e := abs_add_le (z:ℤ) δ
    rw [show z+δ=t*v by omega, abs_mul, abs_of_nonneg (Int.natCast_nonneg _)] at e
    have ha : |v| ≥ (L:ℤ)+1 := by omega
    have hb : 0<(t:ℤ) := by exact_mod_cast hn
    nlinarith
  rw [he,window_period]
  have hh := (window_decay (n := s*t) hm D)
  refine hh.trans (Real.exp_le_exp.mpr ?_)
  -- cast
  have hs : 0<(s:ℝ) := by exact_mod_cast hp
  have hu : 0<(t:ℝ) := by exact_mod_cast hn
  have hz : (t:ℝ)*L≤|(z:ℝ)| := by exact_mod_cast hw
  rw [Nat.cast_mul]
  have hq : ((L:ℝ)/s)^2≤((z:ℝ)/((s:ℝ)*t))^2 := by
    rw [← sq_abs ((z:ℝ)/((s:ℝ)*t)), abs_div,abs_of_pos (by positivity : 0<(s:ℝ)*t)]
    apply pow_le_pow_left₀ (by positivity)
    field_simp
    simpa [mul_comm] using hz
  have hh : (0:ℝ)≤4*D := by positivity
  have hmu := mul_le_mul_of_nonneg_left hq hh
  rw [div_pow] at hmu
  rw [show -(4:ℝ)*D*↑L^2/↑s^2= -(4*D*(↑L^2/↑s^2)) by ring,
    show -(4:ℝ)*D*(↑z/(↑s*↑t))^2 = -(4*D*(↑z/(↑s*↑t))^2) by ring]
  exact neg_le_neg hmu

end Fourier

end IntegerMultiplication
end Computability
end OAI
