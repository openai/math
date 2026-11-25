import OAI.Optimization.LinearProgramming.Games.Rational

/-! An executable extraction of the rational stochastic-game value from the
computed rational approximation. The list length is logarithmic in the binary
denominator of the supplied approximation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Games

/-- Rational implementation of the simple continued-fraction convergents. -/
def rationalConvergent (x : ℚ) : ℕ → ℚ
  | 0 => ⌊x⌋
  | n + 1 => ⌊x⌋ + (rationalConvergent (Int.fract x)⁻¹ n)⁻¹

theorem rationalConvergent_eq (x : ℚ) (k : ℕ) :
    rationalConvergent x k = (x : ℝ).convergent k := by
  induction k generalizing x with
  | zero => simp [rationalConvergent]
  | succ k ih => simp [rationalConvergent, ih, Rat.cast_fract]

private theorem convergent_of_fract_zero {x : ℚ} (hz : Int.fract x = 0) (k : ℕ) :
    rationalConvergent x k = x := by
  have hx : (⌊x⌋ : ℚ) = x := by simpa [hz] using Int.floor_add_fract x
  rw [← hx, rationalConvergent_eq, Rat.cast_intCast, Real.convergent_of_int]

private theorem convergent_step {x : ℚ} {k : ℕ}
    (h : rationalConvergent (Int.fract x)⁻¹ k = (Int.fract x)⁻¹) :
    rationalConvergent x (k+1) = x := by simp [rationalConvergent, h]

/-- In two Euclidean steps, the new positive denominator is less than half
the old upper bound. Thus every convergent at or after twice the bit-length
of an upper bound for the denominator already equals the original rational. -/
theorem convergent_stabilizes {d k : ℕ} (hd : 0 < d) (hsize : d < 2^k)
    (m : ℤ) {j : ℕ} (hj : 2*k ≤ j) :
    rationalConvergent ((m : ℚ)/d) j = (m : ℚ)/d := by
  induction k generalizing d m j with
  | zero => simp at hsize; omega
  | succ k ih =>
    let r : ℕ := (m % (d : ℤ)).toNat
    have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
    have hr' : (r : ℤ) = m % d := Int.toNat_of_nonneg (Int.emod_nonneg _ hd')
    have hr_lt : r < d := by
      exact_mod_cast (hr'.trans_lt (Int.emod_lt_of_pos _ (by exact_mod_cast hd)))
    have hf : Int.fract ((m:ℚ)/d) = (r:ℚ)/d := by
      rw [Int.fract_div_intCast_eq_div_intCast_mod, ← hr', Int.cast_natCast]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · apply convergent_of_fract_zero
      simp [hf, hr]
    have htwo : 2 ≤ j := by omega
    obtain ⟨l,rfl⟩ : ∃ l, j = l+2 := ⟨j-2, by omega⟩
    apply convergent_step
    rw [hf, inv_div]
    have hf' : Int.fract ((d:ℚ)/r) = ((d%r:ℕ):ℚ)/r :=
      Int.fract_div_natCast_eq_div_natCast_mod
    rcases Nat.eq_zero_or_pos (d%r) with ht | ht
    · apply convergent_of_fract_zero
      simp [hf', ht]
    apply convergent_step
    rw [hf', inv_div]
    have hdiv : 1 ≤ d/r := Nat.one_le_div_iff hr |>.mpr hr_lt.le
    have hprod : r ≤ r * (d/r) := by simpa using Nat.mul_le_mul_left r hdiv
    have hrmod := Nat.mod_lt d hr
    have hsum := Nat.mod_add_div d r
    have hsz : d%r < 2^k := by
      rw [pow_succ] at hsize
      omega
    have hh := ih ht hsz (r:ℤ) (j := l) (by omega)
    simpa using hh

/-- The search reads at most `2*(z.den.log2+1)+1` convergents; its output can
be used directly when an approximation and denominator bound are explicit. -/
def reconstructValue (z : ℚ) (A : ℕ) : Option ℚ :=
  let candidates := (List.range (2*(z.den.log2+1)+1)).map (rationalConvergent z)
  candidates.find? fun q => decide (q.den ≤ A ∧ |z-q| ≤ 1/(8*(A:ℚ)^2))

theorem reconstructValue_eq {z g : ℚ} {A : ℕ} (hg : g.den ≤ A)
    (hz : |z-g| ≤ 1/(8*(A:ℚ)^2)) : reconstructValue z A = some g := by
  have castNear (q : ℚ) (h : |z-q| ≤ 1/(8*(A:ℚ)^2)) :
      |(z:ℝ)-q| ≤ 1/(8*(A:ℝ)^2) := by
    have hh : ((|z-q| : ℚ) : ℝ) ≤ ((1/(8*(A:ℚ)^2) : ℚ) : ℝ) := Rat.cast_le.mpr h
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
      Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast] using hh
  have hz' := castNear g hz
  obtain ⟨⟨k,hk⟩, hu⟩ := recover_rational_value hg hz'
  let depth := 2*(z.den.log2+1)
  have hstable (j : ℕ) (hj : depth ≤ j) : rationalConvergent z j = z := by
    simpa only [Rat.num_div_den] using convergent_stabilizes z.pos Nat.lt_log2_self z.num hj
  have hc : ∃ i < depth+1, rationalConvergent z i = g := by
    rw [← rationalConvergent_eq] at hk
    by_cases hkd : k ≤ depth
    · exact ⟨k, by omega, hk⟩
    · exact ⟨depth, Nat.lt_succ_self _, (hstable depth le_rfl).trans ((hstable k (by omega)).symm.trans hk)⟩
  obtain ⟨i, hi, hgi⟩ := hc
  let xs := (List.range (depth+1)).map (rationalConvergent z)
  have hm : g ∈ xs := List.mem_map.mpr ⟨i,List.mem_range.mpr hi,hgi⟩
  let p (q : ℚ) := decide (q.den ≤ A ∧ |z-q| ≤ 1/(8*(A:ℚ)^2))
  change xs.find? p = some g
  cases h : xs.find? p with
  | none =>
    have hp := List.find?_eq_none.mp h g hm
    exact False.elim (hp (decide_eq_true ⟨hg,hz⟩))
  | some q =>
    have hbool : p q = true := List.find?_some h
    have hp : q.den ≤ A ∧ |z-q| ≤ 1/(8*(A:ℚ)^2) := of_decide_eq_true hbool
    exact congrArg some (hu q hp.1 (castNear q hp.2))

end Games
end LinearProgramming
end Optimization
end OAI
