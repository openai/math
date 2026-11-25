import OAI.Optimization.LinearProgramming.PriceGame.LearningExperts
import OAI.Optimization.LinearProgramming.PriceGame.LearningPathCost

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace Bits

open Finset

/-- The denominator common to all raw representatives in the manuscript (d₀ = 64). -/
def commonDenominator : ℕ := (Icc 1 66).lcm id

theorem commonDenominator_pos : 0 < commonDenominator := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro i hi
  exact Nat.ne_of_gt (Finset.mem_Icc.mp hi).1

theorem representative_den_dvd {p : ℕ} (d : Paths.Costs (Fin (p+1))) (a i : Fin (p+1)) :
    (representative d a i).den ∣ p + 1 := by
  let z : ℤ := ∑ s, potential d a s i
  have he : representative d a i = Rat.divInt z (p+1 : ℕ) := by
    rw [Rat.divInt_eq_div]
    simp [representative, z]
  rw [he]
  exact_mod_cast Rat.den_dvd z (p+1 : ℕ)

private theorem num_eq_mul_den (q : ℚ) : (q.num : ℚ) = q * (q.den : ℚ) := by
  exact (div_eq_iff (show (q.den : ℚ) ≠ 0 by exact_mod_cast q.den_nz)).mp q.num_div_den

private theorem cast_natAbs_num (q : ℚ) : (q.num.natAbs : ℚ) = |(q.num : ℚ)| := calc
    (q.num.natAbs : ℚ) = ((q.num.natAbs : ℤ) : ℚ) := by simp
    _ = ((|q.num| : ℤ) : ℚ) := by rw [Int.natCast_natAbs]
    _ = _ := by norm_cast

private theorem abs_le_num (q : ℚ) : |q| ≤ (q.num.natAbs : ℚ) := by
  have h₁ : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  have h := mul_le_mul_of_nonneg_left h₁ (abs_nonneg q)
  rw [mul_one] at h
  calc
    |q| ≤ |q| * (q.den : ℚ) := h
    _ = |q * (q.den : ℚ)| := by rw [abs_mul, abs_of_nonneg (show 0 ≤ (q.den : ℚ) by positivity)]
    _ = |(q.num : ℚ)| := by rw [num_eq_mul_den]
    _ = _ := (cast_natAbs_num q).symm

private theorem size_mul_le (x y : ℕ) : (x*y).size ≤ x.size + y.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  calc
    x*y ≤ x*(2^y.size) := Nat.mul_le_mul_left _ (Nat.lt_size_self y).le
    _ < (2^x.size)*(2^y.size) := Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self x) (by positivity)

/-- Bounds for the reduced fractions obtained from the actual list of experts. -/
theorem generated_fraction {p R : ℕ} {a : Fin (p+1)} {s : Experts.Feature (p+1) → Finset ℚ}
    {v : Fin (p+1) → ℚ} (hv : v ∈ Experts.generate R a s) (i : Fin (p+1)) :
    (v i).den ∣ p+1 ∧ (v i).num.natAbs ≤ (R+1)*(p+1) := by
  obtain ⟨c, _, hc⟩ := List.mem_filterMap.mp hv
  cases ht : cellTable R a (Experts.observations s c) with
  | none => simp [cellRepresentative, ht] at hc
  | some t =>
    have he : representative (Paths.read t) a = v := by simpa [cellRepresentative, ht] using hc
    have hd : (v i).den ∣ p+1 := he ▸ representative_den_dvd (Paths.read t) a i
    refine ⟨hd, ?_⟩
    have box := (Experts.generated_sound hv).2.1 i
    have hlow : 0 ≤ v i := by
      have hL : (0 : ℤ) ≤ boxLower a i := by simp [boxLower]; split <;> omega
      exact (by exact_mod_cast hL : (0 : ℚ) ≤ boxLower a i).trans box.1
    have hup : v i ≤ (R+1 : ℕ) := by
      have hU : boxUpper R a i ≤ (R+1 : ℕ) := by simp [boxUpper]; split <;> omega
      exact box.2.trans (by exact_mod_cast hU)
    have hden : (v i).den ≤ p+1 := Nat.le_of_dvd (by omega) hd
    have hnum0 : (0 : ℤ) ≤ (v i).num := by
      have h : (0 : ℚ) ≤ (v i).num := by rw [num_eq_mul_den]; positivity
      exact_mod_cast h
    have hnum : ((v i).num : ℚ) ≤ (R+1 : ℕ) * (p+1 : ℕ) := by
      rw [num_eq_mul_den]
      apply mul_le_mul hup (by exact_mod_cast hden) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hi : (v i).num ≤ ((R+1)*(p+1) : ℕ) := by exact_mod_cast hnum
    exact_mod_cast (show ((v i).num.natAbs : ℤ) ≤ ((R+1)*(p+1) : ℕ) by
      rw [Int.natCast_natAbs, abs_of_nonneg hnum0]; exact hi)

theorem generated_common_denominator {p R : ℕ} {a : Fin (p+1)}
    {s : Experts.Feature (p+1) → Finset ℚ} {v : Fin (p+1) → ℚ}
    (hv : v ∈ Experts.generate R a s) (hp : p ≤ 65) (i : Fin (p+1)) :
    (v i).den ∣ commonDenominator :=
  (generated_fraction hv i).1.trans (Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))

theorem generated_bit_lengths {p R : ℕ} {a : Fin (p+1)}
    {s : Experts.Feature (p+1) → Finset ℚ} {v : Fin (p+1) → ℚ}
    (hv : v ∈ Experts.generate R a s) (i : Fin (p+1)) :
    (v i).den.size ≤ (p+1).size ∧ (v i).num.natAbs.size ≤ (R+1).size + (p+1).size := by
  obtain ⟨hd, hn⟩ := generated_fraction hv i
  exact ⟨Nat.size_le_size (Nat.le_of_dvd (by omega) hd), (Nat.size_le_size hn).trans (size_mul_le _ _)⟩

private theorem min_abs_le {x y M : ℤ} (hx : |x| ≤ M) (hy : |y| ≤ M) : |min x y| ≤ M := by
  rcases le_total x y with h|h
  · simpa [min_eq_left h] using hx
  · simpa [min_eq_right h] using hy

private theorem tighten_bounded {n : ℕ} {d : Bounds n} {M c : ℤ} (i j : Fin n)
    (hd : ∀ s t, |d s t| ≤ M) (hc : |c| ≤ M) :
    ∀ s t, |tightenArc d i j c s t| ≤ M := by
  intro s t
  simp only [tightenArc]
  split
  · exact min_abs_le (hd s t) hc
  · exact hd s t

/-- Integer tightening increases a bound on the absolute threshold by at most one. -/
theorem floor_ceil_bounds {θ : ℚ} {B : ℕ} (hθ : |θ| ≤ B) :
    |⌊θ⌋| ≤ (B : ℤ) ∧ |⌈θ⌉| ≤ (B : ℤ) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hθ
  have hlo' : ((-(B : ℤ) : ℤ) : ℚ) ≤ θ := by simpa using hlo
  have hhi' : θ ≤ ((B : ℤ) : ℚ) := by simpa using hhi
  exact ⟨abs_le.mpr ⟨by simpa only [Int.floor_intCast] using Int.floor_le_floor hlo',
                     by simpa only [Int.floor_intCast] using Int.floor_le_floor hhi'⟩,
    abs_le.mpr ⟨by simpa only [Int.ceil_intCast] using Int.ceil_le_ceil hlo',
                by simpa only [Int.ceil_intCast] using Int.ceil_le_ceil hhi'⟩⟩

private theorem add_bounded {n B : ℕ} {d e : Bounds n} {o : Observation n} {M : ℤ}
    (hd : ∀ s t, |d s t| ≤ M) (hM : (B : ℤ)+1 ≤ M) (hθ : |o.threshold| ≤ B)
    (he : addObservation d o = some e) : ∀ s t, |e s t| ≤ M := by
  obtain ⟨hf, hc⟩ := floor_ceil_bounds hθ
  obtain ⟨i,j,θ,k⟩ := o
  change |⌊θ⌋| ≤ (B : ℤ) at hf
  change |⌈θ⌉| ≤ (B : ℤ) at hc
  have hfl := abs_le.mp hf
  have hce := abs_le.mp hc
  cases k with
  | lt =>
    simp only [addObservation, Option.some.injEq] at he
    subst e
    exact tighten_bounded j i hd (abs_le.mpr ⟨by omega, by omega⟩)
  | gt =>
    simp only [addObservation, Option.some.injEq] at he
    subst e
    exact tighten_bounded i j hd (abs_le.mpr ⟨by omega, by omega⟩)
  | eq =>
    simp only [addObservation] at he
    split at he
    next =>
      injection he with he'
      subst e
      have hfloor : |⌊θ⌋| ≤ M := hf.trans (by omega)
      exact tighten_bounded (c := -⌊θ⌋) i j (tighten_bounded (c := ⌊θ⌋) j i hd hfloor)
        (by simpa using hfloor)
    next => contradiction

private theorem addList_bounded {n B : ℕ} {M : ℤ} (os : List (Observation n))
    (hM : (B : ℤ)+1 ≤ M) (hθ : ∀ o ∈ os, |o.threshold| ≤ B) (d e : Bounds n)
    (hd : ∀ s t, |d s t| ≤ M) (he : addObservations os d = some e) : ∀ s t, |e s t| ≤ M := by
  induction os generalizing d with
  | nil =>
    have h : d = e := Option.some.inj he
    cases h
    exact hd
  | cons o os ih =>
    cases ha : addObservation d o with
    | none => simp [addObservations, ha] at he
    | some f =>
      exact ih (fun o' ho' => hθ _ (by simp [ho'])) f (add_bounded hd hM (hθ o (by simp)) ha)
        (by simpa [addObservations, ha] using he)

/-- Every initial arc retains a polynomial magnitude bound, including in cells later
discarded because a diagonal becomes negative. A fractional equality may return `none`. -/
theorem compiled_abs_bound {n R B : ℕ} (a : Fin n) (os : List (Observation n)) {d : Bounds n}
    (hθ : ∀ o ∈ os, |o.threshold| ≤ B) (he : addObservations os (boxBounds R a) = some d) :
    ∀ i j, |d i j| ≤ (max (R+1) (B+1) : ℕ) := by
  apply addList_bounded (B := B) os (by exact_mod_cast le_max_right (R+1) (B+1)) hθ _ _ _ he
  intro i j
  have hl : 0 ≤ boxLower a i ∧ boxLower a i ≤ 1 := by unfold boxLower; split <;> omega
  have hu : 0 ≤ boxUpper R a j ∧ boxUpper R a j ≤ (R : ℤ)+1 := by unfold boxUpper; split <;> omega
  have hm : (R : ℤ)+1 ≤ ((max (R+1) (B+1) : ℕ) : ℤ) := by exact_mod_cast le_max_left (R+1) (B+1)
  unfold boxBounds
  split
  · rw [abs_zero]; exact Nat.cast_nonneg _
  · exact abs_le.mpr ⟨by omega, by omega⟩

/-- Magnitude bits needed in every Floyd–Warshall intermediate, starting with data whose
reduced numerators and radius have at most `b` bits. The denominator is at least one. -/
theorem compiled_sweep_bits {n R b : ℕ} (a : Fin n) (os : List (Observation n)) {d : Bounds n}
    (hR : R.size ≤ b) (hθ : ∀ o ∈ os, o.threshold.num.natAbs.size ≤ b)
    (he : addObservations os (boxBounds R a) = some d) (ks : List (Fin n)) (i j : Fin n) :
    (Paths.sweep ks (Paths.initial d) i j).natAbs.size ≤ ks.length + b + 1 := by
  let B := 2^b - 1
  have hpow : 0 < 2^b := by positivity
  have hr : R < 2^b := Nat.size_le.mp hR
  have hvals (o) (ho : o ∈ os) : |o.threshold| ≤ B := by
    have hlt := Nat.size_le.mp (hθ o ho)
    apply (abs_le_num _).trans
    exact_mod_cast (show o.threshold.num.natAbs ≤ B by dsimp [B]; omega)
  have hmax : max (R+1) (B+1) ≤ 2^b := by dsimp [B]; omega
  have hs (x y : Fin n) : |Paths.initial d x y| ≤ ((2^b : ℕ) : ℤ) := by
    have hd : |d x y| ≤ ((2^b : ℕ) : ℤ) :=
      (compiled_abs_bound a os hvals he x y).trans (by exact_mod_cast hmax)
    simp only [Paths.initial]
    split
    · exact min_abs_le (by simp) hd
    · exact hd
  have hn (x y : Fin n) : (Paths.initial d x y).natAbs ≤ 2^b := by
    exact_mod_cast (show ((Paths.initial d x y).natAbs : ℤ) ≤ ((2^b : ℕ) : ℤ) by
      rw [Int.natCast_natAbs]; exact hs x y)
  have hh : (2^b).size ≤ b+1 := Nat.size_le.mpr (by rw [pow_succ]; omega)
  exact (Paths.sweep_magnitude_bits ks (Paths.initial d) (2^b) hn i j).trans (by omega)

/-- The price comparisons use signed differences. Subtracting two prices
on the same rational grid preserves the grid; swapping the arguments
covers the negative sign. -/
theorem difference_threshold {x y : ℚ} {Q U : ℕ} (hQ : 0 < Q)
    (hx : x.den ∣ Q) (hy : y.den ∣ Q) (hux : |x| ≤ U) (huy : |y| ≤ U) :
    (x-y).den ∣ Q ∧ (x-y).num.natAbs ≤ 2*U*Q := by
  have hd : (x-y).den ∣ Q := (Rat.sub_den_dvd_lcm x y).trans (Nat.lcm_dvd hx hy)
  have hd' : (x-y).den ≤ Q := Nat.le_of_dvd hQ hd
  have hu : |x-y| ≤ (↑(2*U) : ℚ) := by
    calc
      |x-y| ≤ |x| + |y| := abs_sub _ _
      _ ≤ _ := by push_cast; linarith
  refine ⟨hd, ?_⟩
  have hn : ((x-y).num.natAbs : ℚ) ≤ ↑(2*U*Q) := by
    rw [cast_natAbs_num, num_eq_mul_den, abs_mul,
      abs_of_nonneg (show 0 ≤ ((x-y).den : ℚ) by positivity), Nat.cast_mul]
    exact mul_le_mul hu (by exact_mod_cast hd') (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact_mod_cast hn

/-- Iterating the market price bound down a path adds only a fixed bit-cost
per level, even if magnitudes themselves grow geometrically. -/
theorem path_price_bits (R G : ℕ) (U : ℕ → ℕ) (hzero : U 0 = 0)
    (hstep : ∀ n, U (n+1) ≤ 2*G*(2*(R+1)+U n)) (depth : ℕ) :
    (U depth).size ≤ (2*(R+1)).size + depth*(2*G+1).size := by
  let C := 2*(R+1)
  let K := 2*G+1
  have major (n : ℕ) : U n + C ≤ C*K^n := by
    induction n with
    | zero => simp [hzero]
    | succ n ih =>
      calc
        U (n+1) + C ≤ 2*G*(C+U n) + C := Nat.add_le_add_right (hstep n) _
        _ ≤ (U n+C)*K := by dsimp [K]; nlinarith
        _ ≤ (C*K^n)*K := Nat.mul_le_mul_right _ ih
        _ = C*K^(n+1) := by ring
  have width (n : ℕ) : (C*K^n).size ≤ C.size + n*K.size := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Nat.mul_assoc, Nat.succ_mul]
      exact (size_mul_le _ _).trans (by omega)
  exact (Nat.size_le_size ((Nat.le_add_right _ _).trans (major depth))).trans (width depth)

end Bits
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
