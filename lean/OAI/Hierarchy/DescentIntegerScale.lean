import OAI.Hierarchy.DescentRowScore

namespace OAI
/-! # Common integer scaling for all candidates in a conditional row step -/

namespace Hierarchy.DescentIntegerScale

open scoped BigOperators Classical
noncomputable section

variable {V : Type*} [Fintype V]

/-- Read the unnormalized autocorrelation of an integral load vector. -/
def natCorrelation [Add V] (x : V → ℕ) (d : V) : ℕ := ∑ i, x i * x (i+d)

theorem normalized_autocorrelation [AddCommGroup V] [Module (ZMod 2) V]
    (q : ℕ) (x : V → ℕ) (d : V) :
    DescentRowScore.autocorrelation (fun i => (x i : ℝ) / q) d =
      (natCorrelation x d : ℝ) / (q : ℝ)^2 := by
  simp only [DescentRowScore.autocorrelation, natCorrelation, Nat.cast_sum, Nat.cast_mul,
    Finset.sum_div, div_mul_div_comm, pow_two]

theorem correlation_le_mass_sq [Add V] (x : V → ℕ) (d : V) :
    natCorrelation x d ≤ (∑ i, x i)^2 := by
  unfold natCorrelation
  rw [pow_two,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_left _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i+d)))

/-- The integer numerator attached to one surviving difference. The index
`j` counts rows after the proposed new row, which leaves `r` rows unfixed. -/
def differenceNumerator (r : ℕ) (W : Fin (r+1) → V → ℕ) (d : V) : ℕ :=
  ∑ j, W j d * (2^(r-j.val)-1)

/-- The common denominator for entries initially normalized by `q`. -/
def denominator (q r : ℕ) : ℕ := q^2 * (2^r-1)

theorem denominator_pos {q r : ℕ} (hq : 0<q) (hr : 0<r) : 0<denominator q r := by
  have power : 1<(2:ℕ)^r := Nat.one_lt_pow (by omega) (by decide)
  exact Nat.mul_pos (pow_pos hq _) (by omega)

omit [Fintype V] in
theorem differenceNumerator_zero (W : Fin 1 → V → ℕ) (d : V) :
    differenceNumerator 0 W d=0 := by simp [differenceNumerator]

/-- `keep` is the set of nonzero differences annihilated by the chosen rows. -/
def rowNumerator (r : ℕ) (W : Fin (r+1) → V → ℕ) (keep : Finset V) : ℕ :=
  ∑ d ∈ keep, differenceNumerator r W d

/-- This is the finite sum with the original rational conditional probabilities. -/
def score (q r : ℕ) (W : Fin (r+1) → V → ℕ) (keep : Finset V) : ℝ :=
  ∑ d ∈ keep, ∑ j, ((W j d : ℝ)/(q:ℝ)^2) *
    (((2^(r-j.val)-1:ℕ):ℝ) / ((2^r-1:ℕ):ℝ))

omit [Fintype V] in
theorem score_eq_integer (q r : ℕ) (W : Fin (r+1) → V → ℕ) (keep : Finset V) :
    score q r W keep = (rowNumerator r W keep : ℝ)/(denominator q r : ℝ) := by
  simp only [score, rowNumerator, differenceNumerator, denominator, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, Finset.sum_div, div_mul_div_comm]

omit [Fintype V] in
theorem compare_scores {q r : ℕ} (hq : 0<q) (hr : 0<r) (W : Fin (r+1) → V → ℕ)
    (a b : Finset V) :
    score q r W a ≤ score q r W b ↔ rowNumerator r W a ≤ rowNumerator r W b := by
  have pos : (0:ℝ)<(denominator q r : ℕ) := by exact_mod_cast denominator_pos hq hr
  rw [score_eq_integer,score_eq_integer,div_le_div_iff_of_pos_right pos]
  exact Nat.cast_le

omit [Fintype V] in
theorem rowNumerator_zero (W : Fin 1 → V → ℕ) (keep : Finset V) :
    rowNumerator 0 W keep=0 := by simp [rowNumerator,differenceNumerator_zero]

/-- The total mass of an old load vector controls every entry quadratically.
The sum over input vectors and its largest integer weight contribute linearly. -/
theorem weighted_correlation_bound [Add V] {A : Type*} (members : Finset A)
    (x : A → V → ℕ) (w : A → ℕ) (d : V) (q weightBits massBits countBits : ℕ)
    (hm : ∀ a∈members, (∑ i,x a i) ≤ 2^massBits)
    (hw : ∀ a∈members, w a ≤ 2^weightBits) (hc : members.card ≤ 2^countBits) :
    q*(∑ a∈members,w a * natCorrelation (x a) d) ≤ q*2^(countBits+weightBits+2*massBits) := by
  apply Nat.mul_le_mul_left
  have h (a : A) (ha : a∈members) : w a * natCorrelation (x a) d ≤
      2^weightBits * (2^massBits)^2 :=
    Nat.mul_le_mul (hw a ha) ((correlation_le_mass_sq (x a) d).trans (Nat.pow_le_pow_left (hm a ha) 2))
  calc
    _ ≤ members.card*(2^weightBits*(2^massBits)^2) := by
      simpa using members.sum_le_card_nsmul _ _ h
    _ ≤ 2^countBits*(2^weightBits*(2^massBits)^2) := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [show 2*massBits=massBits+massBits by omega]; simp [pow_add,pow_two,mul_assoc]

omit [Fintype V] in
/-- A score fits in `k + 2*r + weightBits + 1` unsigned bits. The total
combines at most `2^k` differences and at most `r+1 ≤ 2^r` depths. -/
theorem rowNumerator_bound (r k weightBits : ℕ) (W : Fin (r+1) → V → ℕ)
    (keep : Finset V) (hkeep : keep.card ≤ 2^k) (hW : ∀ j d,W j d ≤ 2^weightBits) :
    rowNumerator r W keep < 2^(k+2*r+weightBits+1) := by
  have one (d : V) : differenceNumerator r W d ≤ 2^r*(2^weightBits*2^r) := by
    have term (j : Fin (r+1)) (_ : j∈Finset.univ) :
        W j d * (2^(r-j.val)-1) ≤ 2^weightBits*2^r :=
      Nat.mul_le_mul (hW j d) ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)))
    unfold differenceNumerator
    calc
      _ ≤ (r+1)*(2^weightBits*2^r) := by
        simpa using Finset.univ.sum_le_card_nsmul _ _ term
      _ ≤ _ := Nat.mul_le_mul_right _ r.lt_two_pow_self
  have nonstrict : rowNumerator r W keep ≤ 2^(k+2*r+weightBits) := calc
    _ ≤ keep.card*(2^r*(2^weightBits*2^r)) := by
      simpa [rowNumerator] using keep.sum_le_card_nsmul _ _ (fun d _ => one d)
    _ ≤ 2^k*(2^r*(2^weightBits*2^r)) := Nat.mul_le_mul_right _ hkeep
    _ = _ := by rw [show 2*r=r+r by omega]; simp only [pow_add]; ac_rfl
  exact nonstrict.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

omit [Fintype V] in
/-- Every signed subtotal in a Walsh row of this table is bounded by the same
unsigned total. This also bounds partial butterfly sums over a subset. -/
theorem signed_subtotal_bound (r : ℕ) (W : Fin (r+1) → V → ℕ)
    (keep : Finset V) (sign : V → Bool) :
    |∑ d∈keep, if sign d then (differenceNumerator r W d : ℤ) else -(differenceNumerator r W d : ℤ)| ≤
      (rowNumerator r W keep : ℤ) := by
  calc
    _ ≤ ∑ d∈keep, |if sign d then (differenceNumerator r W d : ℤ) else -(differenceNumerator r W d : ℤ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      simp only [rowNumerator,Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp

end
end Hierarchy.DescentIntegerScale

end OAI
