import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Integer numerators for the pack means

A fixed finite rational candidate distribution admits integer weights with
one positive denominator. Uniform deck posttranslation makes its mean
independent of the destination tile. Consequently the running mean
numerator needs only one weighted sum of the candidate bin totals per pack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckMean

variable {J B G : Type*} [Fintype J]

/-- Common natural numerators for a finite rational probability distribution,
including candidates of probability zero. Their sum is the denominator. -/
theorem common_probability_denominator (prob : J → ℚ) (hn : ∀ c, 0 ≤ prob c)
    (hs : ∑ c, prob c = 1) :
    ∃ (P : ℕ) (pnum : J → ℕ), 0 < P ∧ ∑ c, pnum c = P ∧
      (∀ c, prob c = (pnum c : ℚ)/P) ∧ ∀ c, pnum c ≤ P := by
  let P := ∏ c, (prob c).den
  let pnum (c : J) := (prob c).num.natAbs * (P / (prob c).den)
  have hp : 0 < P := Finset.prod_pos (fun c _ => (prob c).den_pos)
  have hcast (c : J) : (pnum c : ℚ) = P * prob c := by
    have hdiv : (prob c).den ∣ P :=
      Finset.dvd_prod_of_mem (fun j : J => (prob j).den) (Finset.mem_univ c)
    have habs : ((prob c).num.natAbs : ℚ) = ((prob c).num : ℚ) := by
      simpa only [Int.cast_natCast] using congrArg (fun n : ℤ => (n : ℚ))
        (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr (hn c)))
    dsimp only [pnum]
    rw [Nat.cast_mul,Nat.cast_div_charZero hdiv,habs]
    calc
      _ = (P : ℚ) * (((prob c).num : ℚ) / (prob c).den) := by ring
      _ = _ := by rw [Rat.num_div_den]
  have hsum : ∑ c, pnum c = P := by
    have he : (∑ c, (pnum c : ℚ)) = P := by simp_rw [hcast]; rw [← Finset.mul_sum,hs,mul_one]
    exact_mod_cast he
  refine ⟨P,pnum,hp,hsum,?_,?_⟩
  · intro c
    apply (eq_div_iff (Nat.cast_ne_zero.mpr hp.ne')).mpr
    rw [hcast,mul_comm]
  · intro c
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (pnum j)) (Finset.mem_univ c)).trans_eq hsum

variable [Fintype G]

/-- The integer weighted bin total over all candidate motions and deck tiles. -/
def weighted (pnum : J → ℕ) (counts : J → B → G → ℕ) (b : B) : ℕ :=
  ∑ c, pnum c * ∑ g, counts c b g

/-- The weighted total is bounded by the common bin bound times the mass of
the integer candidate weights. -/
theorem weighted_le (pnum : J → ℕ) (counts : J → B → G → ℕ) (b : B) {R : ℕ}
    (h : ∀ c, ∑ g, counts c b g ≤ R) : weighted pnum counts b ≤ (∑ c, pnum c) * R := by
  simpa only [weighted,Finset.sum_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun c _ => Nat.mul_le_mul_left (pnum c) (h c))

variable [Group G]

/-- Expectation at tile `x` of an independently uniform deck translation of
the candidate chosen with rational probability `prob`. -/
def mean (prob : J → ℚ) (counts : J → B → G → ℕ) (b : B) (x : G) : ℚ :=
  ∑ c, prob c * ((∑ h, (counts c b (h*x) : ℚ)) / Fintype.card G)

/-- Deck averaging removes the dependence on the destination tile. -/
theorem mean_eq (prob : J → ℚ) (counts : J → B → G → ℕ) (b : B) (x : G) :
    mean prob counts b x = ∑ c, prob c * ((∑ g, (counts c b g : ℚ)) / Fintype.card G) := by
  apply Finset.sum_congr rfl
  intro c _
  have he : (∑ h, (counts c b (h*x) : ℚ)) = ∑ g, (counts c b g : ℚ) :=
    Equiv.sum_comp (Equiv.mulRight x) (fun g => (counts c b g : ℚ))
  rw [he]

/-- Multiplication by the candidate denominator times the deck order clears
the exact mean to its weighted natural numerator. -/
theorem scaled_mean {P : ℕ} (hp : 0 < P) {prob : J → ℚ} {pnum : J → ℕ}
    (hprob : ∀ c, prob c = (pnum c : ℚ)/P) (counts : J → B → G → ℕ) (b : B) (x : G) :
    ((P * Fintype.card G : ℕ) : ℚ) * mean prob counts b x = (weighted pnum counts b : ℚ) := by
  have hP : (P : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hG : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  simp only [mean_eq,weighted,Nat.cast_mul,Nat.cast_sum,Finset.mul_sum,hprob]
  apply Finset.sum_congr rfl
  intro c _
  field_simp
  exact Finset.mul_sum ..

/-- Updating the prior numerator by one weighted table computes exactly the
scaled sum of the previous mean and the new pack mean. -/
theorem scaled_update {P : ℕ} (hp : 0 < P) {prob : J → ℚ} {pnum : J → ℕ}
    (hprob : ∀ c, prob c = (pnum c : ℚ)/P) (counts : J → B → G → ℕ)
    (old : B → ℕ) (base : B → ℚ)
    (hbase : ∀ b, ((P * Fintype.card G : ℕ) : ℚ) * base b = old b) (b : B) (x : G) :
    ((P * Fintype.card G : ℕ) : ℚ) * (base b + mean prob counts b x) =
      ((old b + weighted pnum counts b : ℕ) : ℚ) := by
  rw [mul_add,hbase,scaled_mean hp hprob,Nat.cast_add]

/-- Summing the weighted numerators of any prefix of packs gives the exact
scaled accumulated mean, even for different candidate weights sharing a denominator. -/
theorem scaled_prefix {A : Type*} (s : Finset A) {P : ℕ} (hp : 0 < P)
    {prob : A → J → ℚ} {pnum : A → J → ℕ}
    (hprob : ∀ a c, prob a c = (pnum a c : ℚ)/P) (counts : A → J → B → G → ℕ) (b : B) (x : G) :
    ((P * Fintype.card G : ℕ) : ℚ) * (∑ a ∈ s, mean (prob a) (counts a) b x) =
      ((∑ a ∈ s, weighted (pnum a) (counts a) b : ℕ) : ℚ) := by
  rw [Finset.mul_sum,Nat.cast_sum]
  exact Finset.sum_congr rfl fun a _ => scaled_mean hp (hprob a) (counts a) b x

end PackedDeckMean

end BorderVNP
end Computability
end OAI
