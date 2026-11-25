import OAI.Hierarchy.DescentIntegerRow
import OAI.Hierarchy.DescentMixingTrajectory

namespace OAI
/-! # Integral coefficients of the actual coupled level and overflow estimator -/

namespace Hierarchy.DescentIntegerScale

open DescentGL DescentBaseVariance
open scoped BigOperators Classical
noncomputable section

variable {A C : Type*} [Fintype A] [Fintype C] {bits : ℕ}
variable (levels : A → ℕ) (j : (a : A) → Fin (levels a) → ℕ) (hj : ∀ a s, j a s≤bits)
variable (cj : C → ℕ) (hcj : ∀ c, cj c ≤ bits)
variable (x : A → Bits bits → ℕ) (y : C → Bits bits → ℕ) (k B K : ℕ)

/-- The numerator of the paper's joint estimator coefficient. The leading
factor restores the `F*B` scale of the estimator. -/
def mixingWeightNumerator (l : Fin (bits+1)) (d : Bits bits) : ℕ :=
  (2^k*B)*((∑ a, ∑ s : Fin (levels a), 4*2^((s.val+7)/8)*
    (if l.val=j a s then natCorrelation (x a) d else 0)) +
    ∑ c, K^2*(if l.val=cj c then natCorrelation (y c) d else 0))

theorem mixingCollisionWeights_eq_integer (l : Fin (bits+1)) (d : Nonzero bits) :
    mixingCollisionWeights levels j hj cj hcj
      (fun a i => (x a i : ℝ) / ((2^k*B:ℕ):ℝ))
      (fun c i => (y c i : ℝ) / ((2^k*B:ℕ):ℝ)) k B K l d =
    (mixingWeightNumerator levels j cj x y k B K l d.val : ℝ) / ((2^k*B:ℕ):ℝ)^2 := by
  rw [mixingCollisionWeights_apply]
  have splitTerm (P : Prop) [Decidable P] (w a Q : ℝ) :
      w*(if P then a/Q else 0) = (w*(if P then a else 0))/Q := by
    split_ifs <;> simp [mul_div_assoc]
  simp only [normalized_autocorrelation]
  simp only [mixingWeightNumerator, Nat.cast_mul, Nat.cast_add,
    Nat.cast_pow, Nat.cast_sum, Nat.cast_ite, Nat.cast_ofNat, Nat.cast_zero, splitTerm,
    Finset.sum_div, add_div, mul_div_assoc]

/-- The table entries fit a number of bits additive in the bit widths of the
normalization, the number of charged terms, their weights, and twice their raw mass. -/
theorem mixingWeightNumerator_bound (l : Fin (bits+1)) (d : Bits bits)
    (scaleBits countBits weightBits massBits : ℕ)
    (scale : 2^k*B ≤ 2^scaleBits)
    (count : (∑ a,levels a)+Fintype.card C ≤ 2^countBits)
    (weight : ∀ a (s : Fin (levels a)), 4*2^((s.val+7)/8) ≤ 2^weightBits)
    (capacity : K^2 ≤ 2^weightBits)
    (loads : ∀ a,(∑ i,x a i) ≤ 2^massBits) (flows : ∀ c,(∑ i,y c i) ≤ 2^massBits) :
    mixingWeightNumerator levels j cj x y k B K l d ≤ 2^(scaleBits+countBits+weightBits+2*massBits) := by
  let limit := 2^weightBits*(2^massBits)^2
  have guarded (P : Prop) [Decidable P] (z : Bits bits → ℕ) (small : (∑ i,z i)≤2^massBits) :
      (if P then natCorrelation z d else 0) ≤ (2^massBits)^2 := by
    split_ifs
    · exact (correlation_le_mass_sq z d).trans (Nat.pow_le_pow_left small 2)
    · exact Nat.zero_le _
  have level (a : A) : (∑ s : Fin (levels a),4*2^((s.val+7)/8)*
      (if l.val=j a s then natCorrelation (x a) d else 0)) ≤ levels a * limit := by
    simpa using
      Finset.univ.sum_le_card_nsmul _ limit
        (fun (s : Fin (levels a)) _ => Nat.mul_le_mul (weight a s) (guarded _ _ (loads a)))
  have levelSum := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => level a)
  rw [←Finset.sum_mul] at levelSum
  have flowSum : (∑ c,K^2*(if l.val=cj c then natCorrelation (y c) d else 0)) ≤
      Fintype.card C * limit := by
    simpa using Finset.univ.sum_le_card_nsmul _ limit
      (fun (c : C) _ => Nat.mul_le_mul capacity (guarded _ _ (flows c)))
  unfold mixingWeightNumerator
  calc
    _ ≤ 2^scaleBits*(((∑ a,levels a)+Fintype.card C)*limit) := by
      rw [add_mul]
      exact Nat.mul_le_mul scale (Nat.add_le_add levelSum flowSum)
    _ ≤ 2^scaleBits*(2^countBits*limit) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ count)
    _ = _ := by rw [show 2*massBits=massBits+massBits by omega]; simp [limit,pow_add,pow_two,mul_assoc]


/-- This integer score uses the actual multilevel estimator, including all
propagated level charges and all pairwise overflow charges. -/
theorem mixingRowScore_eq_integer {h r : ℕ} (base : Layout ((h+1)+r)) (row : Row ((h+1)+r))
    (levels : A → ℕ) (j : (a : A) → Fin (levels a) → ℕ) (hj : ∀ a s, j a s≤(h+1)+r)
    (cj : C → ℕ) (hcj : ∀ c,cj c≤(h+1)+r)
    (x : A → Bits ((h+1)+r) → ℕ) (y : C → Bits ((h+1)+r) → ℕ) (k B K : ℕ) :
    let q := 2^k*B
    let W := fun l : Fin (r+1) => mixingWeightNumerator levels j cj x y k B K (Fin.natAdd (h+1) l)
    let weights := mixingCollisionWeights levels j hj cj hcj
      (fun a i => (x a i:ℝ)/q) (fun c i => (y c i:ℝ)/q) k B K
    conditionalRowScore base (fun l => weights (Fin.natAdd (h+1) l)) row =
      (rowNumerator r W (surviving base row):ℝ) / (denominator q r:ℝ) := by
  dsimp only
  have one (l : Fin (r+1)) : mixingCollisionWeights levels j hj cj hcj
      (fun a i => (x a i:ℝ)/((2^k*B:ℕ):ℝ)) (fun c i => (y c i:ℝ)/((2^k*B:ℕ):ℝ))
      k B K (Fin.natAdd (h+1) l) =
      (fun d : Nonzero ((h+1)+r) =>
        (mixingWeightNumerator levels j cj x y k B K (Fin.natAdd (h+1) l) d.val:ℝ) /
          ((2^k*B:ℕ):ℝ)^2) :=
    funext fun d => mixingCollisionWeights_eq_integer levels j hj cj hcj x y k B K _ d
  rw [funext one]
  exact conditionalRowScore_eq_integer _ _ _ _


/-- End-to-end unsigned word width for the actual integer row comparison. -/
theorem mixingRowNumerator_fits {h r : ℕ} (base : Layout ((h+1)+r)) (row : Row ((h+1)+r))
    (levels : A → ℕ) (j : (a : A) → Fin (levels a) → ℕ) (cj : C → ℕ)
    (x : A → Bits ((h+1)+r) → ℕ) (y : C → Bits ((h+1)+r) → ℕ) (k B K : ℕ)
    (scaleBits countBits weightBits massBits : ℕ)
    (scale : 2^k*B ≤ 2^scaleBits) (count : (∑ a,levels a)+Fintype.card C ≤ 2^countBits)
    (weight : ∀ a (s : Fin (levels a)), 4*2^((s.val+7)/8) ≤ 2^weightBits)
    (capacity : K^2 ≤ 2^weightBits)
    (loads : ∀ a,(∑ i,x a i) ≤ 2^massBits) (flows : ∀ c,(∑ i,y c i) ≤ 2^massBits) :
    let W := fun l : Fin (r+1) => mixingWeightNumerator levels j cj x y k B K (Fin.natAdd (h+1) l)
    rowNumerator r W (surviving base row) <
      2^(((h+1)+r)+2*r+(scaleBits+countBits+weightBits+2*massBits)+1) := by
  apply rowNumerator_bound
  · simpa only [card_bits] using (Finset.card_le_univ (surviving base row))
  · intro l d
    exact mixingWeightNumerator_bound levels j cj x y k B K _ d _ _ _ _ scale count weight capacity loads flows



end
end Hierarchy.DescentIntegerScale

end OAI
