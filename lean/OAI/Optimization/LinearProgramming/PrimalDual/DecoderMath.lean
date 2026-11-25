import OAI.Optimization.LinearProgramming.PrimalDual.Finite
import OAI.Optimization.LinearProgramming.PrimalDual.Bits

/-! Values and bit bounds at the boundaries of the numeric decoder passes. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open Matrix RAM
open scoped BigOperators

/-- Zero-extended view of a finite vector on a scalar tape. -/
def vectorWord {n : Nat} (x : Fin n → ℚ) (k : Nat) : ℚ :=
  if h : k < n then x ⟨k,h⟩ else 0

@[simp] theorem vectorWord_fin {n : Nat} (x : Fin n → ℚ) (i : Fin n) : vectorWord x i.val = x i := by
  simp [vectorWord]

def partialDot {n : Nat} (x y : Fin n → ℚ) (k : Nat) : ℚ :=
  ∑ i ∈ Finset.range k, vectorWord x i * vectorWord y i

@[simp] theorem partialDot_zero {n : Nat} (x y : Fin n → ℚ) : partialDot x y 0 = 0 := by simp [partialDot]

theorem partialDot_succ {n : Nat} (x y : Fin n → ℚ) (k : Nat) :
    partialDot x y (k+1) = partialDot x y k + vectorWord x k * vectorWord y k := by
  simp [partialDot,Finset.sum_range_succ]

@[simp] theorem partialDot_full {n : Nat} (x y : Fin n → ℚ) : partialDot x y n = x ⬝ᵥ y := by
  simp [partialDot, ← Fin.sum_univ_eq_sum_range,dotProduct]

/-- Binary sizes needed for charging the maximum of all accumulator states. -/
def dotWidth (n U V : Nat) := 3+2*n*(U+V+1)
def differenceWidth (B : Nat) := 3+4*B

theorem partialDot_bits {n : Nat} (x y : Fin n → ℚ) {U V : Nat}
    (hx : ∀ i, ratBits (x i) ≤ U) (hy : ∀ i, ratBits (y i) ≤ V)
    (k : Nat) (hk : k ≤ n) : ratBits (partialDot x y k) ≤ dotWidth n U V := by
  apply (ratBits_partial_dot_le (Finset.range k) (vectorWord x) (vectorWord y)).trans
  have hsum : (∑ i ∈ Finset.range k, (ratBits (vectorWord x i)+ratBits (vectorWord y i)+1)) ≤ k*(U+V+1) := by
    calc
      _ ≤ ∑ _ ∈ Finset.range k, (U+V+1) := Finset.sum_le_sum fun i hi => by
        have h : i < n := (Finset.mem_range.mp hi).trans_le hk
        simpa [vectorWord,h] using Nat.add_le_add_right (Nat.add_le_add (hx ⟨i,h⟩) (hy ⟨i,h⟩)) 1
      _ = _ := by simp
  have h := hsum.trans (Nat.mul_le_mul_right _ hk)
  unfold dotWidth; rw [Nat.mul_assoc]; omega

/-- A common bit limit for the input, difference, dot product, all their partial
sums/products, and division by the ray denominator. -/
def decoderLimit (d H : Nat) := 8*(dotWidth d H (differenceWidth H)+differenceWidth H+H+1)+10

theorem decoderLimit_bounds (d H : Nat) :
    H ≤ decoderLimit d H ∧ 3 ≤ decoderLimit d H ∧ differenceWidth H ≤ decoderLimit d H ∧
    dotWidth d H H ≤ decoderLimit d H ∧ dotWidth d H (differenceWidth H) ≤ decoderLimit d H ∧
    1+2*(H+H) ≤ decoderLimit d H ∧ 1+2*(H+differenceWidth H) ≤ decoderLimit d H ∧
    3+4*dotWidth d H (differenceWidth H)+2*differenceWidth H ≤ decoderLimit d H := by
  have hdw : H ≤ differenceWidth H := by unfold differenceWidth; omega
  have hd : dotWidth d H H ≤ dotWidth d H (differenceWidth H) := by
    unfold dotWidth
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  have he : differenceWidth H = 3+4*H := rfl
  unfold decoderLimit
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- The sign of the normalizing divisor and the resulting unboundedness certificate
are derived from the actual joint Farkas multiplier. -/
theorem certified_ray {m d : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c x₀ : Fin d → ℚ) (h₀ : A *ᵥ x₀ ≤ b) (s : JointRow (Fin m) (Fin d) → ℚ)
    (hs : SparseCertificate (jointMatrix A b c) (jointRhs b c) s) :
    let f := equationMultiplier s
    let den := c ⬝ᵥ f
    den < 0 ∧ A *ᵥ (fun j => f j / den) ≤ 0 ∧ c ⬝ᵥ (fun j => f j / den) = 1 := by
  obtain ⟨hdual,hprimal,hneg⟩ := joint_certificate A b c s hs.annihilates hs.negative
  have hl := fun i => hs.nonnegative (.inl i)
  have hm := fun i => hs.nonnegative (.inr (.inl i))
  have ht := hs.nonnegative (.inr (.inr (.inr (.inr ()))))
  have den := (negative_ray_denominator h₀ hl hm ht hdual hprimal hneg).2
  have out := ray_of_multipliers h₀ hl hm ht hdual hprimal hneg
  exact ⟨den,by simpa only [div_eq_inv_mul,Pi.smul_def,smul_eq_mul] using out⟩

end PrimalDual
end LinearProgramming
end Optimization
end OAI
