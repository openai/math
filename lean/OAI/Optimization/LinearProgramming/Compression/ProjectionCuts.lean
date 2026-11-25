import OAI.Optimization.LinearProgramming.Compression.Projection

/-! Bounded affine tests for the projection of a finite system. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open Finset Matrix
open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}

/-- The coefficients and constant of every relevant projected integer cut have this bound. -/
def projectionCoefficientBound (d B : ℕ) : ℕ :=
  (d+1) * (projectionMultiplierBound d B * B)

/-- The logarithmic height of projected integer cuts is polynomial in dimension and input
coefficient bit length. -/
theorem projectionCoefficientBound_le_pow (d B L : ℕ) (hB : B ≤ 2^L) :
    projectionCoefficientBound d B ≤
      2 ^ ((d+1) + 2 * ((d+1)^2 + ((d+1) + 2*L) * (d+1)) + L) := by
  let n := d+1
  have hn : n ≤ 2^n := n.lt_two_pow_self.le
  have hm : max 1 B ≤ 2^L := max_le (Nat.one_le_pow _ _ (by decide)) hB
  have hf : n.factorial ≤ 2^(n*n) := by
    rw [pow_mul]
    exact n.factorial_le_pow.trans (Nat.pow_le_pow_left hn n)
  have hinner : n * (max 1 B)^2 ≤ 2^(n+2*L) := by
    calc
      _ ≤ 2^n * (2^L)^2 := Nat.mul_le_mul hn (Nat.pow_le_pow_left hm 2)
      _ = _ := by rw [← pow_mul, ← pow_add, Nat.mul_comm L 2]
  have hT : n.factorial * (n*(max 1 B)^2)^n ≤ 2^(n^2+(n+2*L)*n) := by
    calc
      _ ≤ 2^(n*n) * (2^(n+2*L))^n := Nat.mul_le_mul hf (Nat.pow_le_pow_left hinner n)
      _ = _ := by rw [← pow_mul, ← pow_add, pow_two]
  change n * ((n.factorial * (n * max 1 B ^ 2) ^ n)^2 * B) ≤ _
  calc
    _ ≤ 2^n * ((2^(n^2+(n+2*L)*n))^2 * 2^L) :=
      Nat.mul_le_mul hn (Nat.mul_le_mul (Nat.pow_le_pow_left hT 2) hB)
    _ = 2^(n + 2*(n^2+(n+2*L)*n) + L) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega

private theorem weighted_height {σ : Type*} [Fintype σ] (p a : σ → ℤ) {P B : ℕ}
    (hp : ∀ i, (p i).natAbs ≤ P) (ha : ∀ i, (a i).natAbs ≤ B) :
    (∑ i, p i * a i).natAbs ≤ Fintype.card σ * (P * B) := by
  suffices h : |∑ i, p i * a i| ≤ ((Fintype.card σ : ℕ) : ℤ) * ((P : ℤ) * (B : ℤ)) by
    exact_mod_cast (show ((∑ i, p i * a i).natAbs : ℤ) ≤ _ from (Int.natCast_natAbs _).symm ▸ h)
  calc
    _ ≤ ∑ i, |p i * a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : σ, (P : ℤ) * (B : ℤ) := by
      apply sum_le_sum
      intro i _
      rw [abs_mul, ← Int.natCast_natAbs, ← Int.natCast_natAbs]
      exact_mod_cast Nat.mul_le_mul (hp i) (ha i)
    _ = _ := by simp

omit [Fintype ι] in
/-- An affine combination of inequalities with nonnegative weights and zero hidden columns
is a valid inequality for the retained coordinates. -/
private theorem projected_cut_valid (G : Matrix ι κ ℤ) (H : Matrix ι (Fin d) ℤ)
    (c : ι → ℤ) (t : Finset ι) (p : t → ℤ) (hp : ∀ i, 0 ≤ p i)
    (hz : ∀ j, ∑ i : t, p i * H i j = 0) (x : κ → ℝ) (y : Fin d → ℝ)
    (hxy : H.map (Int.cast : ℤ → ℝ) *ᵥ y ≤
      (fun i => (c i : ℝ)) - G.map (Int.cast : ℤ → ℝ) *ᵥ x) :
    0 ≤ ∑ i : t, (p i : ℝ) * (c i - (G.map (Int.cast : ℤ → ℝ) *ᵥ x) i) := by
  let Ht : Matrix t (Fin d) ℝ := of fun i j => (H i j : ℝ)
  have hz' : Htᵀ *ᵥ (fun i : t => (p i : ℝ)) = 0 := by
    funext j
    have hj : ∑ i : t, (p i : ℝ) * (H i j : ℝ) = 0 := by exact_mod_cast hz j
    simpa [Ht, Matrix.mulVec, dotProduct, mul_comm] using hj
  exact projected_inequality_of_witness Ht _ y (fun i => hxy i)
    (fun i : t => (p i : ℝ)) (fun i => by change (0 : ℝ) ≤ (p i : ℝ); exact_mod_cast hp i) hz'

omit [Fintype ι] in
private theorem weighted_affine_residual (G : Matrix ι κ ℤ) (c : ι → ℤ) (t : Finset ι)
    (p : t → ℤ) (x : κ → ℝ) :
    (∑ i : t, (p i : ℝ) * ((c i : ℝ) - (G.map (Int.cast : ℤ → ℝ) *ᵥ x) i)) =
      ((∑ i : t, p i * c i : ℤ) : ℝ) -
      ∑ j, ((∑ i : t, p i * G i j : ℤ) : ℝ) * x j := by
  simp only [Int.cast_sum, Int.cast_mul, mul_sub, sum_sub_distrib, Matrix.mulVec,
    dotProduct, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm (f := fun i j => (p i : ℝ) * ((G i j : ℝ) * x j))]

/-- A point outside an integral projection is separated by an integer affine inequality
valid on the entire projection. Its height depends on the number of eliminated variables
and the row heights, and is independent of the number of rows. -/
theorem exists_bounded_projection_cut (G : Matrix ι κ ℤ) (H : Matrix ι (Fin d) ℤ)
    (c : ι → ℤ) {B : ℕ} (hG : ∀ i j, (G i j).natAbs ≤ B)
    (hH : ∀ i j, (H i j).natAbs ≤ B) (hc : ∀ i, (c i).natAbs ≤ B) (x : κ → ℝ)
    (hout : ¬ ∃ y, H.map (Int.cast : ℤ → ℝ) *ᵥ y ≤
      (fun i => (c i : ℝ)) - G.map (Int.cast : ℤ → ℝ) *ᵥ x) :
    ∃ (a : κ → ℤ) (b : ℤ), (∀ j, (a j).natAbs ≤ projectionCoefficientBound d B) ∧
      b.natAbs ≤ projectionCoefficientBound d B ∧
      (∀ (u : κ → ℝ) (v : Fin d → ℝ), H.map (Int.cast : ℤ → ℝ) *ᵥ v ≤
        (fun i => (c i : ℝ)) - G.map (Int.cast : ℤ → ℝ) *ᵥ u →
        (∑ j, (a j : ℝ) * u j) ≤ b) ∧ (b : ℝ) < ∑ j, (a j : ℝ) * x j := by
  obtain ⟨t, p, ht, hp, hz, hneg⟩ := bounded_integer_obstruction H _ hH hout
  have bound (f : t → ℤ) (hf : ∀ i, (f i).natAbs ≤ B) :
      (∑ i : t, p i * f i).natAbs ≤ projectionCoefficientBound d B := by
    apply (weighted_height p f (fun i => (hp i).2) hf).trans
    simpa [projectionCoefficientBound] using
      Nat.mul_le_mul_right (projectionMultiplierBound d B * B) ht
  refine ⟨fun j => ∑ i : t, p i * G i j, ∑ i : t, p i * c i,
    fun j => bound _ (fun i => hG i j), bound _ (fun i => hc i), ?_, ?_⟩
  · intro u v hv
    exact sub_nonneg.mp <| (weighted_affine_residual G c t p u) ▸
      projected_cut_valid G H c t p (fun i => (hp i).1) hz u v hv
  · change (∑ i : t, (p i : ℝ) * ((c i : ℝ) - (G.map (Int.cast : ℤ → ℝ) *ᵥ x) i)) < 0 at hneg
    exact sub_neg.mp <| (weighted_affine_residual G c t p x) ▸ hneg

/-- Preserving bounded affine tests preserves membership in an integer projection. -/
theorem projection_of_preserving_affine_tests (G : Matrix ι κ ℤ) (H : Matrix ι (Fin d) ℤ)
    (c : ι → ℤ) {B : ℕ} (hG : ∀ i j, (G i j).natAbs ≤ B) (hH : ∀ i j, (H i j).natAbs ≤ B)
    (hc : ∀ i, (c i).natAbs ≤ B) {x x' : κ → ℝ}
    (hx : ∃ y, H.map (Int.cast : ℤ → ℝ) *ᵥ y ≤ (fun i => (c i : ℝ)) - G.map (Int.cast : ℤ → ℝ) *ᵥ x)
    (tests : ∀ (a : κ → ℤ) (b : ℤ), (∀ j, (a j).natAbs ≤ projectionCoefficientBound d B) →
      b.natAbs ≤ projectionCoefficientBound d B → (∑ j, (a j : ℝ) * x j) ≤ b →
      (∑ j, (a j : ℝ) * x' j) ≤ b) :
    ∃ y, H.map (Int.cast : ℤ → ℝ) *ᵥ y ≤ (fun i => (c i : ℝ)) - G.map (Int.cast : ℤ → ℝ) *ᵥ x' := by
  by_contra h
  obtain ⟨a, b, ha, hb, hvalid, hviol⟩ := exists_bounded_projection_cut G H c hG hH hc x' h
  obtain ⟨y, hy⟩ := hx
  exact (hviol.not_ge <| tests a b ha hb (hvalid x y hy))

end Compression
end LinearProgramming
end Optimization
end OAI
