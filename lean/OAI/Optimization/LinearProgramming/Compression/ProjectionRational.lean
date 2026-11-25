import OAI.Optimization.LinearProgramming.Compression.ProjectionCramer
import OAI.Optimization.LinearProgramming.Compression.ProjectionCuts

/-! # Clearing projected systems row by row

One common denominator covers the retained columns, eliminated columns, and
constant of each row. The number of rows is absent from the height bound. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype κ] {d : ℕ}

/-- A height for integer entries obtained by clearing one rational block row. -/
def clearedProjectionRowBound (k d B : ℕ) : ℕ := B ^ (k + d + 2)

/-- An exponent bounding the height of projected tests. Here `L` bounds the
bits of each reduced numerator and denominator before row clearing. -/
def projectionTestBitBound (k d L : ℕ) : ℕ :=
  let n := d + 1
  let u := L * (k + d + 2)
  n + ((n * n + (n + u * 2) * n) * 2 + u)

/-- The bounded affine tests used for a projection have polynomially many bits
even when the original system has exponentially many inequalities. -/
theorem projection_test_height_le_pow (k d B L : ℕ) (hB : B ≤ 2 ^ L) :
    projectionCoefficientBound d (clearedProjectionRowBound k d B) ≤
      2 ^ projectionTestBitBound k d L := by
  let n := d + 1
  let u := L * (k + d + 2)
  let C := clearedProjectionRowBound k d B
  have hC : C ≤ 2 ^ u := by
    apply (Nat.pow_le_pow_left hB (k + d + 2)).trans_eq
    exact (pow_mul 2 L (k + d + 2)).symm
  have hn : n ≤ 2 ^ n := n.lt_two_pow_self.le
  have hf : n.factorial ≤ 2 ^ (n * n) :=
    n.factorial_le_pow.trans <| (Nat.pow_le_pow_left hn n).trans_eq (pow_mul 2 n n).symm
  have hc : max 1 C ≤ 2 ^ u := max_le (Nat.one_le_two_pow) hC
  have hbase : n * max 1 C ^ 2 ≤ 2 ^ (n + u * 2) := by
    rw [pow_add 2 n (u * 2), pow_mul 2 u 2]
    exact Nat.mul_le_mul hn (Nat.pow_le_pow_left hc 2)
  have hmult : n.factorial * (n * max 1 C ^ 2) ^ n ≤ 2 ^ (n * n + (n + u * 2) * n) := by
    rw [pow_add 2 (n * n) ((n + u * 2) * n), pow_mul 2 (n + u * 2) n]
    exact Nat.mul_le_mul hf (Nat.pow_le_pow_left hbase n)
  change n * ((n.factorial * (n * max 1 C ^ 2) ^ n) ^ 2 * C) ≤
    2 ^ (n + ((n * n + (n + u * 2) * n) * 2 + u))
  rw [pow_add 2 n _, pow_add 2 ((n * n + (n + u * 2) * n) * 2) u,
    pow_mul 2 (n * n + (n + u * 2) * n) 2]
  exact Nat.mul_le_mul hn (Nat.mul_le_mul (Nat.pow_le_pow_left hmult 2) hC)

private theorem sum_scaled_coefficients {j : Type*} [Fintype j] (q : j → ℚ) (a : j → ℤ)
    (D : ℕ) (h : ∀ i, (a i : ℚ) = (D : ℚ) * q i) (v : j → ℝ) :
    (∑ i, (a i : ℝ) * v i) = (D : ℝ) * ∑ i, (q i : ℝ) * v i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (a i : ℝ) = (D : ℝ) * (q i : ℝ) := by
    exact_mod_cast h i
  rw [hi, mul_assoc]

/-- Clear each complete block row, including its constant. The integer system
has exactly the same feasible pairs (and hence exactly the same projections). -/
theorem exists_integer_projection_system (G : Matrix ι κ ℚ) (H : Matrix ι (Fin d) ℚ)
    (c : ι → ℚ) {B : ℕ}
    (hG : ∀ i j, (G i j).num.natAbs ≤ B ∧ (G i j).den ≤ B)
    (hH : ∀ i j, (H i j).num.natAbs ≤ B ∧ (H i j).den ≤ B)
    (hc : ∀ i, (c i).num.natAbs ≤ B ∧ (c i).den ≤ B) :
    ∃ (G' : Matrix ι κ ℤ) (H' : Matrix ι (Fin d) ℤ) (c' : ι → ℤ),
      (∀ i j, (G' i j).natAbs ≤ clearedProjectionRowBound (Fintype.card κ) d B) ∧
      (∀ i j, (H' i j).natAbs ≤ clearedProjectionRowBound (Fintype.card κ) d B) ∧
      (∀ i, (c' i).natAbs ≤ clearedProjectionRowBound (Fintype.card κ) d B) ∧
      ∀ (x : κ → ℝ) (y : Fin d → ℝ),
        (H.map (Rat.cast : ℚ → ℝ) *ᵥ y ≤ (fun i => (c i : ℝ)) - G.map (Rat.cast : ℚ → ℝ) *ᵥ x) ↔
        H'.map (Int.cast : ℤ → ℝ) *ᵥ y ≤ (fun i => (c' i : ℝ)) - G'.map (Int.cast : ℤ → ℝ) *ᵥ x := by
  classical
  let row (i : ι) : Option (κ ⊕ Fin d) → ℚ := fun j => j.elim (c i) (Sum.elim (G i) (H i))
  have hrow (i : ι) (j : Option (κ ⊕ Fin d)) :
      (row i j).num.natAbs ≤ B ∧ (row i j).den ≤ B := by
    obtain _ | j := j
    · exact hc i
    · cases j with
      | inl j => exact hG i j
      | inr j => exact hH i j
  choose D a hD _ ha using fun i =>
    clear_bounded_row (row i) (fun j => (hrow i j).1) (fun j => (hrow i j).2)
  let G' : Matrix ι κ ℤ := fun i j => a i (some (.inl j))
  let H' : Matrix ι (Fin d) ℤ := fun i j => a i (some (.inr j))
  let c' := fun i => a i none
  have bound (i : ι) (j : Option (κ ⊕ Fin d)) :
      (a i j).natAbs ≤ clearedProjectionRowBound (Fintype.card κ) d B := by
    simpa [clearedProjectionRowBound, Nat.add_assoc] using (ha i j).2
  refine ⟨G', H', c', (fun i j => bound i (some (.inl j))),
    (fun i j => bound i (some (.inr j))), (fun i => bound i none), ?_⟩
  intro x y
  change (∀ i, (∑ j, (H i j : ℝ) * y j) ≤ (c i : ℝ) - ∑ j, (G i j : ℝ) * x j) ↔
    ∀ i, (∑ j, (H' i j : ℝ) * y j) ≤ (c' i : ℝ) - ∑ j, (G' i j : ℝ) * x j
  apply forall_congr'
  intro i
  have hG' := sum_scaled_coefficients (G i) (G' i) (D i) (fun j => (ha i (some (.inl j))).1) x
  have hH' := sum_scaled_coefficients (H i) (H' i) (D i) (fun j => (ha i (some (.inr j))).1) y
  have hc' : (c' i : ℝ) = (D i : ℝ) * (c i : ℝ) := by
    exact_mod_cast (show (c' i : ℚ) = (D i : ℚ) * c i from (ha i none).1)
  rw [hG', hH', hc', ← mul_sub]
  exact (mul_le_mul_iff_right₀ (show (0 : ℝ) < D i by exact_mod_cast hD i)).symm

/-- Relabeling the eliminated coordinates by a finite ordinal preserves the
projection. This gives the integer presentation expected by the cut theorem. -/
private theorem integer_projection_presentation {ν : Type*} [Fintype ν]
    (G : Matrix ι κ ℚ) (H : Matrix ι ν ℚ) (c : ι → ℚ) {B : ℕ}
    (hG : ∀ i j, (G i j).num.natAbs ≤ B ∧ (G i j).den ≤ B)
    (hH : ∀ i j, (H i j).num.natAbs ≤ B ∧ (H i j).den ≤ B)
    (hc : ∀ i, (c i).num.natAbs ≤ B ∧ (c i).den ≤ B) :
    ∃ (G' : Matrix ι κ ℤ) (H' : Matrix ι (Fin (Fintype.card ν)) ℤ) (c' : ι → ℤ),
      (∀ i j, (G' i j).natAbs ≤ clearedProjectionRowBound (Fintype.card κ) (Fintype.card ν) B) ∧
      (∀ i j, (H' i j).natAbs ≤ clearedProjectionRowBound (Fintype.card κ) (Fintype.card ν) B) ∧
      (∀ i, (c' i).natAbs ≤ clearedProjectionRowBound (Fintype.card κ) (Fintype.card ν) B) ∧
      ∀ x : κ → ℝ, (∃ y, H.map (Rat.cast : ℚ → ℝ) *ᵥ y ≤
          (fun i => (c i : ℝ)) - G.map (Rat.cast : ℚ → ℝ) *ᵥ x) ↔
        ∃ y, H'.map (Int.cast : ℤ → ℝ) *ᵥ y ≤
          (fun i => (c' i : ℝ)) - G'.map (Int.cast : ℤ → ℝ) *ᵥ x := by
  classical
  let e := Fintype.equivFin ν
  let Hf : Matrix ι (Fin (Fintype.card ν)) ℚ := H.submatrix id e.symm
  have remap (v : ν → ℝ) :
      Hf.map (Rat.cast : ℚ → ℝ) *ᵥ (v ∘ e.symm) = H.map (Rat.cast : ℚ → ℝ) *ᵥ v := by
    funext i
    exact e.symm.sum_comp (fun j => (H i j : ℝ) * v j)
  obtain ⟨G', H', c', hGI, hHI, hcI, hequiv⟩ :=
    exists_integer_projection_system G Hf c hG (fun i j => hH i (e.symm j)) hc
  refine ⟨G', H', c', hGI, hHI, hcI, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    exact ⟨y ∘ e.symm, (hequiv x (y ∘ e.symm)).mp ((remap y).symm ▸ hy)⟩
  · rintro ⟨z, hz⟩
    refine ⟨z ∘ e, ?_⟩
    rw [← remap (z ∘ e)]
    simpa [Function.comp_def] using (hequiv x z).mpr hz

/-- Preserving every bounded affine integer test preserves membership in the
projection of a rational inequality system with any finite coordinate sets.
The height bound depends only on the retained and eliminated dimensions and
the heights of individual input coefficients. -/
theorem rational_projection_of_preserving_affine_tests [Fintype ι] {ν : Type*} [Fintype ν]
    (G : Matrix ι κ ℚ) (H : Matrix ι ν ℚ) (c : ι → ℚ) {B : ℕ}
    (hG : ∀ i j, (G i j).num.natAbs ≤ B ∧ (G i j).den ≤ B)
    (hH : ∀ i j, (H i j).num.natAbs ≤ B ∧ (H i j).den ≤ B)
    (hc : ∀ i, (c i).num.natAbs ≤ B ∧ (c i).den ≤ B) {x x' : κ → ℝ}
    (hx : ∃ y, H.map (Rat.cast : ℚ → ℝ) *ᵥ y ≤
      (fun i => (c i : ℝ)) - G.map (Rat.cast : ℚ → ℝ) *ᵥ x)
    (tests : ∀ (a : κ → ℤ) (b : ℤ), (∀ j, (a j).natAbs ≤
        projectionCoefficientBound (Fintype.card ν)
          (clearedProjectionRowBound (Fintype.card κ) (Fintype.card ν) B)) →
      b.natAbs ≤ projectionCoefficientBound (Fintype.card ν)
        (clearedProjectionRowBound (Fintype.card κ) (Fintype.card ν) B) →
      (∑ j, (a j : ℝ) * x j) ≤ b → (∑ j, (a j : ℝ) * x' j) ≤ b) :
    ∃ y, H.map (Rat.cast : ℚ → ℝ) *ᵥ y ≤
      (fun i => (c i : ℝ)) - G.map (Rat.cast : ℚ → ℝ) *ᵥ x' := by
  obtain ⟨G', H', c', hGI, hHI, hcI, hequiv⟩ :=
    integer_projection_presentation G H c hG hH hc
  exact (hequiv x').mpr <| projection_of_preserving_affine_tests G' H' c' hGI hHI hcI
    ((hequiv x).mp hx) tests

/-- A rational projection is the intersection of its valid integer half-spaces
of the displayed bounded height, independently of the number of input rows. -/
theorem rational_projection_iff_bounded_cuts [Fintype ι] {ν : Type*} [Fintype ν]
    (G : Matrix ι κ ℚ) (H : Matrix ι ν ℚ) (c : ι → ℚ) {B : ℕ}
    (hG : ∀ i j, (G i j).num.natAbs ≤ B ∧ (G i j).den ≤ B)
    (hH : ∀ i j, (H i j).num.natAbs ≤ B ∧ (H i j).den ≤ B)
    (hc : ∀ i, (c i).num.natAbs ≤ B ∧ (c i).den ≤ B) (x : κ → ℝ) :
    (∃ y, H.map (Rat.cast : ℚ → ℝ) *ᵥ y ≤
        (fun i => (c i : ℝ)) - G.map (Rat.cast : ℚ → ℝ) *ᵥ x) ↔
      ∀ (a : κ → ℤ) (b : ℤ), (∀ j, (a j).natAbs ≤ projectionCoefficientBound
        (Fintype.card ν) (clearedProjectionRowBound (Fintype.card κ) (Fintype.card ν) B)) →
      b.natAbs ≤ projectionCoefficientBound (Fintype.card ν)
        (clearedProjectionRowBound (Fintype.card κ) (Fintype.card ν) B) →
      (∀ (u : κ → ℝ) (v : ν → ℝ), H.map (Rat.cast : ℚ → ℝ) *ᵥ v ≤
          (fun i => (c i : ℝ)) - G.map (Rat.cast : ℚ → ℝ) *ᵥ u →
        (∑ j, (a j : ℝ) * u j) ≤ b) → (∑ j, (a j : ℝ) * x j) ≤ b := by
  constructor
  · rintro ⟨y, hy⟩ a b _ _ h
    exact h x y hy
  · intro tests
    obtain ⟨G', H', c', hGI, hHI, hcI, hequiv⟩ :=
      integer_projection_presentation G H c hG hH hc
    apply (hequiv x).mpr
    by_contra h
    obtain ⟨a, b, ha, hb, hvalid, hcut⟩ :=
      exists_bounded_projection_cut G' H' c' hGI hHI hcI x h
    apply hcut.not_ge
    apply tests a b ha hb
    intro u v hv
    obtain ⟨z, hz⟩ := (hequiv u).mp ⟨v, hv⟩
    exact hvalid u z hz

end Compression
end LinearProgramming
end Optimization
end OAI
