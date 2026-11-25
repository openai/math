import OAI.LinearAlgebra.FiniteFourier.TensorGrouping
import OAI.LinearAlgebra.FiniteFourier.ProtectedScalarDescent
import OAI.LinearAlgebra.FiniteFourier.ProtectedCyclotomicRoots
import OAI.LinearAlgebra.FiniteFourier.IntegerCircuitAction

/-! # Recovering bounded-width integral tensor circuits

The two coefficient rings need only provide circuits for local matrices in the
image of the integers. The binary constant is uniform over the prime set
selected by clearing the denominators of the ternary circuit.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- Bounded-width grid estimate after mapping prescribed integer factors into
the coefficient ring. -/
def IntegerImageGridTensorEstimate (R : Type*) [CommRing R] (lo hi : ℕ) (β C : ℝ) : Prop :=
  ∀ (k : ℕ) (n : Fin k → ℕ), (∀ i, lo ≤ n i ∧ n i ≤ hi) →
    ∀ A : (i : Fin k) → Matrix (Fin (n i)) (Fin (n i)) ℤ,
      (complexity (gridTensor (fun i => (A i).map (Int.castRingHom R))) : ℝ) ≤
        C * (↑(∏ i, n i) : ℝ) * (1 + (k : ℝ))^β

/-- Recover grids of any permitted widths using the two cyclotomic circuits. -/
theorem boundedGridTensorEstimate_of_protectedGrids {lo hi : ℕ} {β B T : ℝ}
    (hβ : 0 ≤ β) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (ternary : IntegerImageGridTensorEstimate (ProtectedCyclotomic {2} 9) lo hi β T)
    (binary : ∀ L : Finset ℕ, (∀ l ∈ L, Nat.Prime l) → (∀ l ∈ L, Odd l) →
      IntegerImageGridTensorEstimate (ProtectedCyclotomic L 8) lo hi β B) :
    BoundedGridTensorEstimate ℤ lo hi β (72*T + 32*B + 11) := by
  intro k n hn A
  let V := (↑(∏ i, n i) : ℝ)
  let w := (1 + (k : ℝ))^β
  have hV : 0 ≤ V := Nat.cast_nonneg _
  have hw : 1 ≤ w := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) k]) hβ
  have realize (R : Type) [CommRing R] (c : ℝ) (h : IntegerImageGridTensorEstimate R lo hi β c) :
      RealizableAtMost ((gridTensor A).map (Int.castRingHom R)) ⌊c*V*w⌋₊ := by
    have hmap : (gridTensor A).map (Int.castRingHom R) =
        gridTensor (fun i => (A i).map (Int.castRingHom R)) := by
      ext x y
      simp [gridTensor]
    rw [← complexity_le_iff, hmap]
    exact Nat.le_floor (h k n hn A)
  obtain ⟨s, hs, p, hp⟩ := integralCircuit_of_protectedCyclotomic (gridTensor A)
    (realize (ProtectedCyclotomic {2} 9) T ternary)
    (fun L hL ho => realize (ProtectedCyclotomic L 8) B (binary L hL ho))
  have hm := (complexity_le_iff (gridTensor A) s).mpr ⟨s, le_rfl, p, hp⟩
  apply (Nat.cast_le (α := ℝ) |>.mpr hm).trans
  simp only [Fintype.card_pi, Fintype.card_fin] at hs
  have h : (s : ℝ) ≤ 72 * (⌊T*V*w⌋₊ : ℝ) + 32 * (⌊B*V*w⌋₊ : ℝ) + 11 * V := by
    dsimp only [V]
    exact_mod_cast hs
  change (s : ℝ) ≤ _ * V * w
  have hT' := Nat.floor_le (show 0 ≤ T*V*w by positivity)
  have hB' := Nat.floor_le (show 0 ≤ B*V*w by positivity)
  nlinarith only [h, hT', hB', mul_le_mul_of_nonneg_left hw hV]

/-- The integral tensor estimate for all widths `2 ≤ n ≤ d` follows from
protected-ring estimates for the integer grids of widths `4 ≤ n ≤ d²`. -/
theorem integralTensorEstimate_of_protectedPairs {d : ℕ} {β B T : ℝ} (hd : 2 ≤ d)
    (hβ : 0 ≤ β) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (ternary : IntegerImageGridTensorEstimate (ProtectedCyclotomic {2} 9) 4 (d^2) β T)
    (binary : ∀ L : Finset ℕ, (∀ l ∈ L, Nat.Prime l) → (∀ l ∈ L, Odd l) →
      IntegerImageGridTensorEstimate (ProtectedCyclotomic L 8) 4 (d^2) β B) :
    BoundedGridTensorEstimate ℤ 2 d β (2 * (72*T + 32*B + 11)) :=
  boundedGridTensorEstimate_of_paired hd hβ (by positivity)
    (boundedGridTensorEstimate_of_protectedGrids hβ hB hT ternary binary)

/-- Execute the witness on an arbitrary abelian group, counting every
prescribed integer scaling (including readouts) and every addition. -/
theorem BoundedGridTensorEstimate.integerCircuit {lo hi : ℕ} {β C : ℝ} (hβ : 0 ≤ β)
    (h : BoundedGridTensorEstimate ℤ lo hi β C) (k : ℕ) (n : Fin k → ℕ)
    (hn : ∀ i, lo ≤ n i ∧ n i ≤ hi) (A : (i : Fin k) → Matrix (Fin (n i)) (Fin (n i)) ℤ) :
    ∃ (s : ℕ) (p : Circuit ℤ (∀ i, Fin (n i)) (∀ i, Fin (n i)) s),
      p.matrix = gridTensor A ∧
      (p.integerCost : ℝ) ≤ (3*C + 1) * (↑(∏ i, n i) : ℝ) * (1 + (k : ℝ))^β ∧
      ∀ (G : Type*) [AddCommGroup G] (x : (∀ i, Fin (n i)) → G) (o : ∀ i, Fin (n i)),
        p.evalGroup x o = ∑ i, gridTensor A o i • x i := by
  obtain ⟨s, hs, p, hp⟩ := realizableAtMost_complexity (gridTensor A)
  refine ⟨s, p, hp, ?_, fun G _ x o => by rw [Circuit.evalGroup_eq_sum, hp]⟩
  let V := (↑(∏ i, n i) : ℝ)
  let w := (1 + (k : ℝ))^β
  have hw : 1 ≤ w := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) k]) hβ
  have hs' : (s : ℝ) ≤ C * V * w := (Nat.cast_le (α := ℝ) |>.mpr hs).trans (h k n hn A)
  have hg := p.integerCost_le
  simp only [Fintype.card_pi, Fintype.card_fin] at hg
  have hc : (p.integerCost : ℝ) ≤ 3 * s + V := by
    dsimp only [V]
    exact_mod_cast hg
  change (p.integerCost : ℝ) ≤ (3*C + 1) * V * w
  nlinarith only [hc, hs', mul_le_mul_of_nonneg_left hw (show 0 ≤ V from Nat.cast_nonneg _)]

end FiniteFourier
end LinearAlgebra
end OAI
