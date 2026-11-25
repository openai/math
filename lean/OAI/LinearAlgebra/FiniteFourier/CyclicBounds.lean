import OAI.LinearAlgebra.FiniteFourier.FourierTheorem

/-! # Finite cyclic transforms with the constants of the group theorem -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter
open scoped Topology

universe u v

/-- The forward upper estimate gives the inverse estimate with exactly the
same constant over every admissible ground field. -/
theorem UniformFourierUpper.both (h : UniformFourierUpper.{u,v}) {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (G : Type u) (K : Type v) [AddCommGroup G] [Fintype G] [Field K],
      Admissible G K → 2 ≤ Fintype.card G →
      let N : ℝ := Fintype.card G
      let U := C * N * (1 + Real.logb 2 N) ^ ((1 : ℝ)/2 + ε)
      (complexity (fourierMatrix G K) : ℝ) ≤ U ∧
        (complexity (inverseFourierMatrix G K) : ℝ) ≤ U := by
  obtain ⟨C, hC, bound⟩ := h ε hε
  refine ⟨C, hC, fun G K _ _ _ had hN => ?_⟩
  have hf := bound G K had hN
  exact ⟨hf, by rwa [complexity_inverseFourierMatrix G K had]⟩

/-- Upper bounds for the usual positive- and negative-phase DFTs in any
ground field with the specified primitive root. -/
theorem UniformFourierUpper.cyclic (h : UniformFourierUpper.{0,v}) {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (K : Type v) [Field K] (n : ℕ) [NeZero n] (ζ : K),
      IsPrimitiveRoot ζ n → 2 ≤ n →
      let U := C * n * (1 + Real.logb 2 n) ^ ((1 : ℝ)/2 + ε)
      (complexity (dftMatrix n ζ) : ℝ) ≤ U ∧ (complexity (inverseDftMatrix n ζ) : ℝ) ≤ U := by
  obtain ⟨C, hC, bound⟩ := h.both hε
  refine ⟨C, hC, fun K _ n _ ζ hζ hn => ?_⟩
  simpa only [ZMod.card, complexity_dftMatrix hζ, complexity_inverseDftMatrix hζ] using
    bound (ZMod n) K (admissible_zmod hζ) (by simpa only [ZMod.card] using hn)

/-- In cyclic coordinates the same constants work for all orders, fields,
primitive roots, forward and inverse DFTs, and geometric-border feedback systems. -/
theorem FourierComplexityTheorem.cyclic (h : FourierComplexityTheorem.{0,v}) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (K : Type v) [Field K] (n : ℕ) [NeZero n] (ζ : K), IsPrimitiveRoot ζ n → 2 ≤ n →
      let lower := c * n * Real.sqrt (Real.logb 2 n)
      let upper := C * n * (1 + Real.logb 2 n) ^ ((1 : ℝ)/2 + ε)
      (lower ≤ complexity (dftMatrix n ζ) ∧ (complexity (dftMatrix n ζ) : ℝ) ≤ upper) ∧
      (lower ≤ complexity (inverseDftMatrix n ζ) ∧
        (complexity (inverseDftMatrix n ζ) : ℝ) ≤ upper) ∧
      ∀ S : ℕ, (GeometricBorderAtMost (dftMatrix n ζ) S ∨
        GeometricBorderAtMost (inverseDftMatrix n ζ) S) → lower ≤ S := by
  obtain ⟨c, hc, hu⟩ := h
  refine ⟨c, hc, fun ε hε => ?_⟩
  obtain ⟨C,hC,hf⟩ := hu ε hε
  refine ⟨C,hC,?_⟩
  intro K _ n _ ζ hζ hn
  have hmain := hf (ZMod n) K (admissible_zmod hζ) (by simpa using hn)
  dsimp only at hmain ⊢
  rw [ZMod.card] at hmain
  rw [complexity_dftMatrix hζ, complexity_inverseDftMatrix hζ]
  refine ⟨hmain.1, hmain.2.1, fun S hS => hmain.2.2 S ?_⟩
  simpa only [← reindex_fourierMatrix_zmod hζ, ← reindex_inverseFourierMatrix_zmod hζ,
    geometricBorderAtMost_reindex_iff] using hS

/-- The same vanishing exponent describes the actual positive- and
negative-phase DFTs for any choices of primitive roots at growing orders. -/
theorem FourierComplexityTheorem.cyclic_vanishing_exponent (h : FourierComplexityTheorem.{0,v})
    {ι : Type*} (K : ι → Type v) [∀ i, Field (K i)]
    (n : ι → ℕ) [∀ i, NeZero (n i)] (ζ : ∀ i, K i) (hζ : ∀ i, IsPrimitiveRoot (ζ i) (n i))
    {l : Filter ι} (hn : Tendsto n l atTop) :
    ∃ η : ι → ℝ, Tendsto η l (𝓝 0) ∧ ∀ᶠ i in l,
      let size := (n i : ℝ) * (Real.logb 2 (n i)) ^ ((1 : ℝ)/2 + η i)
      (complexity (dftMatrix (n i) (ζ i)) : ℝ) = size ∧
        (complexity (inverseDftMatrix (n i) (ζ i)) : ℝ) = size := by
  simpa only [ZMod.card, fun i => complexity_dftMatrix (hζ i),
    fun i => complexity_inverseDftMatrix (hζ i)] using
    h.vanishing_exponent (fun i => ZMod (n i)) K (fun i => admissible_zmod (hζ i))
      (by simpa only [ZMod.card] using hn)

end FiniteFourier
end LinearAlgebra
end OAI
