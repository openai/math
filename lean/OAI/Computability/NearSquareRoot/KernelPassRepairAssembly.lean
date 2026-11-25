import OAI.Computability.NearSquareRoot.KernelPassFrequency
import OAI.Computability.NearSquareRoot.KernelRepairCoordinates
import OAI.Computability.NearSquareRoot.KernelPencilCoordinates
import OAI.Computability.NearSquareRoot.KernelPencilSpectralTable

/-! # Spectral action of the finite Hermite pass program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Plan

open Matrix Finset

variable {A h w s : ℕ} {I J : Type*}

/-- Frequency values of the independent data lanes in a chosen enumeration. -/
def slice (e : I → Fin w) (y : Addr A h) (x : Bank A h w) : I → ℚ :=
  fun i => frequency x (e i) y

theorem slice_add (e : I → Fin w) (y : Addr A h) (x z : Bank A h w) :
    slice e y (x + z) = slice e y x + slice e y z := by
  funext i
  exact congrFun (Matrix.mulVec_add _ (x (e i)) (z (e i))) y

theorem slice_sub (e : I → Fin w) (y : Addr A h) (x z : Bank A h w) :
    slice e y (x - z) = slice e y x - slice e y z := by
  funext i
  exact congrFun (Matrix.mulVec_sub _ (x (e i)) (z (e i))) y

theorem slice_smul (e : I → Fin w) (y : Addr A h) (q : ℚ) (x : Bank A h w) :
    slice e y (q • x) = q • slice e y x := by
  funext i
  exact congrFun (Matrix.mulVec_smul _ q (x (e i))) y

open CyclotomicCode PencilDyadicMix PencilDescent

/-- At one frequency the compiler executes the rational matrix polynomial on
the flattened rows. The two correction blocks use separate scatter maps from
the original extension table, after expansion to its dyadic basis. -/
theorem slice_hermite [Fintype I] [Fintype J]
    (ei : I → Fin w) (ej : J → Fin s) (y : Addr A h)
    (p : Plan A w w) (g : Plan A w s) (c : Plan A s w) (t : Plan A (s+s) (s+s))
    (B : Matrix I I ℚ) (G : Matrix J I ℚ) (C : Matrix I J ℚ)
    (T₁₁ T₁₂ T₂₁ T₂₂ : Matrix J J ℚ)
    (hp : ∀ x, slice ei y (p.applyAt h x) = B *ᵥ slice ei y x)
    (hg : ∀ x, slice ej y (g.applyAt h x) = G *ᵥ slice ei y x)
    (hc : ∀ x, slice ei y (c.applyAt h x) = C *ᵥ slice ej y x)
    (ht₁ : ∀ u v, slice ej y (leftPart (t.applyAt h (Fin.append u v))) =
      T₁₁ *ᵥ slice ej y u + T₁₂ *ᵥ slice ej y v)
    (ht₂ : ∀ u v, slice ej y (rightPart (t.applyAt h (Fin.append u v))) =
      T₂₁ *ᵥ slice ej y u + T₂₂ *ᵥ slice ej y v)
    (x : Bank A h w) :
    let v := slice ei y x
    let pv := B *ᵥ v
    let u := C *ᵥ (T₁₁ *ᵥ (G *ᵥ pv) + T₁₂ *ᵥ (G *ᵥ v))
    let z := C *ᵥ (T₂₁ *ᵥ (G *ᵥ pv) + T₂₂ *ᵥ (G *ᵥ v))
    slice ei y ((hermite p g c t).applyAt h x) =
      pv - (1/2 : ℚ) • (B *ᵥ (B *ᵥ pv) - pv) - B *ᵥ u + z := by
  dsimp only
  rw [applyAt_hermite]
  let px := p.applyAt h x
  let out := t.applyAt h (Fin.append (g.applyAt h px) (g.applyAt h x))
  let u := c.applyAt h (leftPart out)
  let v := c.applyAt h (rightPart out)
  change slice ei y (px - (1/2 : ℚ) • (p.applyAt h (p.applyAt h px) - px) -
    p.applyAt h u + v) = _
  simp only [slice_add, slice_sub, slice_smul, px, out, u, v, hp, hg, hc, ht₁, ht₂]

theorem slice_iterate [Fintype I] [DecidableEq I] (ei : I → Fin w) (y : Addr A h)
    (p : Plan A w w) (M : Matrix I I ℚ)
    (hp : ∀ x, slice ei y (p.applyAt h x) = M *ᵥ slice ei y x)
    (b : ℕ) (x : Bank A h w) : slice ei y ((p.iterate b).applyAt h x) = M^b *ᵥ slice ei y x := by
  induction b with
  | zero => simp [iterate, applyAt_route]
  | succ b ih => rw [iterate, applyAt_seq, hp, ih, pow_succ', Matrix.mulVec_mulVec]

open PencilSearch PencilCoordinates RepairCoordinates

abbrev basisWidth (m : ℕ) := batchWidth m * 2^(batchExponent m)
abbrev basisChecks (m : ℕ) := batchChecks m * 2^(batchExponent m)

def stageMatrix {m : ℕ} (hm : 2 ≤ m) (k : Signature m) :=
  rationalStage (rowIndex m (clockDigits m) (clockPeriod m)) (batchPencil m hm) k

/-- Assemble all prediction and correction passes on extension basis rows. -/
def compiledBatch {m : ℕ} (hm : 2 ≤ m) (test : Column A → Signature m)
    (p : Plan A (basisWidth m) (basisWidth m)) : Plan A (basisWidth m) (basisWidth m) :=
  hermite (p.iterate (clockPeriod m))
    (rowMix A (.refl _) (.refl _) (generatedChecks m))
    (rowMix A (.refl _) (.refl _) (generatedChecks m)ᵀ)
    (spectralCheckTable test (batchTable m hm))

theorem calls_compiledBatch {m : ℕ} (hm : 2 ≤ m) (test : Column A → Signature m)
    (p : Plan A (basisWidth m) (basisWidth m)) :
    (compiledBatch hm test p).calls = 4*clockPeriod m*p.calls+4*basisChecks m*A := by
  simp only [compiledBatch, calls_hermite, calls_iterate, rowMix_calls, calls_spectralCheckTable,
    basisChecks]
  ring

/-- If a routed stage implements its query pencil, the generated fixed program
applies the exact product of all query signs on every independent data lane. -/
theorem frequency_compiledBatch {m : ℕ} (hm : 2 ≤ m) (test : Column A → Signature m)
    (p : Plan A (basisWidth m) (basisWidth m))
    (hp : ∀ (x : Bank A h (basisWidth m)) (y : Addr A h),
      frequencyRows (p.applyAt h x) y = stageMatrix hm (∑ j, test (y j)) *ᵥ frequencyRows x y)
    (x : Bank A h (basisWidth m)) (y : Addr A h) :
    frequencyRows ((compiledBatch hm test p).applyAt h x) y =
      (∏ t, (-1 : ℚ)^((∑ j, test (y j)) t).val) • frequencyRows x y := by
  let k := ∑ j, test (y j)
  let e := rowIndex m (clockDigits m) (clockPeriod m)
  let B := flattenRat (diagonal (generatedPrediction hm k))
  let H := generatedChecks m
  let t := batchTable m hm k
  have hb : ∀ v, slice finProdFinEquiv y ((p.iterate (clockPeriod m)).applyAt h v) =
      B *ᵥ slice finProdFinEquiv y v := by
    intro v
    rw [slice_iterate finProdFinEquiv y p (stageMatrix hm k) (fun z => hp z y)]
    exact congrArg (· *ᵥ slice finProdFinEquiv y v)
      (rationalStage_pow e _ (batchPencil_good m hm) k)
  apply Eq.trans (slice_hermite finProdFinEquiv finProdFinEquiv y _ _ _ _ B
    (flattenRat H) (flattenRat Hᵀ) (flattenRat t.toBlocks₁₁) (flattenRat t.toBlocks₁₂)
    (flattenRat t.toBlocks₂₁) (flattenRat t.toBlocks₂₂) hb
    (fun z => frequencyRows_rowMix H z y) (fun z => frequencyRows_rowMix Hᵀ z y)
    (fun u v => funext fun j => frequency_spectralCheck_left test (batchTable m hm) u v j y)
    (fun u v => funext fun j => frequency_spectralCheck_right test (batchTable m hm) u v j y) x)
  have he := action _ _ _ _ (generated_certificate hm k) (slice finProdFinEquiv y x)
  dsimp only at he
  rw [baseTarget_rat] at he
  exact he

end KernelPass.Plan

end NearSquareRoot
end Computability
end OAI
