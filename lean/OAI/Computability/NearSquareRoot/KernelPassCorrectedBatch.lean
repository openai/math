import OAI.Computability.NearSquareRoot.KernelPassOuterCorrection
import OAI.Computability.NearSquareRoot.KernelBinaryQueryRational

/-! # Correct normalized binary transforms on the entire batch

The two zero-call endpoint passes are selected once, independently of the
address width. Their ordinary column operators restore the signs and the
exchange in the quadratic Fourier product.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Plan

open BinaryQuery PencilSearch

variable {m u N : ℕ} {L : Type*}

private noncomputable def frontPass (m u : ℕ) : Plan (Arity m u) 1 1 :=
  (outer_passes m u).choose

private noncomputable def backPass (m u : ℕ) : Plan (Arity m u) 1 1 :=
  (outer_passes m u).choose_spec.choose

noncomputable def correctedLabelBatch (hm : 2 ≤ m) (e : L ≃ Fin N)
    (p : Plan (Arity m u) (N*basisWidth m) (N*basisWidth m)) :
    Plan (Arity m u) (N*basisWidth m) (N*basisWidth m) :=
  wrap (frontPass m u) (backPass m u) (compiledLabelBatch hm e (fun _ => test m u) p)

theorem calls_correctedLabelBatch (hm : 2 ≤ m) (e : L ≃ Fin N)
    (p : Plan (Arity m u) (N*basisWidth m) (N*basisWidth m)) :
    (correctedLabelBatch hm e p).calls = 4*clockPeriod m*p.calls+4*N*basisChecks m*Arity m u := by
  obtain ⟨hf, hb, _, _⟩ := (outer_passes m u).choose_spec.choose_spec
  rw [correctedLabelBatch, frontPass, backPass, calls_wrap _ _ _ hf hb, calls_compiledLabelBatch]

/-- A joint routed stage with its authentic spectral action gives a correct
finite pass template for every paired column width and every independent row. -/
theorem correctedLabelBatch_correct (hm : 2 ≤ m) (hodd : m ≡ 1 [MOD 2]) (e : L ≃ Fin N)
    (p : Plan (Arity m u) (N*basisWidth m) (N*basisWidth m))
    (hp : ∀ h v (x : Bank (Arity m u) h (N*basisWidth m)) (y : Addr (Arity m u) h),
      labelSlice e v y (p.applyAt h x) =
        (stageMatrix hm (∑ j, test m u (y j))).mulVec (labelSlice e v y x)) :
    Correct (correctedLabelBatch hm e p) := by
  obtain ⟨_, _, hf, hb⟩ := (outer_passes m u).choose_spec.choose_spec
  apply correct_wrap
  · exact fun h => compiledLabelBatch_mulVec hm e (test m u) p (hp h)
  · exact fun h => outer_kernel hodd _ _ hf hb _ (product_kernel m u h)

end KernelPass.Plan

end NearSquareRoot
end Computability
end OAI
