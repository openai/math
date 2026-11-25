import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleBudget
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleDiagonal
import OAI.LinearAlgebra.FiniteFourier.PrimeRectanglePencilAction
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleChargedCompiler
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleFreeCompiler
import OAI.LinearAlgebra.FiniteFourier.PrimeRoutedUniformPencil

/-! # Recursive cost of the labeled ordinary query pencil

A weighted identity on labels cancels the off-diagonal transfers. Compiling the
common transform once per charged rectangle and the two endpoint transforms
once per free incidence gives the per-stage call bound.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
namespace PrimeRectangleSystem
open scoped Classical

variable {K : Type*} [CommRing K] {ℓ L v m b : ℕ} [Fact ℓ.Prime] [Invertible (ℓ : K)] {ζ : K}

/-- The entire clock pencil acts on independent labeled arrays. Its local work
is uniformly linear in one row volume and its recursive calls have the stated budget. -/
theorem realizesPencil (S : PrimeRectangleSystem K ℓ L v)
    (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] (p : PrimeRepairPencil ℓ m b hζ) :
    ∃ C : ℕ, ∀ f : ℕ, 0 < f → RealizesRows (primeConcreteStage hζ S p f)
      (C * Fintype.card (primeRowDigits ℓ m S.D f) +
        primePencilCalls ℓ L v m S.D (primePredictorRows ℓ m b) *
        ℓ ^ ((2 * (m + S.D - 1) - 1) * f) * complexity (primeTransform ℓ f ζ)) := by
  let G := S.geometry
  let Q (f : ℕ) (j : Fin m) := primeSpectrumQuery hζ
    (fun ω : G.RowAddress m f => primeCommonQueryExponents ω j)
  let T (f : ℕ) (a : (ZMod ℓ)ˣ) (j : Fin m) := ((Q f j) ^ (a : ZMod ℓ).val).toMatrix'
  let B (a : (ZMod ℓ)ˣ) (j : Fin m) := routedClockMatrix (fun β => p.A β j a)
  have h := routedPencil_uniform chargedEndpoint chargedEndpoint
    (fun r : FreeBitRectangle ℓ L v => bitSources r.val) (fun r => bitTargets r.val)
    S.chargedWeight S.freeWeight
    (fun v w => by
      by_cases e : v = w <;> simpa only [e, ite_true, ite_false] using S.identity v w)
    (routedClockMatrix p.A₀) B
    (fun f => G.transfer hζ f) T (fun f a j w => G.transfer_self hζ f a j w) (2 * S.D)
    (fun a r j => G.chargedRectangle_linearRowTemplate hζ r (S.chargedWeight r) (B a j) a j)
    (fun a r => G.freeRectangle_template hζ r (S.freeWeight r) (B a) a)
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun f hf => ?_⟩
  obtain ⟨c, hc, t, ht, program⟩ := hC f hf
  have hcalls : t ≤ primePencilCalls ℓ L v m S.D (primePredictorRows ℓ m b) := by
    apply ht.trans
    simpa only [Fintype.card_fin, primePredictorRows] using
      primePencilCalls_bound ℓ L v m S.D (primePredictorRows ℓ m b)
  apply realizesRows_routedQueryPencilStage (Q f) p.A₀ p.A (T f) (fun a j => by
    ext x y
    exact BitRoutingGeometry.toMatrixEntry_congr _ _ _ _ _ _ _)
  obtain ⟨n, hn, circ, hmat⟩ := program.compile
  exact ⟨n, hn.trans (Nat.add_le_add hc
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcalls))), circ, hmat⟩

end PrimeRectangleSystem
end

end

end FiniteFourier
end LinearAlgebra
end OAI
