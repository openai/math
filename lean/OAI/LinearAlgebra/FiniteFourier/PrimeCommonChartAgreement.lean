import OAI.LinearAlgebra.FiniteFourier.PrimeCommonCoordinates
import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointAuxiliary

/-! # Uniform spectator coordinates for the ordinary prime queries

Numbering the distinguished coordinates other than `j` by `j.succAbove`
identifies the common-kernel chart with the physical chart of the endpoint
factorization. In this ordering all query indices use the same address type.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

variable {ℓ m : ℕ} {C J U E L : Type*}

/-- Curry both tuples of ordinary addresses by columns. -/
def endpointDigitCurry :
    ((C × J → L) × (C × J → L)) ≃ EndpointDigitPairs C J L :=
  (Equiv.curry _ _ _).prodCongr (Equiv.curry _ _ _)

/-- Uniform numbering of both spectator arrays, skipping the selected slot. -/
def primeCommonUniformSpectators (j : Fin (m+1)) :
    PrimeCommonSpectators C j ℓ ≃ EndpointDigitPairs C (Fin m) (ZMod ℓ) :=
  let e := ((Equiv.refl C).prodCongr (finSuccAboveEquiv j).symm).arrowCongr (Equiv.refl (ZMod ℓ))
  (e.prodCongr e).trans endpointDigitCurry

/-- Converting the spectator to its uniform order turns the common-kernel
chart into the physical chart on curried ordinary digits. -/
theorem primeCommonQueryChart_uniform [AddCommGroup E] [Module (ZMod ℓ) E]
    (j : Fin (m+1)) (p q : E ≃ₗ[ZMod ℓ] ZMod ℓ × (U → ZMod ℓ)) :
    (primeCommonQueryChart (C := C) j (primeCommonLabelMap p) (primeCommonLabelMap q)).trans
      ((Equiv.refl _).prodCongr (primeCommonUniformSpectators j)) =
    endpointDigitCurry.trans (endpointQueryPhysicalChart j p.toEquiv q.toEquiv) := by
  ext x <;> rfl

/-- The two ordinary kernels agree after any bijection on the spectator
index, because the spectator only contributes an equality test. -/
theorem primeCommonKernel_reindex_spectator {K T T' : Type*} [CommRing K]
    [NeZero ℓ] [Invertible (ℓ : K)] [Fintype C] [AddCommGroup E] [Module (ZMod ℓ) E]
    {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (B : E →ₗ[ZMod ℓ] E →ₗ[ZMod ℓ] ZMod ℓ)
    (a : (ZMod ℓ)ˣ) (D : ℕ) (e : T ≃ T') :
    let r := (Equiv.refl ((C → E) × (C → E))).prodCongr e
    (primeCommonKernel (C := C) (T := T') hζ B a D).submatrix r r =
      primeCommonKernel (T := T) hζ B a D := by
  ext o i
  classical
  change (if e i.2 = e o.2 then _ else (0 : K)) = _
  rw [show e i.2 = e o.2 ↔ i.2 = o.2 from e.injective.eq_iff]
  rfl

/-- Pulling the common matrix back along the uniformly numbered physical
chart gives its ordinary matrix in the original digit coordinates. -/
theorem primeCommonKernel_physical {K : Type*} [CommRing K] [NeZero ℓ] [Invertible (ℓ : K)]
    [Fintype C] [AddCommGroup E] [Module (ZMod ℓ) E] {ζ : K}
    (hζ : IsPrimitiveRoot ζ ℓ) (B : E →ₗ[ZMod ℓ] E →ₗ[ZMod ℓ] ZMod ℓ)
    (a : (ZMod ℓ)ˣ) (D : ℕ) (j : Fin (m+1))
    (p q : E ≃ₗ[ZMod ℓ] ZMod ℓ × (U → ZMod ℓ)) :
    let physical := endpointDigitCurry.trans (endpointQueryPhysicalChart (C := C) j p.toEquiv q.toEquiv)
    let localChart := primeCommonQueryChart j (primeCommonLabelMap p) (primeCommonLabelMap q)
    (primeCommonKernel hζ B a D).submatrix physical physical =
      (primeCommonKernel hζ B a D).submatrix localChart localChart := by
  dsimp only
  rw [← primeCommonQueryChart_uniform j p q]
  let localChart := primeCommonQueryChart (C := C) j (primeCommonLabelMap p) (primeCommonLabelMap q)
  exact congrArg (fun M : Matrix _ _ K => M.submatrix localChart localChart)
    (primeCommonKernel_reindex_spectator (C := C) hζ B a D (primeCommonUniformSpectators j))

end

end

end FiniteFourier
end LinearAlgebra
end OAI
