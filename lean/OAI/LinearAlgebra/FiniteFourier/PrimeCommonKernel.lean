import OAI.LinearAlgebra.FiniteFourier.PrimeQueryTuple
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The ordinary prime query in common coordinates

Each column carries a pair of vectors in the common space. All coordinates
outside the selected query travel unchanged. Paired changes of basis leave
this kernel invariant, even if the two changes of basis are different.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

variable {K : Type*} [CommRing K] {ℓ : ℕ} [NeZero ℓ] [Invertible (ℓ : K)] {ζ : K}
variable {C V W T : Type*} [Fintype C]
variable [AddCommGroup V] [Module (ZMod ℓ) V] [AddCommGroup W] [Module (ZMod ℓ) W]

/-- Two active vectors in each column and the spectator address. -/
abbrev PrimeCommonAddress (C V T : Type*) := ((C → V) × (C → V)) × T

open scoped Classical in
/-- Ordinary kernel of an invertible query power on a common space of dimension
`D`. The source is the second matrix index and the target is the first. -/
def primeCommonKernel (hζ : IsPrimitiveRoot ζ ℓ)
    (B : V →ₗ[ZMod ℓ] V →ₗ[ZMod ℓ] ZMod ℓ) (a : (ZMod ℓ)ˣ) (D : ℕ) :
    Matrix (PrimeCommonAddress C V T) (PrimeCommonAddress C V T) K :=
  fun o i => if i.2 = o.2 then (⅟(ℓ : K)) ^ (Fintype.card C * D) *
    digitPhase hζ ((↑(a⁻¹) : ZMod ℓ) * ∑ c, B (i.1.1 c - o.1.1 c) (o.1.2 c - i.1.2 c))
    else 0

/-- Change the two active coordinates in every column by the same pair of
maps. The spectator address is retained. -/
def primeCommonChart (p q : V ≃ₗ[ZMod ℓ] W) :
    PrimeCommonAddress C V T ≃ PrimeCommonAddress C W T :=
  ((Equiv.piCongrRight fun _ => p.toEquiv).prodCongr
    (Equiv.piCongrRight fun _ => q.toEquiv)).prodCongr (Equiv.refl T)

/-- An identification by paired bases sends the ordinary kernel to the kernel
of the induced pairing. In particular the same common matrix can be used for
every label, with different coordinate permutations. -/
theorem primeCommonKernel_chart (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ) (D : ℕ)
    (A : V →ₗ[ZMod ℓ] V →ₗ[ZMod ℓ] ZMod ℓ) (B : W →ₗ[ZMod ℓ] W →ₗ[ZMod ℓ] ZMod ℓ)
    (p q : V ≃ₗ[ZMod ℓ] W) (hpq : ∀ x y, B (p x) (q y) = A x y) :
    (primeCommonKernel (C := C) (T := T) hζ B a D).submatrix (primeCommonChart p q)
      (primeCommonChart p q) = primeCommonKernel hζ A a D := by
  classical
  ext o i
  change (if i.2 = o.2 then _ * digitPhase hζ (_ * ∑ c,
    B (p (i.1.1 c) - p (o.1.1 c)) (q (o.1.2 c) - q (i.1.2 c))) else _) = _
  simp only [← map_sub, hpq, primeCommonKernel]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
