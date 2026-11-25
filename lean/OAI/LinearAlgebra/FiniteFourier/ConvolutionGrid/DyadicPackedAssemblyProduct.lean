import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.PackedAssemblyProduct
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.DyadicPrimeGrid

/-! # Packed grid multiplication at the dyadic primes -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace ConvolutionGrid

open Deformation Matrix Polynomial
open scoped Classical BigOperators

variable {R T : Type*} [CommRing R] [CommRing T]
variable {σ O : Type*} [CommRing O] [Nontrivial O] [Fintype σ] {p : σ → ℕ} [∀ i, Fact (p i).Prime]
  {C : ∀ i, PrimeAxisOrbit (p i)} {u : σ → Oˣ} {hm : ∀ i, IsUnit ((p i-1 : ℕ) : O)}

local notation "Addr" => fun s : Finset σ => Dyadic.Address (fun i : s => p (Subtype.val i)-1)

/-- If each split endpoint returns the binomial product of its active axes,
the paired grid circuits return the cyclic product over the original residues. -/
theorem exists_dyadicGridCircuits (axis : ∀ i, DyadicPrimeAxis O (p i) (C i) (u i) (hm i))
    {φ : R →+* T} {η : T} {M : T[X]} {e r : ℕ} {H : Finset σ → ℕ}
    (ψ : O →+* JetQuotient M r) {a d : ℝ} {b c : Finset σ → ℝ}
    (hC : JetMatrixCircuit φ η M e r (columns fun i => (axis i).forward.map ψ) a)
    (hD : JetMatrixCircuit φ η M e r (columns fun i => (axis i).backward.map ψ) d)
    {f : ∀ s, (Addr s → JetQuotient M r) → (Addr s → JetQuotient M (H s))}
    {g : ∀ s, (Addr s → JetQuotient M (H s)) → (Addr s → JetQuotient M r)}
    (hf : ∀ s, JetStage φ η M e r (H s) (f s) (b s))
    (hg : ∀ s, JetStage φ η M e (H s) r (g s) (c s))
    (hsg : ∀ s (x y : Addr s → JetQuotient M r), g s (f s x * f s y) =
      multiply (Dyadic.coeff (fun i : s => ψ ((axis i.val).beta : O)) (fun i : s => p i.val-1)) x y) :
    HasGridProductCircuits φ η M (∀ i, ZMod (p i)) e r (fun k : Σ s, Addr s => H k.1)
      (2*a+d+∑ s, (2*b s+c s)) := by
  apply exists_sectorProductCircuits (sectorEquiv (K := fun i => Fin (p i-1))) hC hD hf hg
  intro x y z hz
  apply dyadic_grid_recover axis ψ x y z
  intro s
  exact (hz s).trans (hsg s _ _)

end ConvolutionGrid

end FiniteFourier
end LinearAlgebra
end OAI
