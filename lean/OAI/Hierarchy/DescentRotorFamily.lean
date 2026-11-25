import OAI.Hierarchy.DescentRotorTables
import OAI.Hierarchy.NonlinearExpanders

namespace OAI
/-! # Uniform configured rotors on the dyadic spectral expander sequence -/

namespace Hierarchy.DescentRotor
open LinearAlgebra.SpectralBooks ThreeFlat
open RouteUnits Expander NonlinearExpanders
open scoped BigOperators
noncomputable section

/-- The incidence charge includes both exposed rows per site. Its coefficient is
independent of the number of sites, chosen row width, and tensor power. Directed
arcs of the host are counted with their full multiplicities. -/
theorem host_charge {n h : ℕ} (G : Graph n h) (C w u : ℕ) :
    Fintype.card (Arc G.arcs) * (C*w*u) + 2*(2^n)*(w*u) =
      (h*C+2)*(2^n)*w*u := by
  have card : Fintype.card (Arc G.arcs) = 2^n*h := by
    change Fintype.card (Σ ij : Fin (2^n) × Fin (2^n), Fin (G.arcs ij.1 ij.2))=_
    rw [Fintype.card_sigma,Fintype.sum_prod_type]
    simp [G.regular]
  rw [card]
  ring

/-- The expander family gives simultaneous finite-table configurations for every
permutation, at arbitrarily large dyadic orders with one common supply degree
and one common bit multiplicity. -/
theorem rotors_of_family {F : Type} [Field F] (family : SpectralFamily F) :
    ∃ (h C : ℕ), 0<h ∧ ∀ n₀ : ℕ, ∃ n ≥ n₀, ∃ G : Graph n h,
      ∃ width₀ : ℕ, ∀ w ≥ width₀, ∀ π : Equiv.Perm (Fin (2^n)),
        Configures F G.arcs C w π := by
  obtain ⟨h,γ,hh,hγ,data⟩ := family
  obtain ⟨K,hK⟩ := exists_nat_ge (160*γ/h)
  refine ⟨h,2*K+2,hh,fun n₀ => ?_⟩
  obtain ⟨n,hn,G,scalar,spectral⟩ := data n₀
  exact ⟨n,hn,G,configured_of_covers <|
    cloud_covers_of_expansion (F:=F) (Nat.two_pow_pos n) hh hγ hK G.arcs scalar spectral⟩

end
end Hierarchy.DescentRotor

end OAI
