import OAI.Computability.BorderVNP.TransferIntegerGraph

/-!
# Common source matrix orders in every characteristic

The two identities over the integers and the dyadic integers from §12
specialize in a commutative diagram of polynomial substitutions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open VPVNP VPVNP.HardnessCNF MvPolynomial

universe u

/-- For an integer weighted CNF family, the orders of the Hamiltonian-cycle and
permanent source matrices can both be fixed before specifying the field. -/
theorem uniform_matrix_projections_of_weightedCNF {V : ℕ → Type*}
    (p : ∀ n, MvPolynomial (V n) ℤ) {K : ℕ → ℕ} (φ : ∀ n, CNF (K n))
    (w : ∀ n, Projection ℤ (Fin (K n)) (V n))
    (hk : PolynomiallyBounded K) (hl : PolynomiallyBounded fun n => literalCount (φ n))
    (he : ∀ n, weightedCNF (φ n) (fun i => (w n i).elim X C) = p n) :
    ∃ jHC jPer : ℕ → ℕ, PolynomiallyBounded jHC ∧ PolynomiallyBounded jPer ∧
      (∀ n, 2 ≤ jHC n ∧ 2 ≤ jPer n) ∧
      (∀ n (F : Type u) [Field F], ∃ ρ : Projection F (Fin (jHC n) × Fin (jHC n)) (V n),
        ρ.hom (hamiltonianCyclePolynomial F (jHC n)) = map (Int.castRingHom F) (p n)) ∧
      (∀ n (F : Type u) [Field F] (q : ℕ) [CharP F q], q ≠ 2 →
        ∃ ρ : Projection F (Fin (jPer n) × Fin (jPer n)) (V n),
          ρ.hom (permanentPolynomial F (jPer n)) = map (Int.castRingHom F) (p n)) := by
  obtain ⟨r, t, hr, ht, hg⟩ := integral_graph_projections φ w hk hl
  refine ⟨r, t, hr, ht, fun n => ⟨(hg n).1, (hg n).2.1⟩, ?_, ?_⟩
  · intro n F _
    obtain ⟨ψ, hψ⟩ := (hg n).2.2.1
    let f := Int.castRingHom F
    exact ⟨castProjection f ψ, by
      simpa only [map_projection_hom, map_hamiltonianCyclePolynomial] using
        congrArg (map f) (hψ.trans (he n))⟩
  · intro n F _ q _ hq
    obtain ⟨ψ, hψ⟩ := (hg n).2.2.2
    let f := dyadicToField F q hq
    have h : f.comp (Int.castRingHom DyadicIntegers) = Int.castRingHom F := Subsingleton.elim ..
    exact ⟨castProjection f ψ, by
      simpa only [map_projection_hom, map_permanentPolynomial, he, map_map, h] using
        congrArg (map f) hψ⟩

end BorderVNP
end Computability
end OAI
