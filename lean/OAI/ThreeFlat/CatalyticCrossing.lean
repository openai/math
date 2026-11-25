import OAI.LinearAlgebra.SpectralBooks.FinitePlaneCriterion
import OAI.ThreeFlat.CrossingGeometry
import OAI.ThreeFlat.CrossingSupply
import OAI.LinearAlgebra.SpectralBooks.WireIdentity

namespace OAI
/-! # Catalytic straightening of a packet of crossings

For a four-terminal crossing, a fixed ratio of catalyst width suffices at
arbitrarily small selector rate. An integer unit of the width vector here
represents an actual binary wire in the six-party site tensor.
-/

open scoped BigOperators
namespace ThreeFlat

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor LinearAlgebra.SpectralBooks.ChordGraph CrossingSupply

/-- For precision parameter q, a packet at scale b has crossing width 4qb,
a surplus of 2b bits per numbered pair, and horizontal input and output width
4qbR. The integer multiplicities describe each summand's wiring. -/
theorem exists_catalytic_crossing_tile {F : Type*} [Field F]
    (hno : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 3))))
    (q : ℕ) (hq : 0 < q) :
    ∃ R : ℕ, 4 ≤ R ∧ ∀ {η : ℝ}, 0 < η → ∀ N : ℕ,
      ∃ b s : ℕ, N < b ∧ (s : ℝ) ≤ η * b ∧
        let T := raw F (b • demand q R)
        ∃ L : ℕ, L ≤ 2 ^ s ∧ ∃ z : Fin L → (∀ i, T.Leg i) → F,
          T.coeff = ∑ k, z k ∧ ∀ k, ∃ n : SupplyChoice → ℕ, ∑ j, n j = b ∧
            ({T with coeff := z k} : Raw (Fin 6) F).Restricts
              (raw F (∑ j, n j • supply q R j)) := by
  have hτ : 0 < 1 / (4 * (q : ℝ)) := by positivity
  obtain ⟨R, hR, bound⟩ := exists_catalytic_crossing_price hno hτ
  refine ⟨R, hR, fun hη N => exists_finite_wire_tile F _ _ (fun φ => ?_) hη N⟩
  let d := rawWireDistance φ 1
  obtain ⟨X, met, P, x, complete, geo, hd, _⟩ :=
    SpectralPlacementPrices.realize_finite_point_geodesic φ 1 zero_le_one
  let p : CrossingPlacement F := {
    carrier := X, prices := P, cat := P.catZero geo, A := x 4, B := x 5, x := x ∘ site }
  apply exists_cost_cover d (rawWireDistance_symm φ 1) (rawWireDistance_self φ 1 zero_le_one)
    q R hq (by omega)
  have h := bound p
  dsimp only [p, CrossingPlacement.d, CrossingPlacement.phase, CrossingPlacement.excess,
    xDemand, xSide, xMass, phaseCorr, Function.comp_apply] at h
  have ha (i : Fin 4) : dist (x 4) (x (site i)) = d (site i) 4 :=
    (dist_comm _ _).trans (hd _ _)
  have hb (i : Fin 4) : dist (x 5) (x (site i)) = d (site i) 5 :=
    (dist_comm _ _).trans (hd _ _)
  simp_rw [ha, hb, hd] at h
  exact h

end ThreeFlat

end OAI
