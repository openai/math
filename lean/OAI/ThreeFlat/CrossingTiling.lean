import OAI.ThreeFlat.CatalyticCrossing
import OAI.ThreeFlat.CrossingTilePowers

namespace OAI
/-! # Tiling all sufficiently large catalytic crossings

A width is partitioned into whole copies of a single fixed tile and a residual
packet. The residual horizontal wires travel through site zero. The residual
crossed wires consume the unused part of the allowance on the six pairs.
-/

open scoped BigOperators
namespace ThreeFlat

open Filter LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor LinearAlgebra.SpectralBooks.ChordGraph CrossingSupply

/-- Without a spectral three-flat the six-terminal catalytic crossing admits
the tiled decomposition at every sufficiently large width, simultaneously
with exact input/output capacities and arbitrarily small selector rate. -/
theorem eventually_catalytic_crossing {F : Type*} [Field F]
    (hno : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 3))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, 4 ≤ R ∧ ∀ {η : ℝ}, 0 < η → ∀ᶠ w : ℕ in atTop,
      let T := raw F (crossDemand w R)
      ∃ (J : Type) (_ : Fintype J) (s : ℕ), Fintype.card J ≤ 2^s ∧ (s : ℝ) ≤ η*w ∧
        ∃ z : J → (∀ i, T.Leg i) → F, T.coeff = ∑ l, z l ∧
          ∀ j, ∃ u v a : ℕ, ∃ H : Widths 6,
            u+v ≤ w ∧ (a : ℝ) ≤ ε*w ∧
            (∀ e : Chord 6, ¬ (e.1.1 < 4 ∧ 4 ≤ e.1.2) → H e = 0) ∧
            load 4 H = w*R ∧ load 5 H = w*R ∧
            ({T with coeff := z j} : Raw (Fin 6) F).Restricts
              (raw F (matching true u + matching false v + slack a + H)) := by
  classical
  obtain ⟨q,hq⟩ := exists_nat_gt (1/ε)
  have hεq : 1 ≤ ε*q := by linarith [(div_lt_iff₀ hε).mp hq]
  have hqpos : 0 < q := by exact_mod_cast (one_div_pos.mpr hε).trans hq
  obtain ⟨R,hR,tile⟩ := exists_catalytic_crossing_tile hno q hqpos
  refine ⟨R,hR,?_⟩
  intro η hη
  obtain ⟨b,s,hb,hs,L,hL,z,hz,terms⟩ := tile hη 0
  exact eventually_crossing_of_fixed_tile hqpos (by omega) hb hε hη hεq hs hL z hz terms


end ThreeFlat

end OAI
