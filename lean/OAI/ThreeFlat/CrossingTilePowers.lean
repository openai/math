import OAI.ThreeFlat.TilingBudget
import OAI.ThreeFlat.CrossingRemainder
import OAI.LinearAlgebra.SpectralBooks.RepeatWireTile
import OAI.ThreeFlat.TilingArithmetic

namespace OAI
/-! # Repetition of a fixed six-terminal crossing tile -/

open scoped BigOperators
namespace ThreeFlat

open Filter LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor LinearAlgebra.SpectralBooks.ChordGraph CrossingSupply

/-- A fixed crossing packet suffices for all sufficiently large widths, with selector
alphabet the words of tile labels and the remainder routed through a single site. -/
theorem eventually_crossing_of_fixed_tile {F : Type*} [Field F] {q R b s L : ℕ} {ε η : ℝ}
    (hqpos : 0 < q) (hR : 2 ≤ R) (hb : 0 < b) (hε : 0 < ε) (hη : 0 < η)
    (hεq : 1 ≤ ε*q) (hs : (s:ℝ) ≤ η*b) (hL : L ≤ 2^s)
    (z : Fin L → (∀ i, (raw F (b • demand q R)).Leg i) → F)
    (hz : (raw F (b • demand q R)).coeff = ∑ l, z l)
    (terms : ∀ l, ∃ n : SupplyChoice → ℕ, ∑ j, n j = b ∧
      ({raw F (b • demand q R) with coeff := z l} : Raw (Fin 6) F).Restricts
        (raw F (∑ j, n j • supply q R j))) :
    ∀ᶠ w : ℕ in atTop,
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
  choose n hn hrest using terms
  filter_upwards [eventually_tiling_budgets hqpos hb hε hη hεq hs] with w hw
  let t := w / (4*q*b)
  let r := w % (4*q*b)
  obtain ⟨heq,hsel,hadd⟩ := hw
  change 4*q*b*t+r = w at heq
  let U (j : Fin L) := ∑ k, n j k • supply q R k
  have tiled := repeat_wire_tile F (b • demand q R) (crossDemand r R) (remainderSupply r R)
    t U z hz hrest (remainder_restricts F r R)
  rw [repeat_demand_add, heq] at tiled
  obtain ⟨Z,hZ,restrict⟩ := tiled
  refine ⟨Fin t → Fin L, inferInstance, s*t, ?_, hsel, Z, hZ, ?_⟩
  · calc
      Fintype.card (Fin t → Fin L) = L^t := by simp
      _ ≤ (2^s)^t := Nat.pow_le_pow_left hL t
      _ = 2^(s*t) := (pow_mul _ _ _).symm
  intro j
  obtain ⟨u,v,H,huv,harm,h4,h5,hgraph⟩ :=
    tiled_supply_budgets q R b t r L (by omega) n hn j
  refine ⟨u,v,2*b*t+r,H,by omega,hadd,harm,heq ▸ h4,heq ▸ h5,?_⟩
  simpa only [U, remainderSupply, hgraph] using restrict j

end ThreeFlat

end OAI
