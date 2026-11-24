import OAI.Computability.VPVNP.CompressionState
import OAI.Computability.VPVNP.DegreeRefreshCosts
import OAI.Computability.VPVNP.LaneReindex

/-!
# Degree refresh on dyadic compression states

A degree-`2^a` state spends `a` of its binary lane coordinates on the ports
of the expander. The next state has degree `2^a₀` and the remaining `g`
lane coordinates. Its positions, energy and largest width are related to
the old state by the estimates of Section 7.3 on each admitted branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.Refresh

open NetworkKernel SpectralGeometry DegreeRefresh MotifConversion

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (X : State a (a + g))

/-- Split the consumed port coordinates from the remaining lanes of the state. -/
abbrev splitSlots := relane X.slots (splitBitWord a g)

/-- The original widths after the identical split of lane coordinates. -/
abbrev splitWidths := relaneWidths (splitBitWord a g) X.width

variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)

/-- Choices of local terms for the dyadic degree refresh, using the split slots and widths of
the current state. -/
abbrev DyadicRefreshChoice := BlockChoices (splitSlots X) (bitWordFinEquiv a) (splitWidths X) P hdH hconn F

/-- The degree-restored state uses the port as part of its new base label. -/
noncomputable def dyadicRefreshNext (c : DyadicRefreshChoice X P hdH hconn F) : State a₀ g where
  Base := X.Base × Fin (2 ^ a)
  baseFintype := inferInstance
  baseNonempty := inferInstance
  baseIndex := State.productIndex X.baseIndex (Equiv.refl (Fin (2 ^ a)))
  slots := degreeRefresh (splitSlots X) P.toSlotGraph hD hd
  width := actualWidths hd (bitWordFinEquiv a) (splitWidths X)
    (blockSupplyWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) P hdH hconn F c)

variable {R : Type*} [CommRing R] (κ : (parameterData F).Entry → R) (hκ : (parameterData F).IsSolution κ)

/-- The exact kernel over an arbitrary solution of the fixed parameter equations,
with every output of the kernel paired with its compression state. -/
noncomputable def dyadicRefreshPass : StatePass R X a₀ g where
  step := (expanderRefreshStep (splitSlots X) (bitWordFinEquiv a) (splitWidths X)
    P hdH hconn F κ hκ hD hd).reindexInput (relaneIso X.slots (splitBitWord a g) X.width)
  next := dyadicRefreshNext X P hdH hconn F hD hd
  output_eq _ := rfl

/-- Each old position stays at its own physical port. -/
theorem dyadicRefreshPass_place (c : DyadicRefreshChoice X P hdH hconn F)
    (x : X.Base × BitWord (a + g)) :
    (((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term c).place x) =
      refreshPositions (bitWordFinEquiv a) (x.1,splitBitWord a g x.2) := rfl

/-- The degree refresh preserves the exact number of positions on every branch. -/
theorem dyadicRefreshNext_positions (c : DyadicRefreshChoice X P hdH hconn F) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).positions = X.positions := by
  change Fintype.card ((X.Base × Fin (2 ^ a)) × BitWord g) = Fintype.card (X.Base × BitWord (a+g))
  let e := ((Equiv.refl X.Base).prodCongr (splitBitWord a g).toEquiv).trans
    (refreshPositions (bitWordFinEquiv a))
  exact (Fintype.card_congr e).symm

/-- Equation (7.3) with the energy and position count of the compression
state. The leading factor is `2^a₀ + 2 K'`, independent of the old degree
when the block is chosen by `exists_expander_parameters`. -/
theorem dyadicRefreshNext_energy (hK' : 0 ≤ K') (c : DyadicRefreshChoice X P hdH hconn F) :
    (dyadicRefreshNext X P hdH hconn F hD hd c).energy ≤
      ((2 ^ a₀ : ℕ) + 2 * K') * X.energy + F.energyConstant * X.positions ^ 2 := by
  have h := expander_branch_energy_le (splitSlots X) (bitWordFinEquiv a) (splitWidths X)
    P hdH hconn F hD hd hK' c
  dsimp only at h
  have hc : Fintype.card (X.Base × (BitWord a × BitWord g)) = X.positions :=
    relane_card_sites (V := X.Base) (splitBitWord a g)
  rw [hc, relane_sum_widths (splitBitWord a g) X.width
    (fun n ↦ (n : ℝ) ^ 2 / (1 / ((X.positions : ℝ) * (2 ^ a : ℕ))))] at h
  rw [State.energy, dyadicRefreshNext_positions]
  exact h

/-- The field bound of the degree refresh, stated on the full output state. -/
theorem dyadicRefreshNext_width (hK' : 0 ≤ K') (c : DyadicRefreshChoice X P hdH hconn F)
    {W : ℕ} (hW : ∀ e, X.width e ≤ W) (e : ((X.Base × Fin (2 ^ a)) × Fin (2 ^ a₀)) × BitWord g) :
    ((dyadicRefreshNext X P hdH hconn F hD hd c).width e : ℝ) ≤
      max ((2 ^ a : ℕ) : ℝ) (Real.sqrt ((((2 ^ a : ℕ) : ℝ) / (2 ^ a₀ : ℕ)) *
        (K' * Fintype.card (Tie (2 ^ a)) + max 0 F.energyConstant))) * (W + 1) :=
  expander_branch_width_le (splitSlots X) (bitWordFinEquiv a) (splitWidths X)
    P hdH hconn F hD hd hK' c (fun _ ↦ hW _) e

end Compression.Refresh

end VPVNP
end Computability
end OAI
