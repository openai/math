import OAI.Computability.VPVNP.DegreeRefreshActualStep
import OAI.Computability.VPVNP.DegreeRefreshPorts
import OAI.Computability.VPVNP.DegreeRefreshSupply
import OAI.Computability.VPVNP.ExpanderSlots
import OAI.Computability.VPVNP.MotifConversion

/-!
# Exact degree refresh from a spectral expander

The expander and the field determine the finite equations of the port
motif before any old graph or widths are specified. Any solution of these
equations over a commutative ring gives the exact degree refresh (7.1).
Each block chooses an admitted payload profile from Theorem 6.1. Its
internal slots carry the profile widths together with the selector bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.Refresh

open MotifGrid MotifBlocks MotifConversion SpectralGeometry NetworkKernel WireTensor DegreeRefresh

variable {k : Type*} [Field k] {D dH d₀ : ℕ} {γ K K' : ℝ}

/-- A single finite system of integer equations has a solution over the
field of the spectral port bound. The system is independent of the old
network and its widths. -/
theorem exists_expander_parameters (G : RegularArcGraph (Fin D) dH) (hdH : 0 < dH)
    (hD : 2 ≤ D) (hd₀ : 0 < d₀) (hP : SpectralPortBound k G γ) :
    let P := expanderSupply G hdH (hP.connected_and_pos hD).1
    let K := 2 * γ * d₀ / dH
    ∃ F : FixedBlock k tieSource tieTarget P (realWidths tieMass) (realWidths (expanderMass d₀)) K (K + 1),
      ∃ κ : (parameterData F).Entry → k, (parameterData F).IsSolution κ := by
  obtain ⟨F⟩ := exists_expander_block G hdH hD hd₀ hP
  exact ⟨F, exists_solution F⟩

variable {V E L : Type} [Fintype V] [Fintype E] [Fintype L] [AddCommGroup E] [AddCommGroup L]
  (G : LiftedSlots V D (E × L)) (port : E ≃ Fin D) (w : (V × Fin D) × (E × L) → ℕ)

/-- The widths of the two copies of nonlocal segment ties read in each block. -/
abbrev blockDemandWidths := internalWidth (oldPortMatching G port) (groupedWidths port w)

omit [Fintype V] [Fintype E] [Fintype L] in
theorem blockDemandWidths_eq : blockDemandWidths G port w =
    tieWidth (bundleTarget G) (bundlePort G port) (bundleWidths port w) := by
  funext s e
  exact internalWidth_eq_tieWidth G port _ s e

variable (P : RegularArcGraph (Fin D) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : FixedBlock k tieSource tieTarget (expanderSupply P hdH hconn)
    (realWidths tieMass) (realWidths (expanderMass d₀)) K K')

/-- Independent admitted payload profiles in the blocks of a network. -/
noncomputable abbrev BlockChoices :=
  (s : V × L) → ↥(outerIndices F (blockDemandWidths G port w s))

/-- Every internal edge carries its admitted payload and one selector per
base-identity repetition. -/
noncomputable abbrev blockSupplyWidths (c : BlockChoices G port w P hdH hconn F) :=
  fun s ↦ supplyWidths F (blockDemandWidths G port w s) (c s).val

variable {R : Type*} [CommRing R] (κ : (parameterData F).Entry → R)
  (hκ : (parameterData F).IsSolution κ) (hD : 1 < D) (hd : dH + 1 ≤ d₀)

/-- Evaluate the fixed equations' local maps on the old graph and use the
actual slots of the refreshed graph for the resulting kernel. -/
noncomputable def expanderRefreshStep : Step R (actualWireGraph G w) := by
  let : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
  let b := blockDemandWidths G port w
  let I (s : V × L) := ↥(outerIndices F (b s))
  let u (s : V × L) (i : I s) := supplyWidths F (b s) i.val
  let A (s : V × L) (i : I s) (e : Fin D × Fin dH) := Fin (2 ^ u s i e)
  have hp (i : Tie D) : 0 < tieMass i := zero_lt_one
  have hq (e : Fin D × Fin dH) : 0 < expanderMass d₀ e := by
    unfold expanderMass
    exact div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))
  let M (s : V × L) (i : I s) (j : Fin D) :=
    fun x y ↦ evalEntry κ (entry F hp (b s) i.val j x y)
  apply actualRefreshStep G port w P.toSlotGraph hD hd A u (fun s i e ↦ (wordIndex (u s i e)).symm) M
  intro s
  exact (identity F κ hκ hp hq (b s)).trans (Finset.sum_coe_sort _ _).symm

/-- The branches of the spectral refresh use the arc widths of the admitted
motif terms, in the regular graph's specified slot numbering. -/
theorem expanderRefreshStep_output (c : BlockChoices G port w P hdH hconn F) :
    ((expanderRefreshStep G port w P hdH hconn F κ hκ hD hd).term c).output =
      actualWireGraph (degreeRefresh G P.toSlotGraph hD hd)
        (actualWidths hd port w (blockSupplyWidths G port w P hdH hconn F c)) := rfl

/-- The old vertex factor stays at its physical position in every branch. -/
theorem expanderRefreshStep_place (c : BlockChoices G port w P hdH hconn F) (x : V × (E × L)) :
    ((expanderRefreshStep G port w P hdH hconn F κ hκ hD hd).term c).place x =
      refreshPositions port x := rfl

end Compression.Refresh

end VPVNP
end Computability
end OAI
