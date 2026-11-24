import OAI.Computability.VPVNP.CompressorRecordRefreshExternal
import OAI.Computability.VPVNP.CompressorRecordChoices
import OAI.Computability.VPVNP.DegreeRefreshConversion

/-!
# Selecting and recording one expander-motif term per port block

The term reader uses the widths of the two copies of the ordered ties, including an
incoming width at its translated source address. Every accepted encoding selects exactly
one family of terms of the actual refresh. The internal arcs in the numbered output rows
carry the selected supply widths, including the selector fields required by the motif map.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh

open Compression Compression.Refresh Compression.DegreeRefresh
open MotifGrid MotifBlocks MotifConversion SpectralGeometry

variable {V E L : Type} {D dH d₀ n bits : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}
variable [AddCommGroup E] [AddCommGroup L] (G : LiftedSlots V D (E × L))
  (port : E ≃ Fin D) (w : (V × Fin D) × (E × L) → ℕ)
  (P : RegularArcGraph (Fin D) dH) (hdH : 0 < dH) (conn : (arcSupportGraph P.multiplicity).Connected)
  (F : FixedBlock k tieSource tieTarget (expanderSupply P hdH conn)
    (realWidths tieMass) (realWidths (expanderMass d₀)) K K')

/-- The demand vector used by the reader is available from the two endpoint record tables. -/
theorem demand_vector (s : V × L) :
    (fun e => (demandRecord G port w s e).width) = blockDemandWidths G port w s :=
  funext (demandRecord_width G port w s)

variable (hD : 1 < D) (hd : dH + 1 ≤ d₀)
  (blocks : Fin n ≃ V × L) (fit : ∀ s, outerCap F (blockDemandWidths G port w s) < 2 ^ bits)

include hD hd in
private theorem supplyMassPos (e : Fin D × Fin dH) : 0 < expanderMass d₀ e :=
  div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))

/-- Complete choice prefixes biject with the internal terms in the exact degree refresh. -/
noncomputable def termReader : ChoiceReader (BlockChoices G port w P hdH conn F) :=
  motifPassReader F blocks finProdFinEquiv.symm (supplyMassPos hD hd) (blockDemandWidths G port w) bits fit

theorem termReader_bits (c : BlockChoices G port w P hdH conn F) :
    ((termReader G port w P hdH conn F hD hd blocks fit).encode c).length ≤ n * ((D * dH) * bits) :=
  motifPass_bits_le F blocks finProdFinEquiv.symm (supplyMassPos hD hd) (blockDemandWidths G port w) bits fit c

/-- The stored expander slot number identifies the supply role, the matching incoming slot
and the exact payload-plus-selector width of this branch. -/
theorem chosen_supply_record (c : BlockChoices G port w P hdH conn F) (s : V × L) (e : Fin D × Fin dH) :
    let internal := blockSupplyWidths G port w P hdH conn F c
    let r := slotRecord G port w P.toSlotGraph hd internal (s,e.1) (.inr (.inl e.2))
    r.src = (promotedSites (s,e.1), refreshSlots hd (.inr (.inl e.2))) ∧
      r.dst = (promotedSites (s,(P.reverse e).1), refreshSlots hd (.inr (.inl (P.reverse e).2))) ∧
      r.width = supplyWidths F (fun t => (demandRecord G port w s t).width) (c s).val e := by
  rw [demand_vector]
  exact ⟨rfl, rfl, rfl⟩

end CompressorRecords.PortRefresh

end VPVNP
end Computability
end OAI
