import OAI.ThreeFlat.Diagonal.PhysicalStageBinary
import OAI.ThreeFlat.Diagonal.PhysicalStateEnergy

namespace OAI
/-! # The fixed-table energy bound on the actual refreshed physical state -/

namespace ThreeFlat.Diagonal.PhysicalStage

open private refreshRules_count from OAI.ThreeFlat.Diagonal.PhysicalStageRefresh
open Expander Computability.VPVNP.Compression CompressorPacking
open scoped BigOperators Classical
noncomputable section

section General

variable {m lanes hbits rem h pad : ℕ} {F : Type} [Field F]
    {c : Fin m → Fin m → ℕ} {H γ : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) H) (A : State m lanes)
    (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
    (hm : 2 ≤ m) (hh : 0 < h)
    (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h)
    (zero : ∀ i, c i i=0) (conn : Bound (transition c h) ℝ γ)

/-- Splitting a lane into the port coordinate and the remaining lane bits
is a bijection on the sites of each successor. -/
theorem refreshMove_positions (i : Fin (refreshMove T A u port hm hh sym rows zero conn).rules.count) :
    ((refreshMove T A u port hm hh sym rows zero conn).next i).positions = A.positions := by
  change Fintype.card ((A.Base × BitWord rem) × Fin m) = A.positions
  exact A.positions_reindex (StageAddress.refreshSite u port).symm

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- Every actual histogram branch of the refresh has the quadratic table
error and the old-energy multiplier shared by all physical graphs. -/
theorem refreshMove_energy (i : Fin (refreshMove T A u port hm hh sym rows zero conn).rules.count) :
    ((refreshMove T A u port hm hh sym rows zero conn).next i).energy ≤
      (((1+h+pad : ℕ) : ℝ)+2*H)*A.energy + T.error*(A.positions : ℝ)^2 := by
  let G := changeLanes A.graph u
  let w := refreshInput A u port
  let z := (Fintype.equivFin (refreshBranches T A u port)).symm
    (i.cast (refreshRules_count T A u port hm hh sym rows zero conn))
  let out := RefreshTies.freshWidth c rows (RefreshTies.termWidth c w (T.widths G port w z)) pad
  let R := refreshMove T A u port hm hh sym rows zero conn
  have hpNat : Fintype.card (A.Base × BitWord rem)*m = A.positions := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using (A.positions_reindex (StageAddress.refreshSite u port).symm)
  have hp : (Fintype.card (A.Base × BitWord rem) : ℝ)*m = A.positions := by exact_mod_cast hpNat
  have old : (∑ e, (w e : ℝ)^2/(1/((A.positions : ℝ)*m))) = A.energy :=
    A.energy_reindex (StageAddress.refreshEdge u port).symm
  have bound := T.stage_energy G port w (show 0 < m by omega)
    (show 0 < Fintype.card (A.Base × BitWord rem) from Fintype.card_pos) rows z
  dsimp only at bound
  rw [hp, old] at bound
  change (∑ e, (out e : ℝ)^2/(1/(((R.next i).positions : ℝ)*(1+h+pad : ℕ)))) ≤ _
  rw [show (R.next i).positions = A.positions from
    refreshMove_positions T A u port hm hh sym rows zero conn i]
  exact bound

end General

section Binary

variable {s rem h pad : ℕ} {F : Type} [Field F] {H γ : ℝ} {c : Fin (2^s) → Fin (2^s) → ℕ}
    (T : RefreshMotif.Table F c (1+h+pad) H) (A : State (2^s) (s+rem))
    (hm : 2 ≤ 2^s) (hh : 0 < h) (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h)
    (zero : ∀ i, c i i=0) (conn : Bound (transition c h) ℝ γ)

theorem refreshBinary_positions (i : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count) :
    ((refreshBinary T A hm hh sym rows zero conn).next i).positions = A.positions :=
  refreshMove_positions T A (splitWord s rem) (Native.tagOrdinal s).symm hm hh sym rows zero conn i

/-- In particular the table with leading coefficient
`RefreshMotif.leading h (1+h+pad) γ + 1` uses precisely its stored error. -/
theorem refreshBinary_energy (i : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count) :
    ((refreshBinary T A hm hh sym rows zero conn).next i).energy ≤
      (((1+h+pad : ℕ) : ℝ)+2*H)*A.energy + T.error*(A.positions : ℝ)^2 :=
  refreshMove_energy T A (splitWord s rem) (Native.tagOrdinal s).symm hm hh sym rows zero conn i

end Binary
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
