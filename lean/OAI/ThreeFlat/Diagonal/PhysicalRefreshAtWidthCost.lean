import OAI.ThreeFlat.Diagonal.PhysicalRefreshTableWords
import OAI.ThreeFlat.Diagonal.HistoryPhysicalStages

namespace OAI
/-! # Root width and typed cost of the refresh at its installed successor width -/

namespace ThreeFlat.Diagonal.RefreshTies
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression Expander HistoryContraction
open scoped Classical BigOperators
noncomputable section

variable {V C L F Pins : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L] [Field F]
  {m h : ℕ} (G : LiftedSlots V m (C×L)) (port : Fin m ≃ C) (c : Fin m → Fin m → ℕ)
  (w : Address (V×L) m → ℕ) (base : V×L → Bool×Fin m×Fin m → ℕ) (r : V×L → ℕ)
  (T : ∀ u, FixedMotifTile (RefreshMotif.denseGraph m) (ports c) (base u) F)
  (fit : ∀ u e, profile G port w u e ≤ base u e*r u) (hm : 2 ≤ m) (hh : 0<h) (pad : ℕ)
  (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h) (zero : ∀ i, c i i=0)
  {γ : ℝ} (bound : Bound (transition c h) ℝ γ) (idx : Fin (Fintype.card (Histories c base r T)))

local notation "histStep" => histogramStep G port c w base r T fit hm hh pad sym rows zero bound
local notation "actualGraph" => actualPortGraph (outputGraph G c sym rows zero hm pad)
set_option quotPrecheck false in
local notation "chosen" => (Fintype.equivFin (Histories c base r T)).symm idx
local notation "selectedWidth" => freshWidth c rows (termWidth c w (sparseWidth c base r T chosen)) pad

attribute [local irreducible] actualPortGraph freshWidth
set_option maxRecDepth 6000
set_option maxHeartbeats 280000

/-- The refresh root reads the inherited hidden word followed by all incident
bits of the physically supplied successor layout. -/
theorem refresh_root_width_at_width (old : WordLayout (oldPortGraph (arrival G port)) w Pins)
    (bits : LiveSlot V L m (1+h+pad) → ℕ)
    (fresh : WordLayout (actualPortGraph (outputGraph G c sym rows zero hm pad)) bits Pins)
    (same : (histStep).target idx=WordLayout.shape actualGraph bits) (j : (V×L)×Fin m) :
    (refreshAssemblyAtWidth G port c w base r T fit hm hh pad sym rows zero bound idx old bits fresh same).rootWidth j =
      old.ports.hidden (R:=histStep) (t:=idx) (fun _=>1) singleChild j + fresh.ports.halfBits j := by
  have widths : selectedWidth=bits := WordLayout.width_injective actualGraph same
  subst bits
  rfl

/-- The installed stage retains the finite tile charge when its successor exposes
the same width through its own half-word layout. -/
theorem refresh_fresh_at_width (old : WordLayout (oldPortGraph (arrival G port)) w Pins)
    (bits : LiveSlot V L m (1+h+pad) → ℕ)
    (fresh : WordLayout (actualPortGraph (outputGraph G c sym rows zero hm pad)) bits Pins)
    (same : (histStep).target idx=WordLayout.shape actualGraph bits) (j : (V×L)×Fin m) (K u : ℕ)
    (tile : refreshTariff c base T j.1 j.2 ≤ K)
    (level : HistogramTileNetwork.siteHeight (r j.1) (T j.1).bitCap ≤ u) :
    (refreshAssemblyAtWidth G port c w base r T fit hm hh pad sym rows zero bound idx old bits fresh same).freshResources j ≤
      (2+K)*(u+1)^3*(1+(old.ports.hidden (R:=histStep) (t:=idx) (fun _=>1) singleChild j+
        fresh.ports.halfBits j)+r j.1) := by
  have widths : selectedWidth=bits := WordLayout.width_injective actualGraph same
  subst bits
  exact refresh_fresh_uniform G port c w base r T fit hm hh pad sym rows zero bound idx
    old (WordLayout.atWidth selectedWidth fresh) j K u tile level

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
