import OAI.ThreeFlat.Diagonal.PhysicalWordWidthTransport
import OAI.ThreeFlat.Diagonal.RefreshStageAssembly

namespace OAI
/-! # The actual refresh kernel at a transported output word width -/

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

/-- Retain the actual local direct-party tree and its child order when the physical
successor exposes its half bits using a propositionally equal width function. -/
def refreshAssemblyAtWidth (old : WordLayout (oldPortGraph (arrival G port)) w Pins)
    (bits : LiveSlot V L m (1+h+pad) → ℕ)
    (fresh : WordLayout (actualPortGraph (outputGraph G c sym rows zero hm pad)) bits Pins)
    (same : (histStep).target idx=WordLayout.shape actualGraph bits) :
    Stage histStep idx old.ports.form
      (same.symm ▸ (old.inherited fresh id (fun _ => 1) singleChild).ports.form) := by
  let raw := refreshAssembly G port c w base r T fit hm hh pad sym rows zero bound idx old
    (WordLayout.atWidth selectedWidth fresh)
  exact raw.reform (WordLayout.inheritedWidth_eq (graph:=actualGraph) (first:=selectedWidth)
    (second:=bits) old same fresh id (fun _ => 1) singleChild).symm

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
