import OAI.ThreeFlat.Diagonal.RefreshSiteTree
import OAI.ThreeFlat.Diagonal.HistoryWordLayout

namespace OAI
/-! # Joining the unique inherited child to the genuine refresh coefficient -/

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
set_option quotPrecheck false in
local notation "branchHistory" => (Fintype.equivFin (Histories c base r T)).symm idx

def singleChild {J : Type} (j : J) : Fin 1 ≃ {i // id i=j} where
  toFun _ := ⟨j,rfl⟩
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv i := Subtype.ext i.property.symm

variable (A : WordLayout (oldPortGraph (arrival G port)) w Pins)
  (W : WordLayout (actualPortGraph (outputGraph G c sym rows zero hm pad))
    (freshWidth c rows (termWidth c w (sparseWidth c base r T
      ((Fintype.equivFin (Histories c base r T)).symm idx))) pad) Pins)

attribute [local irreducible] actualPortGraph freshWidth

set_option maxHeartbeats 1400000 in
def refreshAssembly : Stage histStep idx A.ports.form (A.ports.inherit (R:=histStep) (t:=idx) W.ports (fun _ => 1) singleChild).form := by
  letI : NeZero m := ⟨by omega⟩
  apply A.ports.wordsStage (R:=histStep) (t:=idx) W.ports (fun _ => 1) singleChild
    (fun j => siteTree G port c w base r T branchHistory hm hh pad sym rows zero bound j.1 j.2
      (A.ports.stageOld (R:=histStep) (t:=idx) W.ports (fun _ => 1) singleChild j ⟨j,rfl⟩)
      (A.ports.stageNew (R:=histStep) (t:=idx) W.ports (fun _ => 1) singleChild j))
  intro j pin x y ox oy
  exact siteTree_eval G port c w base r T branchHistory hm hh pad sym rows zero bound j.1 j.2 _ _ fit pin (x ⟨j,rfl⟩) y (ox ⟨j,rfl⟩) oy

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
