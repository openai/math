import OAI.ThreeFlat.Diagonal.HistoryPhysicalFootprint
import OAI.ThreeFlat.Diagonal.ShrinkStageAssembly
import OAI.ThreeFlat.Diagonal.RefreshStageAssembly

namespace OAI
/-! # Concrete per-stage charges for the shrink and refresh history assemblers -/

namespace ThreeFlat.Diagonal.HistoryContraction

open scoped BigOperators Classical

theorem Tree.resources_le_siteCost {F : Type*} {p : ℕ} (T : Tree F p) : T.resources ≤ T.siteCost := by
  unfold Tree.resources Stage.treeWork Tree.siteCost
  omega

theorem PortLayout.sum_hidden {Pins F : Type*} [CommSemiring F] {S : Shape} {R : Rewrite S F} {t : Fin R.count}
    (L : PortLayout S Pins) (n : (R.target t).Site → ℕ) (ord : ∀ v, Fin (n v) ≃ {i // R.owner t i=v}) :
    (∑ v,L.hidden n ord v)=2*∑ e,L.width e := by
  rw [←L.sum_halfBits]
  calc
    _ = ∑ v, ∑ i : {i // R.owner t i = v}, L.halfBits i.val :=
      Finset.sum_congr rfl (fun v _ => (ord v).sum_comp (fun i => L.halfBits i.val))
    _ = _ := Fintype.sum_fiberwise _ _

/-- Merge fixed map overhead and the cubic sorter tariff into the charge used by the history scan. -/
theorem absorb_half_widths (old fresh copies C level : ℕ) :
    1+old+(old+fresh)+C*(level+1)^3*(1+(old+fresh)+copies) ≤
      (2+C)*(level+1)^3*(1+(old+fresh)+copies) := by
  let width := 1+(old+fresh)+copies
  have enough : 1+old+(old+fresh) ≤ 2*width := by dsimp [width]; omega
  have h : 2 ≤ 2*(level+1)^3 := Nat.le_mul_of_pos_right _ (by positivity)
  calc
    _ ≤ (2*(level+1)^3)*width + C*(level+1)^3*width :=
      Nat.add_le_add_right (enough.trans (Nat.mul_le_mul_right _ h)) _
    _ = _ := by dsimp [width]; ring

end ThreeFlat.Diagonal.HistoryContraction

namespace ThreeFlat.Diagonal.CompressorPacking

open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression HistoryContraction MotifKernel MotifOuterTerms
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 950000
set_option maxRecDepth 16000
set_option quotPrecheck false

attribute [local irreducible] historyLayout shrinkingGraph slotPortGraph
  SlotRefinement.actualWidth allPieceSlots shrinkPiece shrinkSite

variable {c d Q : ℕ} {V H Tag L F Pins : Type} [Field F] [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c → ℕ)
    (code : Arc V H Tag L d c ↪ ℕ) (hQ : 0<Q) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q) (bundled : ∀ m, (num m).1=P.bundle m)
    (base : P.Motif → Fin 2 → ℕ) (r : P.Motif → ℕ) (T : ∀ m, FixedMotifTile demandGraph supplyGraph (base m) F)
    (fits : ∀ m e, demandWidth P w num m e ≤ base m e*r m) {terms : ℕ} (hist : Fin terms ≃ Histories P base r T)
    (hn : ∀ a : Tag, -a=a) (good : TagConditions P.slots (shift P) P.offset) (n : Fin 4 → ℕ)
    (positive : ∀ i, 0<n i) (order : ShrinkEdge P n ↪ ℕ) (hc : 2≤c) (pad : ℕ) (padding : LiftedSlots (V×Tag) pad L)
    (idx : Fin terms) (A : WordLayout (oldGraph P) w Pins)

local notation "metricStep" => histogramStep P w code hQ num bundled base r T fits hist hn good n positive order hc pad padding
local notation "lay" => historyLayout P base r T (hist idx)
local notation "nextG" => CompressorRefresh.union (shrinkingGraph P lay n order hc hn good) padding
local notation "nextW" => outputWidth P base r T (hist idx) hn good lay n order hc pad

local notation "W" => shrinkWordLayout (Pins:=Pins) P base r T hist hn good n order hc pad padding idx

variable (counts : Site V Tag L → ℕ) (ord : ∀ v, Fin (counts v) ≃ {i // P.placement (historyLayout P base r T (hist idx)) i=v})
    (sites : Site V Tag L → ℕ) (motifs : ∀ v, Fin (sites v) ≃ Active (partySite P (historyLayout P base r T (hist idx))) v)


local notation "A0" => shrinkAssembly P w code hQ num bundled base r T fits hist hn good n positive order hc pad padding idx A counts ord sites motifs
local notation "old" => A.ports.hidden (R:=metricStep) (t:=idx) counts ord
set_option quotPrecheck false in
local notation "new" => (W).ports.halfBits

theorem shrink_fresh_cost (v : Site V Tag L) (C u D : ℕ)
    (tiles : ∀ m : Active (partySite P lay) v, shrinkTariff P base T m.val ≤ C)
    (heights : ∀ m : Active (partySite P lay) v, HistogramTileNetwork.siteHeight (r m.val) (T m.val).bitCap ≤ u)
    (bounded : sites v ≤ D) :
    (A0).freshResources v ≤ 1+old v+(old v+new v)+
      (1+D+2*C*(D+1))*(u+1)^3*(1+(old v+new v)+∑ m : Active (partySite P lay) v,r m.val) := by
  let oldPins := A.ports.stageOld (R:=metricStep) (t:=idx) (W).ports counts ord v
  let freshPins := A.ports.stageNew (R:=metricStep) (t:=idx) (W).ports counts ord v
  let root := shrinkSite (p:=old v+new v) P w code hQ num base r T (hist idx) hn good n positive
    order hc pad padding v oldPins freshPins (motifs v)
  have paid := shrinkSite_uniform (p:=old v+new v) P w code hQ num base r T (hist idx) hn good
    n positive order hc pad padding v oldPins freshPins (motifs v) C u D tiles heights bounded
  change 1+old v+(old v+new v)+root.resources ≤ _
  exact Nat.add_le_add_left ((Tree.resources_le_siteCost root).trans paid) _

theorem shrink_fresh_uniform (v : Site V Tag L) (C u D : ℕ)
    (tiles : ∀ m : Active (partySite P lay) v, shrinkTariff P base T m.val ≤ C)
    (heights : ∀ m : Active (partySite P lay) v, HistogramTileNetwork.siteHeight (r m.val) (T m.val).bitCap ≤ u)
    (bounded : sites v ≤ D) :
    (A0).freshResources v ≤ (2+(1+D+2*C*(D+1)))*(u+1)^3*(1+(old v+new v)+∑ m : Active (partySite P lay) v,r m.val) :=
  (shrink_fresh_cost P w code hQ num bundled base r T fits hist hn good n positive order hc pad padding idx A
    counts ord sites motifs v C u D tiles heights bounded).trans (absorb_half_widths ..)

end
end ThreeFlat.Diagonal.CompressorPacking

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

local notation "π" => arrival G port
local notation "histStep" => histogramStep G port c w base r T fit hm hh pad sym rows zero bound
set_option quotPrecheck false in
local notation "X" => (Fintype.equivFin (Histories c base r T)).symm idx
local notation "Y" => actualPortGraph (outputGraph G c sym rows zero hm pad)
local notation "nw" => freshWidth c rows (termWidth c w (sparseWidth c base r T X)) pad

variable (A : WordLayout (oldPortGraph (arrival G port)) w Pins)
  (W : WordLayout (actualPortGraph (outputGraph G c sym rows zero hm pad))
    (freshWidth c rows (termWidth c w (sparseWidth c base r T
      ((Fintype.equivFin (Histories c base r T)).symm idx))) pad) Pins)

attribute [local irreducible] actualPortGraph freshWidth
set_option maxRecDepth 9000
set_option maxHeartbeats 850000


local notation "A0" => refreshAssembly G port c w base r T fit hm hh pad sym rows zero bound idx A W
local notation "old" => A.ports.hidden (R:=histStep) (t:=idx) (fun _ => 1) singleChild
local notation "new" => W.ports.halfBits

theorem refresh_fresh_cost (j : (V×L)×Fin m) :
    (A0).freshResources j ≤ 1+old j+(old j+new j)+
      refreshTariff c base T j.1 j.2*((r j.1+1)*(HistogramTileNetwork.siteHeight (r j.1) (T j.1).bitCap+1)^3) := by
  have paid := siteTree_cost (p:=old j+new j) G port c w base r T X hm hh pad sym rows zero bound j.1 j.2
    (A.ports.stageOld (R:=histStep) (t:=idx) W.ports (fun _ => 1) singleChild j ⟨j,rfl⟩)
    (A.ports.stageNew (R:=histStep) (t:=idx) W.ports (fun _ => 1) singleChild j)
  exact Nat.add_le_add_left ((Tree.resources_le_siteCost _).trans paid) (1+old j+(old j+new j))

private theorem refresh_charge {work oldWidth newWidth fee height copies limit price : ℕ}
    (charged : work ≤ 1+oldWidth+(oldWidth+newWidth)+fee*((copies+1)*(height+1)^3))
    (tile : fee ≤ price) (level : height ≤ limit) :
    work ≤ (2+price)*(limit+1)^3*(1+(oldWidth+newWidth)+copies) := by
  apply charged.trans
  refine le_trans ?_ (absorb_half_widths oldWidth newWidth copies price limit)
  apply Nat.add_le_add_left
  have leCopies : copies+1 ≤ 1+(oldWidth+newWidth)+copies := by omega
  calc
    _ ≤ price*((1+(oldWidth+newWidth)+copies)*(limit+1)^3) := Nat.mul_le_mul tile
      (Nat.mul_le_mul leCopies (Nat.pow_le_pow_left (Nat.succ_le_succ level) _))
    _ = _ := by ring

theorem refresh_fresh_uniform (j : (V×L)×Fin m) (C u : ℕ)
    (tile : refreshTariff c base T j.1 j.2 ≤ C)
    (level : HistogramTileNetwork.siteHeight (r j.1) (T j.1).bitCap ≤ u) :
    (A0).freshResources j ≤ (2+C)*(u+1)^3*(1+(old j+new j)+r j.1) := by
  exact refresh_charge (refresh_fresh_cost G port c w base r T fit hm hh pad sym rows zero bound idx A W j)
    tile level

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
