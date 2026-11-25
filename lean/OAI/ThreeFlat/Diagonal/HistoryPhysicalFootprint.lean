import OAI.ThreeFlat.Diagonal.HistoryPhysicalTariff
import OAI.ThreeFlat.Diagonal.ShrinkSiteTree
import OAI.ThreeFlat.Diagonal.RefreshSiteTree

namespace OAI
/-! # Resources charged by the physical shrink and refresh history-site constructors -/

namespace ThreeFlat.Diagonal

open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression HistoryContraction MotifOuterTerms MotifKernel MotifBinaryPacking HistogramTileNetwork
open scoped Classical BigOperators
noncomputable section



namespace CompressorPacking

set_option maxHeartbeats 1000000
set_option maxRecDepth 16000

attribute [local irreducible] historyLayout shrinkingGraph slotPortGraph
  SlotRefinement.actualWidth allPieceSlots

open private sitePins pieceAt from OAI.ThreeFlat.Diagonal.ShrinkSiteTree

variable {c d Q p : ℕ} {V H Tag L F : Type} [Field F] [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c → ℕ)
    (code : Arc V H Tag L d c ↪ ℕ) (hQ : 0<Q) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q)
    (base : P.Motif → Fin 2 → ℕ) (r : P.Motif → ℕ) (T : ∀ m, FixedMotifTile demandGraph supplyGraph (base m) F)
    (fit : ∀ m e, demandWidth P w num m e ≤ base m e*r m) (x : Histories P base r T)
    (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset)
    (n : Fin 4 → ℕ) (positive : ∀ i, 0<n i) (order : ShrinkEdge P n ↪ ℕ) (hc : 2≤c) (pad : ℕ)
    (padding : LiftedSlots (V×Tag) pad L) (v : Site V Tag L)

local notation "layout" => historyLayout P base r T x
variable (old : (i : {i // P.placement (historyLayout P base r T x) i=v}) → (a : (oldGraph P).Port i.val) → Fin (w a.1.1) → Fin p)
    (new : sitePins (outGraph P hn good (historyLayout P base r T x) n order hc pad padding) (outputWidth P base r T x hn good (historyLayout P base r T x) n order hc pad) v p)

/-- This price depends on the finite six-party tile and its base demand. -/
def shrinkTariff (m : P.Motif) : ℕ :=
  Tree.tileTariff demandGraph supplyGraph (base m) (T m).bits (Fintype.card (T m).Alphabet) (T m).bitCap

theorem shrinkPiece_cost (m : P.Motif) :
    (shrinkPiece (p:=p) P w code hQ num base r T x hn good n positive order hc pad padding v old new m).siteCost ≤
      shrinkTariff P base T m*((r m+1)*(siteHeight (r m) (T m).bitCap+1)^3) := by
  let := (T m).hasLetter
  let party := HistoryMaskOrder.order (fun j => partySite P layout m j=v)
  let crossed := crossingPin (p:=p) P base r T x hn good layout n positive order hc pad padding v new m
  unfold shrinkPiece pieceAt shrinkTariff
  exact Tree.occupied_cost (F:=F) (p:=p) (k:=(T m).bits) (d:=(T m).bitCap)
    (r:=r m) (D:=demandGraph) (G:=ShrinkMotif.supply) (w:=demandWidth P w num m)
    (base:=base m) (sw:=(T m).output) (M:=(T m).entry) (code:=(T m).encode)
    (id:=Fintype.equivFin (T m).Alphabet) (z:=x m) (place:=partySite P layout m) (v:=v)
    (edges:=HistoryMaskOrder.order (fun e => wireOwner supplyGraph.tail supplyGraph.head
      (partySite P layout m) e=some v)) (parts:=party)
    (supply:=fun i => (Fintype.equivFin (supplyGraph.Port (party i).val)).symm)
    (demand:=fun i => (Fintype.equivFin (demandGraph.Port (party i).val)).symm)
    (cap:=fun y f => (T m).output_le_cap y f)
    (oldPins:=fun i q t => oldPinSource P w code hQ num layout v old m (party i).val q t)
    (crossPins:=crossed)

attribute [local irreducible] shrinkPiece

theorem shrinkSite_cost {s : ℕ} (enum : Fin s ≃ Active (partySite P layout) v) :
    (shrinkSite (p:=p) P w code hQ num base r T x hn good n positive order hc pad padding v old new enum).siteCost ≤
      1+s*p+2*∑ m : Active (partySite P layout) v,
        shrinkTariff P base T m.val*((r m.val+1)*(siteHeight (r m.val) (T m.val).bitCap+1)^3) := by
  let child : Active (partySite P layout) v → Tree F p := fun m =>
    shrinkPiece (p:=p) P w code hQ num base r T x hn good n positive order hc pad padding v old new m.val
  let charge : Active (partySite P layout) v → ℕ := fun m =>
    shrinkTariff P base T m.val*((r m.val+1)*(siteHeight (r m.val) (T m.val).bitCap+1)^3)
  have paid (m : Active (partySite P layout) v) : (child m).siteCost ≤ charge m :=
    shrinkPiece_cost (p:=p) P w code hQ num base r T x hn good n positive order hc pad padding v old new m.val
  unfold shrinkSite
  refine (Tree.activeTree_cost_le (p:=p) (F:=F) (partySite P layout) v enum child charge paid).trans_eq ?_
  apply congrArg (fun q : ℕ => 1+s*p+2*q)
  apply Finset.sum_congr (by ext; simp)
  intro m _
  rfl

/-- A single library tariff and sorter depth suffice across all active tiles.
The number of active motifs controls the number of full public pin maps. -/
theorem shrinkSite_uniform {s : ℕ} (enum : Fin s ≃ Active (partySite P layout) v) (C u D : ℕ)
    (tiles : ∀ m : Active (partySite P layout) v, shrinkTariff P base T m.val ≤ C)
    (height : ∀ m : Active (partySite P layout) v, siteHeight (r m.val) (T m.val).bitCap ≤ u)
    (active : s ≤ D) :
    (shrinkSite (p:=p) P w code hQ num base r T x hn good n positive order hc pad padding v old new enum).siteCost ≤
      (1+D+2*C*(D+1))*(u+1)^3*(1+p+∑ m : Active (partySite P layout) v,r m.val) := by
  apply (shrinkSite_cost P w code hQ num base r T x hn good n positive order hc pad padding v old new enum).trans
  let J := Active (partySite P layout) v
  let f : J → ℕ := fun m => r m.val
  let q := (u+1)^3
  have one : 1 ≤ q := Nat.succ_le_of_lt (by dsimp [q]; positivity : 0 < q)
  have card : Fintype.card J=s := by simpa only [Fintype.card_fin] using (Fintype.card_congr enum).symm
  have sums : (∑ m : J, shrinkTariff P base T m.val*((r m.val+1)*(siteHeight (r m.val) (T m.val).bitCap+1)^3)) ≤
      C*q*((∑ m,f m)+s) := by
    calc
      _ ≤ ∑ m : J, C*q*(f m+1) := by
        apply Finset.sum_le_sum
        intro m _
        calc
          _ ≤ C*((f m+1)*q) := Nat.mul_le_mul (tiles m)
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ (height m)) _))
          _ = _ := by ring
      _ = _ := by simp [←Finset.mul_sum,Finset.sum_add_distrib,card]
  have first : 1+s*p ≤ (1+D)*q*(1+p+∑ m,f m) := by
    calc
      _ ≤ 1+D*p := Nat.add_le_add_left (Nat.mul_le_mul_right _ active) _
      _ ≤ (1+D)*(1+p+∑ m,f m) := by rw [Nat.add_mul,one_mul,Nat.mul_add,Nat.mul_add,Nat.mul_one]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ one)
  have bound : (∑ m,f m)+s ≤ (D+1)*(1+p+∑ m,f m) := by
    simp only [Nat.add_mul,one_mul,Nat.mul_add,Nat.mul_one]
    omega
  calc
    _ ≤ (1+D)*q*(1+p+∑ m,f m)+2*(C*q*((∑ m,f m)+s)) :=
      Nat.add_le_add first (Nat.mul_le_mul_left _ sums)
    _ ≤ (1+D)*q*(1+p+∑ m,f m)+2*(C*q*((D+1)*(1+p+∑ m,f m))) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ bound)) _
    _ = _ := by change _ = (1+D+2*C*(D+1))*q*(1+p+∑ m,f m); ring

end CompressorPacking
end
end ThreeFlat.Diagonal
namespace ThreeFlat.Diagonal.RefreshTies

set_option maxHeartbeats 1000000
set_option maxRecDepth 16000

open Computability.VPVNP.Compression Computability.VPVNP.MotifSelector LinearAlgebra.SpectralBooks Expander HistoryContraction MotifOuterTerms HistogramTileNetwork
open scoped Classical BigOperators
noncomputable section

variable {V C L F : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L] [Field F]
  {m h p : ℕ} (G : LiftedSlots V m (C×L)) (port : Fin m ≃ C) (c : Fin m → Fin m → ℕ)
  (w : Address (V×L) m → ℕ) (base : V×L → Bool×Fin m×Fin m → ℕ) (r : V×L → ℕ)
  (T : ∀ u, FixedMotifTile (RefreshMotif.denseGraph m) (ports c) (base u) F) (x : Histories c base r T)
  (hm : 2 ≤ m) (hh : 0<h) (pad : ℕ) (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h)
  (zero : ∀ i, c i i=0) {γ : ℝ} (bound : Bound (transition c h) ℝ γ) (u : V×L) (v : Fin m)

local notation "π" => arrival G port
local notation "Y" => actualPortGraph (outputGraph G c sym rows zero hm pad)
local notation "sparseW" => sparseWidth c base r T x
local notation "bw" => termWidth c w sparseW
local notation "newW" => freshWidth c rows bw pad
local notation "D" => RefreshMotif.denseGraph m
local notation "P" => (fun _ : V×L => ports c)
local notation "S" => DoublePorts.connectedSupply c hh rows sym bound
set_option quotPrecheck false in
local notation "idT" => Fintype.equivFin (T u).Alphabet
set_option quotPrecheck false in
local notation "selector" => (fun j e => SlotRefinement.selectorWord (r j) (T j).bits (histWidth (T j).output (x j) e))

open private outputPins pullPins from OAI.ThreeFlat.Diagonal.RefreshSiteTree

variable (old : (a : (oldPortGraph (arrival G port)).Port (u,v)) → Fin (w a.1.1) → Fin p)
  (new : outputPins G c hm pad sym rows zero (termWidth c w (sparseWidth c base r T x)) (u,v) p)

attribute [local irreducible] actualPortGraph freshWidth

def refreshTariff :=
  1+Tree.portTariff D (ports c) (base u) (T u).bits (Fintype.card (T u).Alphabet) (T u).bitCap v

omit [Fintype V] [Fintype L] in
theorem siteTree_cost :
    (siteTree (p:=p) G port c w base r T x hm hh pad sym rows zero bound u v old new).siteCost ≤
      refreshTariff c base T u v*((r u+1)*(siteHeight (r u) (T u).bitCap+1)^3) := by
  let : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
  let := (T u).hasLetter
  let src := pullPins G c hm pad sym rows zero bw (u,v) p new
  unfold siteTree refreshTariff
  exact Tree.directParty_cost (F:=F) (p:=p) (k:=(T u).bits) (d:=(T u).bitCap)
    (r:=r u) (e:=2*h) (n:=4*m) (H:=(T u).Alphabet) D S v (profile G port w u) (base u)
    ⟨RefreshParty.denseOrder v,(T u).encode⟩ (RefreshParty.sparseOrder c sym rows v)
    (T u).output (fun z q => (T u).output_le_cap z _) (T u).entry idT (x u)
    (demandPin π (externalSite G) (external_site G port) P w sparseW u v old src)
    (sparsePin (externalSite G) P w sparseW u v src)

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
