import OAI.ThreeFlat.Diagonal.PhysicalRefreshTableChart
import OAI.ThreeFlat.Diagonal.PhysicalRefreshAtWidthCost

namespace OAI
/-! # The measured width and resource bill of the installed refresh table -/

namespace ThreeFlat.Diagonal.RefreshMotif.Table
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression Expander HistoryContraction RefreshTies
open scoped Classical BigOperators
noncomputable section

variable {V C L F Pins U E : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L]
  [Field F] [Fintype U] [Fintype E] {m h pad : ℕ} {c : Fin m → Fin m → ℕ} {tariff γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) tariff) (G : LiftedSlots V m (C×L))
  (port : Fin m ≃ C) (w : Address (V×L) m → ℕ) (hm : 2 ≤ m) (hh : 0<h)
  (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h) (zero : ∀ i,c i i=0)
  (conn : Bound (transition c h) ℝ γ)
  {source : PortGraph U E} {width : E → ℕ}

local notation "rule" => step T G port w hm hh sym rows zero conn
local notation "oldGraph" => oldPortGraph (arrival G port)
local notation "outGraph" => actualPortGraph (outputGraph G c sym rows zero hm pad)
attribute [local irreducible] actualPortGraph freshWidth
set_option maxHeartbeats 400000
set_option maxRecDepth 2600

variable (I : HistoryRelabel.Iso (WordLayout.shape source width) (WordLayout.shape (oldPortGraph (arrival G port)) w))
  (layout : WordLayout source width Pins) (i : Fin (T.step G port w hm hh sym rows zero conn).count)
  (bits : LiveSlot V L m (1+h+pad) → ℕ) (fresh : WordLayout (actualPortGraph (outputGraph G c sym rows zero hm pad)) bits Pins)
  (same : (T.step G port w hm hh sym rows zero conn).target i=WordLayout.shape (actualPortGraph (outputGraph G c sym rows zero hm pad)) bits)
  (edgeWidth : ∀ e,width e=w (I.edge e)) (keep : ∀ e x,(I.label e x).val=x.val)

local notation "installed" => wordStageOnChart T G port w hm hh sym rows zero conn I layout i bits fresh same edgeWidth keep


local notation "packed" => I.pushWord (G:=source) (H:=oldGraph) (w:=width) (b:=w) layout
set_option quotPrecheck false in
local notation "old" => (packed).ports.hidden (R:=rule) (t:=i) (fun _=>1) singleChild
local notation "base" => (fun a => T.base (T.winner G port w a))
local notation "copies" => T.repeats G port w
local notation "tile" => T.entry G port w

include edgeWidth in
private theorem packedHidden (z : (V×L)×Fin m) :
    old z=layout.ports.halfBits (I.site.symm z) := by
  calc
    _ = (packed).ports.halfBits z := by
      change (∑ j : Fin 1,(packed).ports.halfBits (singleChild z j).val)=_
      simp [singleChild]
    _ = _ := I.pushWord_halfBits_at layout edgeWidth z

theorem wordStageOnChart_hidden (z : (V×L)×Fin m) :
    (installed).hidden z=layout.ports.halfBits (I.site.symm z) := by
  change old z=_
  exact packedHidden T G port w hm hh sym rows zero conn I layout i edgeWidth z

theorem wordStageOnChart_width (z : (V×L)×Fin m) :
    (installed).rootWidth z=layout.ports.halfBits (I.site.symm z)+fresh.ports.halfBits z := by
  have raw := refresh_root_width_at_width G port c w base copies tile (fun v=>T.fits _)
    hm hh pad sym rows zero conn i packed bits fresh same z
  exact raw.trans (congrArg (fun n => n + fresh.ports.halfBits z)
    (packedHidden T G port w hm hh sym rows zero conn I layout i edgeWidth z))

theorem wordStageOnChart_price (z : (V×L)×Fin m) (K u : ℕ)
    (fee : refreshTariff c base tile z.1 z.2 ≤ K)
    (level : HistogramTileNetwork.siteHeight (copies z.1) (tile z.1).bitCap ≤ u) :
    (installed).freshResources z ≤
      (2+K)*(u+1)^3*(1+(layout.ports.halfBits (I.site.symm z)+fresh.ports.halfBits z)+copies z.1) := by
  have raw := refresh_fresh_at_width G port c w base copies tile (fun v=>T.fits _)
    hm hh pad sym rows zero conn i packed bits fresh same z K u fee level
  have hidden := packedHidden T G port w hm hh sym rows zero conn I layout i edgeWidth z
  exact raw.trans_eq (congrArg (fun n => (2+K)*(u+1)^3*(1+(n+fresh.ports.halfBits z)+copies z.1)) hidden)

end
end ThreeFlat.Diagonal.RefreshMotif.Table

end OAI
