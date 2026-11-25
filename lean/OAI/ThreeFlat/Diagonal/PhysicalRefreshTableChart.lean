import OAI.ThreeFlat.Diagonal.PhysicalRefreshTableWords
import OAI.ThreeFlat.Diagonal.RefreshTableStep

namespace OAI
/-! # Installing the selected table's refresh kernel in a numbered source chart -/

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
set_option maxHeartbeats 250000
set_option maxRecDepth 2600

/-- The source chart transports the original pin words. The selected physical shape
equality fixes the destination, including the literal half-bit ordering. -/
def wordStageOnChart (I : HistoryRelabel.Iso (WordLayout.shape source width) (WordLayout.shape oldGraph w))
    (layout : WordLayout source width Pins) (i : Fin (rule).count)
    (bits : LiveSlot V L m (1+h+pad) → ℕ) (fresh : WordLayout outGraph bits Pins)
    (same : (rule).target i=WordLayout.shape outGraph bits)
    (edgeWidth : ∀ e,width e=w (I.edge e)) (keep : ∀ e x,(I.label e x).val=x.val) :
    Stage (I.rewrite rule) i layout.ports.form
      (same.symm ▸ ((I.pushWord (H:=oldGraph) (b:=w) layout).inherited fresh id (fun _ => 1) singleChild).ports.form) :=
  I.onStage (G:=source) (H:=oldGraph) (w:=width) (b:=w) (R:=rule) (idx:=i) layout
    (refreshAssemblyAtWidth G port c w (fun v => T.base (T.winner G port w v))
      (T.repeats G port w) (T.entry G port w) (fun _v => T.fits _)
      hm hh pad sym rows zero conn i (I.pushWord (H:=oldGraph) (b:=w) layout) bits fresh same)
    edgeWidth keep

variable (I : HistoryRelabel.Iso (WordLayout.shape source width) (WordLayout.shape (oldPortGraph (arrival G port)) w))
  (layout : WordLayout source width Pins) (i : Fin (T.step G port w hm hh sym rows zero conn).count)
  (bits : LiveSlot V L m (1+h+pad) → ℕ) (fresh : WordLayout (actualPortGraph (outputGraph G c sym rows zero hm pad)) bits Pins)
  (same : (T.step G port w hm hh sym rows zero conn).target i=WordLayout.shape (actualPortGraph (outputGraph G c sym rows zero hm pad)) bits)
  (edgeWidth : ∀ e,width e=w (I.edge e)) (keep : ∀ e x,(I.label e x).val=x.val)

local notation "installed" => wordStageOnChart T G port w hm hh sym rows zero conn I layout i bits fresh same edgeWidth keep

theorem wordStageOnChart_count (z : (V×L)×Fin m) : (installed).count z=1 := rfl

theorem wordStageOnChart_child (z : (V×L)×Fin m) (k : Fin ((installed).count z)) :
    ((installed).child z k).val=I.site.symm z := rfl

end
end ThreeFlat.Diagonal.RefreshMotif.Table

end OAI
