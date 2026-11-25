import OAI.ThreeFlat.Diagonal.PhysicalRefreshIssuedValue
import OAI.ThreeFlat.Diagonal.PhysicalRefreshIssuedType

namespace OAI
/-! # The installed word stage of a physical refresh and its parent slot -/

namespace ThreeFlat.Diagonal.PhysicalStage
open LinearAlgebra.SpectralBooks Expander Computability.VPVNP.Compression CompressorPacking HistoryContraction
open scoped Classical BigOperators
noncomputable section

variable {F Pins : Type} [Field F] {m lanes hbits rem h pad : ℕ} {c : Fin m→Fin m→ℕ} {C γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) C) (A : State m lanes)
  (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
  (hm : 2 ≤ m) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (zero : ∀ i,c i i=0) (conn : Bound (transition c h) ℝ γ)

set_option quotPrecheck false

local notation "physMove" => refreshMove T A u port hm hh sym rows zero conn
local notation "inIso" => StageAddress.refreshInputIso A.graph A.chart u port A.width

attribute [local irreducible] CompressorRefresh.graph RefreshTies.freshWidth
  RefreshMotif.Table.wordStageOnChart RefreshTies.refreshAssemblyAtWidth

section
variable (L : A.Words Pins) (idx : Fin (refreshMove T A u port hm hh sym rows zero conn).rules.count)

open private uniqueChild physicalChildren
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshIssuedStage

set_option maxHeartbeats 110000 in
def refreshWordStage : StageFor (physMove) idx L
    (refreshWords T A u port hm hh sym rows zero conn L idx) :=
  cast (RefreshIssued.type_eq T A u port hm hh sym rows zero conn L idx)
    (RefreshIssued.selected T A u port hm hh sym rows zero conn L idx)

private theorem castStage_heq {X Y : Sort _} (types : X = Y) (value : X) :
    HEq (cast types value) value := by cases types; rfl

private abbrev selectedStage_heq :=
  castStage_heq (RefreshIssued.type_eq T A u port hm hh sym rows zero conn L idx)
    (RefreshIssued.selected T A u port hm hh sym rows zero conn L idx)

private theorem installedChildren :
    uniqueChild (refreshWordStage T A u port hm hh sym rows zero conn L idx) (inIso).site.symm := by
  have source := physicalChildren T A u port hm hh sym rows zero conn L idx
  have issued := RefreshIssued.selected_eq T A u port hm hh sym rows zero conn L idx
  rw [← issued] at source
  have equal := eq_of_heq (selectedStage_heq T A u port hm hh sym rows zero conn L idx)
  unfold refreshWordStage
  rw [equal]
  exact source

theorem refreshWordCount (z : ((physMove).rules.target idx).Site) :
    (refreshWordStage T A u port hm hh sym rows zero conn L idx).count z=1 :=
  (installedChildren T A u port hm hh sym rows zero conn L idx z).1

theorem refreshWordChild (z : ((physMove).rules.target idx).Site)
    (k : Fin ((refreshWordStage T A u port hm hh sym rows zero conn L idx).count z)) :
    ((refreshWordStage T A u port hm hh sym rows zero conn L idx).child z k).val
      = (inIso).site.symm z :=
  (installedChildren T A u port hm hh sym rows zero conn L idx z).2 k


end
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
