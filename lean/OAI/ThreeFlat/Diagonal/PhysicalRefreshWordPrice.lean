import OAI.ThreeFlat.Diagonal.PhysicalRefreshWordStage
import OAI.ThreeFlat.Diagonal.PhysicalRefreshSourcePrice
import OAI.ThreeFlat.Diagonal.PhysicalRefreshIssuedPrice

namespace OAI
/-! # Fresh resources of the numerical stage issued on the selected refresh move -/

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

local notation "inputGraph" => changeLanes A.graph u
local notation "inputWidth" => refreshInput A u port
local notation "outGraph" => RefreshTies.actualPortGraph (RefreshTies.outputGraph inputGraph c sym rows zero hm pad)
local notation "rule" => T.step inputGraph port inputWidth hm hh sym rows zero conn

open private selectedBits outputWords outputShape selectedOutput issuedWords
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage

open private selectedStage_heq from OAI.ThreeFlat.Diagonal.PhysicalRefreshWordStage

local notation "sourceStage" => RefreshPrepared.sourceStage T A u port hm hh sym rows zero conn L idx
local notation "actual" => refreshWordStage T A u port hm hh sym rows zero conn L idx
local notation "selected" => outputWords (Pins:=Pins) T A u port hm hh sym rows zero conn idx

set_option maxHeartbeats 200000 in
private theorem installed_measure (z : ((physMove).rules.target idx).Site) :
    ((actual).freshResources z,(actual).hidden z,(actual).rootWidth z) =
      ((sourceStage).freshResources z,(sourceStage).hidden z,(sourceStage).rootWidth z) ∧
    ∀ k, Tree.Within k ((sourceStage).root z) → Tree.Within k ((actual).root z) := by
  have measured := refreshIssued_measure T A u port hm hh sym rows zero conn L idx z
  have issued := RefreshIssued.selected_eq T A u port hm hh sym rows zero conn L idx
  rw [← issued] at measured
  have equal := eq_of_heq (selectedStage_heq T A u port hm hh sym rows zero conn L idx)
  unfold refreshWordStage
  rw [equal]
  exact measured

set_option maxHeartbeats 200000 in
theorem refreshWordStage_cost (z : ((physMove).rules.target idx).Site) :
    (actual).freshResources z=(sourceStage).freshResources z :=
  congrArg Prod.fst (installed_measure T A u port hm hh sym rows zero conn L idx z).1

set_option maxHeartbeats 200000 in
theorem refreshWordStage_hidden (z : ((physMove).rules.target idx).Site) :
    (actual).hidden z=L.ports.halfBits ((inIso).site.symm z) := by
  refine (congrArg (fun m : ℕ × ℕ × ℕ => m.2.1)
    (installed_measure T A u port hm hh sym rows zero conn L idx z).1).trans ?_
  exact RefreshPrepared.source_hidden T A u port hm hh sym rows zero conn L idx z

set_option maxHeartbeats 200000 in
theorem refreshWordStage_width (z : (A.Base × BitWord rem) × Fin m) :
    (actual).rootWidth z=L.ports.halfBits ((inIso).site.symm z)+(selected).ports.halfBits z := by
  have same := congrArg (fun m : ℕ × ℕ × ℕ => m.2.2)
    (installed_measure T A u port hm hh sym rows zero conn L idx z).1
  exact same.trans (RefreshPrepared.source_width T A u port hm hh sym rows zero conn L idx z)

set_option maxHeartbeats 200000 in
/-- The root issued by the refresh move is the original selected party tree. -/
theorem refreshWordStage_within (z : ((physMove).rules.target idx).Site) :
    Tree.Within 3 ((actual).root z) :=
  (installed_measure T A u port hm hh sym rows zero conn L idx z).2 3
    (RefreshPrepared.source_within T A u port hm hh sym rows zero conn L idx z)

set_option maxHeartbeats 300000 in
/-- The physical move uses the same party tree, input half bits, and copy count
as the selected row of the finite table. -/
theorem refreshWordStage_price (z : (A.Base × BitWord rem) × Fin m) (K height : ℕ)
    (fee : RefreshTies.refreshTariff c (fun a=>T.base (T.winner inputGraph port inputWidth a))
      (T.entry inputGraph port inputWidth) z.1 z.2 ≤ K)
    (room : HistogramTileNetwork.siteHeight (T.repeats inputGraph port inputWidth z.1)
      (T.entry inputGraph port inputWidth z.1).bitCap ≤ height) :
    (actual).freshResources z ≤ (2+K)*(height+1)^3*(1+(L.ports.halfBits ((inIso).site.symm z)+
      (selected).ports.halfBits z)+T.repeats inputGraph port inputWidth z.1) := by
  have billed := RefreshPrepared.source_price T A u port hm hh sym rows zero conn L idx z K height fee room
  exact (refreshWordStage_cost T A u port hm hh sym rows zero conn L idx z).le.trans billed


end
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
