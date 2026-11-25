import OAI.ThreeFlat.Diagonal.PhysicalRefreshStageDepth
import OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage

namespace OAI
/-! # Depth of the numbered refresh source and its installed output -/

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

/-- The staged table constructor uses the same tree at each numbered site. -/
theorem RefreshPrepared.source_within (z : (A.Base × BitWord rem) × Fin m) :
    Tree.Within 3 ((RefreshPrepared.sourceStage T A u port hm hh sym rows zero conn L idx).root z) :=
  refreshInputStage_within T A u port hm hh sym rows zero conn L idx
    (selectedBits T A u port hm hh sym rows zero conn idx)
    (outputWords (Pins:=Pins) T A u port hm hh sym rows zero conn idx)
    (outputShape T A u port hm hh sym rows zero conn idx)
    (selectedOutput T A u port hm hh sym rows zero conn L idx)
    (issuedWords T A u port hm hh sym rows zero conn L idx) z

/-- Relabeling the output form preserves every site's depth at its original bound. -/
def RefreshPrepared.PreservesWithin {K P : Type} [Field K] {s : Shape}
    {r : Rewrite s K} {j : Fin r.count} {input : Form s P} {out₁ out₂ : Form (r.target j) P}
    (install : Stage r j input out₁ → Stage r j input out₂) : Prop :=
  ∀ (stage : Stage r j input out₁) (k : ℕ) (z : (r.target j).Site),
    Tree.Within k (stage.root z) → Tree.Within k ((install stage).root z)

set_option maxRecDepth 7000 in
theorem RefreshPrepared.install_within :
    RefreshPrepared.PreservesWithin (RefreshPrepared.install T A u port hm hh sym rows zero conn L idx) := by
  intro stage k z bound
  exact bound

end
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
