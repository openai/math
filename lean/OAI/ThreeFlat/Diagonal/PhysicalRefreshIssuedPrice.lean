import OAI.ThreeFlat.Diagonal.HistoryStageCharges
import OAI.ThreeFlat.Diagonal.PhysicalRefreshIssuedStage
import OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedDepth

namespace OAI
/-! # Resource and depth measurements through the selected refresh installer -/

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

open private combine rewriteAgreement installedOutputAgreement
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshIssuedStage

/-- Measure a stage returned by the installer through the same rule and word equalities
as the physical move. Each site's coordinates are compared before either form is evaluated. -/
private theorem combine_measure {K P : Type} [CommSemiring K]
    {s : Shape} {r : Rewrite s K} {i : Fin r.count} {old : Form s P} {out : Form (r.target i) P}
    (made : Stage r i old out)
    {s' : Shape} {r' : Rewrite s' K} {j : Fin r'.count} {old' : Form s' P} {out' : Form (r'.target j) P}
    {Y : Sort _} (use : Stage r' j old' out' → Y)
    (shapes : s=s') (rules : HEq r r') (indices : i.val=j.val)
    (inputs : HEq old old') (outputs : HEq out out')
    (sites : (r'.target j).Site=(r.target i).Site)
    (fee : Y → (r'.target j).Site → ℕ × ℕ × ℕ) (depth : ℕ → Y → (r'.target j).Site → Prop)
    (retains : ∀ stage z, fee (use stage) z = (stage.freshResources z,stage.hidden z,stage.rootWidth z) ∧
      ∀ k, Tree.Within k (stage.root z) → depth k (use stage) z)
    (z : (r'.target j).Site) :
    let installed := combine made use shapes rules indices inputs outputs
    fee installed z = (made.freshResources (cast sites z),made.hidden (cast sites z),made.rootWidth (cast sites z)) ∧
      ∀ k, Tree.Within k (made.root (cast sites z)) → depth k installed z := by
  cases shapes
  cases eq_of_heq rules
  cases (Fin.ext indices : i=j)
  cases eq_of_heq inputs
  cases eq_of_heq outputs
  exact retains made z

set_option maxHeartbeats 120000 in
private abbrev priceAt :=
  combine_measure (RefreshPrepared.sourceStage T A u port hm hh sym rows zero conn L idx)
    (RefreshPrepared.install T A u port hm hh sym rows zero conn L idx)

set_option maxHeartbeats 120000 in
private abbrev priceRule :=
  priceAt T A u port hm hh sym rows zero conn L idx rfl
    (heq_of_eq (rewriteAgreement T A u port hm hh sym rows zero conn)) rfl

set_option maxHeartbeats 120000 in
private abbrev priceInput :=
  priceRule T A u port hm hh sym rows zero conn L idx HEq.rfl

set_option maxHeartbeats 120000 in
private abbrev priceForm :=
  priceInput T A u port hm hh sym rows zero conn L idx
    (installedOutputAgreement T A u port hm hh sym rows zero conn L idx) rfl
    (fun installed site => (installed.freshResources site,installed.hidden site,installed.rootWidth site))
    (fun k installed site => Tree.Within k (installed.root site))

private def preservesMeasures {K P : Type} [Field K] {s : Shape}
    {r : Rewrite s K} {j : Fin r.count} {input : Form s P} {before after : Form (r.target j) P}
    (install : Stage r j input before → Stage r j input after) : Prop :=
  ∀ (stage : Stage r j input before) (site : (r.target j).Site),
    ((install stage).freshResources site,(install stage).hidden site,(install stage).rootWidth site) =
      (stage.freshResources site,stage.hidden site,stage.rootWidth site) ∧
    ∀ k, Tree.Within k (stage.root site) → Tree.Within k ((install stage).root site)

private theorem reform_measures {K P : Type} [Field K] {s : Shape}
    {r : Rewrite s K} {j : Fin r.count} {input : Form s P} {before after : Form (r.target j) P}
    (same : before=after) :
    preservesMeasures (fun stage : Stage r j input before => stage.reform same) := by
  intro stage site
  exact ⟨rfl,fun _ h=>h⟩

open private installNumbered selectedBits selectedOutput outputShape sameGraph sameBits sameIssuedOutput
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage

private theorem numbered_measures {K P : Type} [Field K] {d l D n : ℕ} {source : State d l}
    (r : Move K source D n) (i : Fin r.rules.count) (input : source.Words P) (output : (r.next i).Words P)
    (sites : Fintype (r.next i).Site) (edges : Fintype (((r.next i).Base × Fin D) × BitWord n))
    (graph : PortGraph (r.next i).Site (((r.next i).Base × Fin D) × BitWord n))
    (bits : ((r.next i).Base × Fin D) × BitWord n → ℕ) (word : WordLayout graph bits P)
    (shape : r.rules.target i = @WordLayout.shape _ _ sites edges graph bits)
    (graphEq : graph = (r.next i).shape.graph) (bitsEq : bits = (r.next i).width)
    (wordEq : HEq word output) :
    preservesMeasures (installNumbered r i input output sites edges graph bits word shape graphEq bitsEq wordEq) := by
  unfold installNumbered
  exact reform_measures _

set_option maxHeartbeats 110000 in
private abbrev numberedAt :=
  numbered_measures (physMove) idx L (refreshWords T A u port hm hh sym rows zero conn L idx)

set_option maxHeartbeats 110000 in
private abbrev layoutAt :=
  numberedAt T A u port hm hh sym rows zero conn L idx
    (inferInstance : Fintype ((A.Base × BitWord rem) × Fin m))
    (inferInstance : Fintype (RefreshTies.LiveSlot A.Base (BitWord rem) m (1+h+pad)))
    outGraph

set_option maxHeartbeats 110000 in
private abbrev wordsAt :=
  layoutAt T A u port hm hh sym rows zero conn L idx
    (selectedBits T A u port hm hh sym rows zero conn idx)
    (selectedOutput T A u port hm hh sym rows zero conn L idx)
    (outputShape T A u port hm hh sym rows zero conn idx)

set_option maxHeartbeats 110000 in
private abbrev install_measures :=
  wordsAt T A u port hm hh sym rows zero conn L idx
    (sameGraph T A u port hm hh sym rows zero conn idx)
    (sameBits T A u port hm hh sym rows zero conn idx)
    (sameIssuedOutput T A u port hm hh sym rows zero conn L idx)

set_option maxHeartbeats 160000 in
/-- The selected installer retains the three numerical fields and the per-site tree-depth bound. -/
abbrev refreshIssued_measure :=
  priceForm T A u port hm hh sym rows zero conn L idx
    (install_measures T A u port hm hh sym rows zero conn L idx)


end
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
