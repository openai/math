import OAI.Computability.VPVNP.PairShrinkSiteActions
import OAI.Computability.VPVNP.PairShrinkRoleSiteOperands
import OAI.Computability.VPVNP.PairShrinkOrdinalSources
import OAI.Computability.VPVNP.PairShrinkItemsOfFn
import OAI.Computability.VPVNP.PairShrinkInstalledItem

/-!
# The installed map loop at a selected shrinking site

The row cursor ranges over the site's true ordered resident occurrences. Each
occurrence reads the selected level's physical tables, gathers from the
caller’s retained packets and evaluates the grouped matrix at its own ordinal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSiteBank

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open NetworkKernel CompressorRecords DescriptorSpace ShrinkBlockInputs ShrinkSlots
open ShrinkVertexImage ShrinkMapImage.Registers MapResidentRows ShrinkRole ShrinkRole.MapWitness
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates} {i : Fin S.steps}
variable {g w n : ℕ} {X : State (a i) (packingLaneBits (a i) g)}
variable {sel : SelectedScore.Selection B X} {v : Site X}
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
variable (site : CanonicalSite B i X sel v w n (Fintype.card B.Entry))
variable (ord : B.Entry → Fin (Fintype.card B.Entry))
variable (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
variable (old : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
    X.packingInputIso.site.symm) X.network.Half v)
variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
    (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel)) v)
local notation "side" => selectedLayout X B.shrink sel
local notation "J" => jobs B i X sel site.workspace site.positions site.blocks site.cur site.bounds
  n site.rowEnd site.older site.later v old parent
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "L" => BlockProgram.layout B site.workspace.val site.positions site.blocks
local notation "here" => Nat.cast (R := Word w) (levelStart L site.cur)
local notation "cut" => tableBase L site.cur (0 : Fin 6)
local notation "node" => site.later + (B.recordLimit + 2) *
  PortRefresh.ArgumentAddress.siteOrdinal (X.shrinkNext B.shrink (S.shrink i) sel) v

/-- The canonical fit uses the old row base and pitch of this job's packet arena. -/
private theorem job_fit (q : X.packingData.ResidentMap side v) :
    let job := J q
    let d := ShrinkPreparedCall.widthsDemand X q.1.1
    ShrinkCallFields.Fits (w := w) (n := n) (limit := site.limit)
      (t := Fintype.card B.Entry) (u := MotifConversion.repetitions B.shrink d) B.shrink
      d (sel q.1.1).val job.scratch (ShrinkMotifOrder.stateNumber X q.1.1).val
      (ShrinkCallDemandCells.cdBase X q.1.1 job.arena job.nodes) := site.fits q.1.1

variable {p r : ℕ} (M : Machine w p r 11) (pc : Fin (shrinkSegment B ord).count → Fin p)
variable (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r)
variable (reg : Fin (shrinkSegment B ord).privateRegs ↪ Fin r) (done : Fin p)
local notation "common" => shared B ord i reg
local notation "P" => mapLoop B ord i pc reg done

-- The loaded party and motif identify the row without reevaluating its energy comparison.
open private jobPublic from OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader
attribute [local irreducible] Compression.ShrinkEnergy.chosenLayout MapWitness.rowEquiv
  rowOrdinalWord rowAction ShrinkCallFields.workspace

private theorem item_change {p r k w endAddr src₀ src₁ : ℕ}
    {p₀ p₁ : ResidentMapLoop.Program p r} {machine : Machine w p r k} {mem : Memory w}
    {d : Fin 9 ↪ Fin r} {inv : Word w → Config w p r → Prop}
    {f₀ f₁ : ResidentMapLoop.Exact.Action w endAddr}
    (h : ResidentMapLoop.Exact.Item p₀ machine mem d inv src₀ f₀)
    (program : p₀ = p₁) (src : src₀ = src₁) (act : f₀ = f₁) :
    ResidentMapLoop.Exact.Item p₁ machine mem d inv src₁ f₁ := by
  subst p₁ src₁ f₁
  exact h

set_option maxHeartbeats 1200000 in
-- Instantiate the dependent stage and resident index in the host's gather and matrix banks.
/-- Execute every canonical map action with the actual installed role and live row sources. -/
theorem exact_items
    (installed : ∀ j, M.code (pc j) = ((shrinkSegment B ord).row pc dfs saved reg done j).resize w)
    (ds : ∀ j k, reg j ≠ dfs k) (ss : ∀ j k, reg j ≠ saved k)
    (H : Word w) (terminalRoom : H.val + 31 < 2 ^ w)
    (levelEq : site.level = here)
    (sources : ∀ q, RowSources B i X sel site.workspace site.positions site.blocks site.cur
      site.bounds n site.rowEnd site.older site.later v old parent site.mem H q)
    (entry : Config w p r) (expected : Word w → Word w)
    (start : SiteMapInput common dfs regions n ((node : ℕ) : Word w) site.level site.term
      expected entry)
    (fields : ∀ q : X.packingData.ResidentMap side v,
      (J q).Packets n entry.privateMem ∧ (J q).ChildWords entry.privateMem n ∧
      ShrinkCallSupplyCells.Absorbed X side (ShrinkPreparedCall.width B.shrink X sel) q.1.1
        q.1.2 (J q).scratch (q.2.symm ▸ hidden) entry.privateMem ∧
      (∀ u, (J q).arena.base ((J q).nodes u) + (J q).arena.stride ≤ (J q).scratch.hist) ∧
      (J q).arena.base (J q).node + (J q).arena.stride ≤ (J q).scratch.hist) :
    ResidentMapLoop.Exact.Items P M site.mem dfs (siteInvariant site common entry)
      (firstMap B i site.source v) (canonicalBank site ord parent old hidden) := by
  let F := matrixFamily B ord i
  let G := gatherFamily B ord i
  let locals := reloadRegs B ord i reg
  let tmp := locals (layoutTemp F G)
  have localD : ∀ j k, locals j ≠ dfs k := fun _ _ ↦ ds _ _
  have localS : ∀ j k, locals j ≠ saved k := fun _ _ ↦ ss _ _
  have banks := hosted_banks F G dfs saved locals localD localS
  have link := map_linked B ord i M (matrixPC B ord i pc) dfs saved locals done
    (selected_map_rows B ord i M pc dfs saved reg done installed)
  unfold canonicalBank MapWitness.actions
  apply ResidentMapLoop.Exact.Items.ofFn
  intro j
  let q := rowEquiv (a := a i) (g := g) X side v j
  let job := J q
  let atParty : Placed (X.packingData.shrinkInternalOwner side)
      (internalLabel (ShrinkPreparedCall.width B.shrink X sel) side)
      (X.packingData.shrinkPartySite side q.1.1 q.1.2) :=
    Eq.rec (motive := fun y _ ↦ Placed (X.packingData.shrinkInternalOwner side)
      (internalLabel (ShrinkPreparedCall.width B.shrink X sel) side) y) hidden q.2.symm
  have fit := job_fit site parent old q
  let pp := pub site.level (job.node : Word w) regions n
  let st := rowOrdinalWord (w := w) X side v j
  have pubEq : ShrinkCallABI.pub entry common = pp := by
    dsimp only [pp]
    rw [node_eq]
    exact start.pub_eq
  have hst := row_ordinal (g := g) (w := w) (B := B) (i := i) (X := X) (sel := sel) (v := v) j
  have data := source_at (g := g) (w := w) site parent old q H st levelEq hst (sources q)
  have heads := data.1
  have next := data.2
  have abArea := (sources q).abArea
  have supplyArea := (sources q).supplyArea
  rw [← levelEq] at abArea supplyArea
  have sites := job.abi_readSafe (slotDegree S) H terminalRoom heads next abArea supplyArea
  have hist := ShrinkResidentMemory.histogram_before_hidden regions n (Fintype.card B.Entry) le_rfl
  have stack : n ≤ job.scratch.hist := Nat.le_add_right ..
  have positive : 0 < w := by
    by_contra! zero
    have two := (sources q).two
    simp [Nat.eq_zero_of_le_zero zero] at two
  have pair := row_pair (g := g) (B := B) (i := i) (X := X) (sel := sel) (v := v) j
  have oldLive : job.OldPublished (ShrinkCallABI.operands (slotDegree S))
      (ShrinkCallABI.pub entry common) st site.mem site.level
      (packedIncidence L w site.cur (DemandRAM.oldCount X)) cut := by
    rw [pubEq]
    exact heads
  have args := fields q
  have live (u : Word w) (c : Config w p r) (valid : siteInvariant site common entry u c) :=
    ShrinkPartyNative.Job.liveOperands (w := w) (p := p) (r := r) (g := g)
      (endAddr := n) (n := n) (limit := site.limit) B ord i sel job atParty fit dfs saved
      common tmp entry st site.mem site.level site.term banks.2.2 start.level start.term
      start.stride start.one args.1 args.2.1 args.2.2.1 args.2.2.2.1 args.2.2.2.2 hist
      oldLive (sources q).two (sources q).termRoom (sources q).pairs (sources q).fields u c valid
  have run := ShrinkPartyNative.Job.installedItem (X := X) (w := w) (g := g)
    (endAddr := n) (n := n) (limit := site.limit) (motif := q.1.1) (party := q.1.2)
    (origin := cut) (layer := site.later) (pitch := B.recordLimit + 2)
    (T := packedIncidence L w site.cur (DemandRAM.oldCount X))
    (U := packedIncidence L w (site.cur + 1) (actualCount (levelShape (b := b i) X)))
    (absolute := ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X cut) w)
    (heads := ShrinkOutput.heads (levelShape (b := b i) X)
      (SelectedArena.roleBase X (ShrinkInput.termHead (w := w) X cut) 10)
      (tableBase L site.cur (3 : Fin 6)))
    B ord i sel job atParty fit (gatheredPC B ord i pc) dfs saved locals done M v site.mem
    site.level site.term site.source j pp site.width (siteInvariant site common entry) link
    localD localS positive pair.symm (TerminalLink.workerCell H) sites heads next stack hist (by
      intro u c valid
      have ev := live u c valid
      rw [pubEq] at ev
      exact ev)
  refine item_change run ?_ ?_ ?_
  · rfl
  · rfl
  · funext u scratch
    dsimp only [q, job, atParty, pp, MapWitness.jobInput, jobPublic, id]

end PairSimulation.ShrinkSiteBank

end VPVNP
end Computability
end OAI
