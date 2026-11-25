import OAI.Hierarchy.ProbeFixedPriceLabelFits
import OAI.Hierarchy.ProbeFixedWideGeometry
import OAI.Hierarchy.ProtocolRAMStripForestHeaderFits
import OAI.Hierarchy.ProbeFixedForestHeaderBound

namespace OAI
/-! # The complete paid-width program fits in the original fixed arena -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe ReportSockets CatalystArchive TaggedShorterSupergroups
open StripChart StripDirectory CatalogueRows BoughtSockets StockCommit
open scoped Classical
attribute [local irreducible] permutationFabric

private theorem mounted_tree_fits {z W k q depth w limit : ℕ}
    (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
    (G : PortBanks ((c.inject+c.cool)*c.outerFuel)) (F : Type*) [Field F]
    [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
    (base : ℕ) (installed : PortHeader) (a : Attempt) (occurs : Event.attempt a ∈ events c)
    (word : limit < 2^w) (tables : (boughtPage s c b G F base).stop ≤ limit)
    (headerRoom : installed.stop ≤ limit) (flag : b.bought.flag.Fits w limit)
    (ports : DatePortFits s c b G w limit a) :
    let old := originalTree s c b G F base a
    let tree := forestAtHeader s c b G installed old a
    tree.edge.Fits w limit ∧ tree.sourceRow.Fits w limit ∧ ∀ mask mate,
      tree.catalystMate = some (mask,mate) → mask.Fits w limit ∧ mate.Fits w limit := by
  intro old tree
  have below : (payloadPage s c b G F base).stop ≤ (boughtPage s c b G F base).stop :=
    Nat.le_add_right _ _
  have original : old.edge.Fits w limit ∧ old.sourceRow.Fits w limit := by
    dsimp only [old]
    cases a with
    | outer phase trial =>
      exact stripTree_fits _ b _ _ ((treeHeader_bound s c b G F base _ _ occurs).trans
        (below.trans tables)) word ports
    | inner phase trial slice tick =>
      exact stripTree_fits _ b _ _ ((treeHeader_bound s c b G F (payloadPage s c b G F base).stop
        _ _ occurs).trans tables) word ports
  exact ⟨b.checked_fits _ original.1 flag, original.2,
    forest_pair_fits (z:=z) (W:=W) (k:=k) (q:=q) (depth:=depth)
      s c b G installed old a headerRoom word flag ports⟩

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
variable (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "b" => (P).catalogue
local notation "A" => v.privateArena P h width
local notation "w" => wordBits h (2^v.W) copies
local notation "r" => Fintype.card (CoreRoute.Slots h (2^v.W) k)
local notation "top" => (A).endAddress v.mesh
local notation "H" => v.publicHeader P h width
local notation "s" => v.located (v.seed P h width) P width

set_option cleanup.letToHave false in
set_option maxHeartbeats 1000000 in
theorem wide_paid_operands (routes : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank) (a : Attempt)
    (occurs : Event.attempt a∈events v.mesh) (word : top<2^w) :
    let stamp:=v.stamp P h width r routes src tab dst owners a
    let tree:=v.nativeTrees P h width a
    stamp.edge.Fits w top ∧ tree.edge.Fits w top ∧ tree.sourceRow.Fits w top ∧
      ∀mask mate,tree.catalystMate=some (mask,mate)→mask.Fits w top ∧ mate.Fits w top := by
  intro stamp tree
  have before : (A).base v.mesh (.attempt a)≤top:=(Nat.le_add_right ..).trans ((A).within v.mesh (.attempt a) occurs)
  have first : (A).first≤top:=(Nat.le_add_right ..).trans before
  have core:=(v.wideGeometryPrefix h width).2.2.trans ((v.catalyst_initial_le_first P h width).trans first)
  have ⟨_,indices,cols,atlas,keys⟩:=v.diagnostic_original h (WideMemory.K h v.W)
    (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs)
    (WideMemory.R v.sampler h v.W k) 0 (v.wideSources h width).2 top core word
  have found:=v.wide_catalogue_sources h width routes src tab dst owners word
  let page:=payloadPage s v.mesh b (P).routes F (H).payloadTree.base
  have pageEq : page=(H).payloadTree:=v.paidTreePage_eq P h width (H).payloadTree.base _
  have both : boughtPage s v.mesh b (P).routes F (H).payloadTree.base=(H).boughtTree := by
    change treePage s v.mesh b (P).routes F page.stop _=_
    rw [pageEq]
    exact v.paidTreePage_eq P h width (H).payloadTree.stop _
  have tables : (boughtPage s v.mesh b (P).routes F (H).payloadTree.base).stop≤top := by
    rw [both]
    exact (show (H).boughtTree.stop≤(A).first from
      (Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P h width)).trans first
  have ports:=v.chronological_ports P h width a top word before indices cols atlas keys
  have tags:=v.native_price_tags P h width a top word before ports
  have role:=v.native_price_role P h width a top word before
  let hand := StripChart.header F (v.mounted (v.seed P h width) P width) a
  have handFits : hand.stop ≤ top := (v.forest_header_before P h width a).trans first
  have paid : stamp.edge.Fits w top := ⟨choose_fits_bound _ 0 _ _ tags role,trivial⟩
  exact ⟨paid, mounted_tree_fits (z:=h) (W:=v.W) (k:=k) (depth:=v.depth)
    s v.mesh b (P).routes F (H).payloadTree.base hand a occurs word tables handFits found.2.2.2.2.1 ports⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
