import OAI.Hierarchy.ProbeFixedPriorPaidPair
import OAI.Hierarchy.TaggedWireGuardedPortRead
import OAI.Hierarchy.TaggedWirePaidPrefixFrame
import OAI.Hierarchy.ProtocolRAMPaidProductFits

namespace OAI
/-! # Original broadcast forest after an elapsed purchase -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing
open StripChart StripDirectory BoughtSockets ReportSockets TaggedShorterSupergroups
attribute [local irreducible] permutationFabric

private theorem forest_clamped {h₀ d k₀ n W₀ : ℕ} {S : PurchaseSampler} {B : Type*}
    (p₀ : StripPorts S h₀ d k₀ (Strip.TreeColumn n) (Fin n) B) (bb : CatalogueRows.Board)
    (start₀ rows : ℕ) (mem : Memory W₀) (u : Word W₀) (room : bb.rows<2^W₀) (positive : 0<bb.coreRows) :
    (((stripTree p₀ bb start₀ rows).edge.eval mem u).val)<bb.coreRows := by
  have core : bb.coreRows<2^W₀:=by unfold Board.rows at room;omega
  let hdr:=treeHeader start₀ rows n k₀
  change ((chooseField hdr.ports 0 _ hdr.fieldTerm).eval mem u).val<bb.coreRows
  apply StripChart.choice_has 0 _ _ mem u (fun y=>y.val<bb.coreRows) (by simpa using positive)
  intro i
  rw [eval_atRow]
  simp only [Board.treeEdge,Expr.eval,ThreeFlat.RAM.DescriptorExpr.Comparison.test,Fin.lt_def,decide_eq_true_eq,Fin.val_cast_of_lt core]
  split_ifs with valid
  · exact valid
  · simpa using positive

set_option maxHeartbeats 1000000 in
private theorem mounted_forest_words {z W k q depth bits limit : ℕ}
    (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
    (G : PortBanks ((c.inject+c.cool)*c.outerFuel)) (F : Type*) [Field F]
    [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
    (base : ℕ) (installed : StockCommit.PortHeader) (a : Attempt)
    (hit : Event.attempt a ∈ events c) (word : limit < 2^bits)
    (tables : (boughtPage s c b G F base).stop ≤ limit) (ports : DatePortFits s c b G bits limit a)
    (room : b.rows < 2^bits) (positive : 0 < b.coreRows) :
    let old := originalTree s c b G F base a
    let tree := forestAtHeader s c b G installed old a
    tree.sourceRow.Fits bits limit ∧ ∃ raw : Expr, tree.edge = b.checkedEdge raw ∧
      raw.Fits bits limit ∧ ∀ (mem : Memory bits) (reg : Word bits), (raw.eval mem reg).val < b.coreRows := by
  intro old tree
  have below : (payloadPage s c b G F base).stop ≤ (boughtPage s c b G F base).stop :=
    Nat.le_add_right _ _
  have fit : old.edge.Fits bits limit ∧ old.sourceRow.Fits bits limit := by
    dsimp only [old]
    cases a with
    | outer phase trial =>
      exact stripTree_fits _ b _ _ ((treeHeader_bound s c b G F base _ _ hit).trans
        (below.trans tables)) word ports
    | inner phase trial slice tick =>
      exact stripTree_fits _ b _ _ ((treeHeader_bound s c b G F (payloadPage s c b G F base).stop
        _ _ hit).trans tables) word ports
  have bound : ∀ (mem : Memory bits) (reg : Word bits), (old.edge.eval mem reg).val < b.coreRows := by
    intro mem reg
    dsimp only [old]
    cases a with
    | outer phase trial =>
      let a₀ := Attempt.outer phase trial
      exact forest_clamped (payloadPortsAt s c G) b
        (pageStart (payloadPage s c b G F base) c a₀) (treeRows s c b G F a₀) mem reg room positive
    | inner phase trial slice tick =>
      let a₀ := Attempt.inner phase trial slice tick
      exact forest_clamped (boughtPortsAt s c b G phase trial) b
        (pageStart (boughtPage s c b G F base) c a₀) (treeRows s c b G F a₀) mem reg room positive
  exact ⟨fit.2,old.edge,rfl,fit.1,bound⟩

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
set_option quotPrecheck false
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "w" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
local notation "f" => v.nativeFormats P h width
local notation "r" => Fintype.card (Slots h D k)
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh (P).catalogue (P).routes F A))
local notation "start" => v.catalystStaticStart P h width
local notation "page" => v.wideSignedPage h width stock
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "banks" => TerminalLayout.settlement page stock
local notation "es" => events v.mesh
local notation "until" => fun e=>(A).base v.mesh e+(A).stride

open ProbeStage.Native
local notation "gs" => v.stamp P h width r banks (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) owners
local notation "tr" => v.nativeTrees P h width
local notation "floor" => (A).endAddress v.mesh
local notation "b" => (P).catalogue
local notation "bs" => v.nativeBoards P h width
local notation "site" => v.located (v.seed P h width) P width
local notation "ported" => withPorts site v.mesh b (P).routes

set_option cleanup.letToHave false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2800000 in
theorem elapsed_forest_words (a : Attempt) (hit : Event.attempt a∈es)
    (limit : ℕ) (past : (A).base v.mesh (.attempt a)≤limit)
    (word : limit<2^w) (room : (b).rows<2^w) :
    (tr a).sourceRow.Fits w limit ∧ ∃ raw : Expr, (tr a).edge=(b).checkedEdge raw ∧
      raw.Fits w limit ∧ ∀(mem : Memory w) (u : Word w), (raw.eval mem u).val<(b).coreRows := by
  let : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  let coreEdge : Edges v.sampler h D k:=.inl (.inl ((.inl ⟨0,by positivity⟩ : Columns h D),⟨0,v.positive⟩,false))
  have positive : 0<(b).coreRows:=(Nat.zero_le _).trans_lt ((v.wideOrder h width).symm coreEdge).isLt
  have first : (A).first≤limit:=(Nat.le_add_right ..).trans past
  have coreEnd:=(v.wideGeometryPrefix h width).2.2.trans ((v.catalyst_initial_le_first P h width).trans first)
  obtain ⟨_,indices,cols,atlas,keys⟩:=v.diagnostic_original h (WideMemory.K h v.W)
    (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs)
    (WideMemory.R v.sampler h v.W k) 0 (v.wideSources h width).2 limit coreEnd word
  have ports:=v.chronological_ports P h width a limit word past indices cols atlas keys
  let H:=v.publicHeader P h width
  let srcPage:=payloadPage site v.mesh b (P).routes F H.payloadTree.base
  have pageEq : srcPage=H.payloadTree:=v.paidTreePage_eq P h width H.payloadTree.base _
  have both : boughtPage site v.mesh b (P).routes F H.payloadTree.base=H.boughtTree:=by
    change treePage site v.mesh b (P).routes F srcPage.stop _=_
    rw [pageEq]
    exact v.paidTreePage_eq P h width H.payloadTree.stop _
  have lastTable : (boughtPage site v.mesh b (P).routes F H.payloadTree.base).stop≤limit:=by
    rw [both]
    exact (show H.boughtTree.stop≤(A).first from
      (Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P h width)).trans first
  let hand := StripChart.header F (v.mounted (v.seed P h width) P width) a
  exact mounted_forest_words (z:=h) (W:=v.W) (k:=k) (depth:=v.depth)
    site v.mesh b (P).routes F H.payloadTree.base hand a hit word lastTable ports room positive

theorem wide_prior_forest_low (left right : Memory w) (endWord : floor<2^w) (boardRoom : (b).rows<2^w)
    (bits : ℕ) (a : Attempt) (live : Event.attempt a∈es) (low : PrefixAgreement.Low (until (.attempt a)) left right)
    (edge : Fin (b).rows) :
    let ar:=(f a).pricedArea
    let tree:=tr a
    let s:=PaidWidths.paidBroadcast ar tree.positions tree.owner tree.parity tree.edge tree.sourceRow (f a).board.batch.copies bits
    s.load left edge=s.load right edge := by
  intro ar tree sl
  let limit:=until (.attempt a)
  have room : limit<2^w:=((A).within v.mesh (.attempt a) live).trans_lt endWord
  obtain ⟨owner,x,found,fit,core⟩:=v.elapsed_forest_words h width a live limit (Nat.le_add_right ..) room boardRoom
  have saved:=(v.prior_amount_banks h width a live endWord).2
  have qty : sl.amount.Fits w limit:=PaidAmount.product_fits _ _ _ trivial ⟨saved,owner⟩
  apply sl.load_congr left right
  · intro i
    exact PrefixAgreement.expr sl.amount left right limit (PrefixAgreement.inputEnd_of_fits _ qty) low _
  · intro i _
    change (tree.edge.eval left _)=(tree.edge.eval right _)
    rw [found,(b).checked_core_value x left _ boardRoom (Or.inl (core _ _)),
      (b).checked_core_value x right _ boardRoom (Or.inl (core _ _))]
    exact PrefixAgreement.expr x left right limit (PrefixAgreement.inputEnd_of_fits _ fit) low _


theorem wide_prior_forest (m : Memory w) (active : Calendar.mounted C es m) (endWord : floor<2^w) (boardRoom : (b).rows<2^w)
    (bits : ℕ) (t : Fin (es).length) (j : ℕ) (past : t.val<j) (last : j≤(es).length)
    (a : Attempt) (date : (es).get t=.attempt a) (edge : Fin (b).rows) :
    let ar:=(f a).pricedArea
    let tree:=tr a
    let s:=PaidWidths.paidBroadcast ar tree.positions tree.owner tree.parity tree.edge tree.sourceRow (f a).board.batch.copies bits
    s.load (checkedOut C floor m) edge=s.load (StockBound.state C m j) edge := by
  exact v.wide_prior_forest_low h width _ _ endWord boardRoom bits a (date ▸ (es).get_mem t)
    (date ▸ v.prior_paid_low h width m active t j past last) edge

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
