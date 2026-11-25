import OAI.Hierarchy.ProbeFixedPriorPaidCore
import OAI.Hierarchy.ProbeFixedWidePaidOperands
import OAI.Hierarchy.ProbeFixedForestHeaderBound
import OAI.Hierarchy.ProtocolRAMStripForestHeaderFits

namespace OAI
/-! # Direct and second-radius debits retain their original edge throughout the calendar -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing
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

open StripChart StripDirectory BoughtSockets
open ProbeStage.Native ThreeFlat.RAM.DescriptorExpr
local notation "gs" => v.stamp P h width r banks (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) owners
local notation "tr" => v.nativeTrees P h width
local notation "floor" => (A).endAddress v.mesh
local notation "b" => (P).catalogue
local notation "bs" => v.nativeBoards P h width
local notation "site" => v.located (v.seed P h width) P width

/-- The second-radius checker has a syntactic flag lookup for a bought edge.
Every one of its actual raw operands is instead a core row or the sentinel;
both branches produce precisely the original raw word. -/
private theorem checked_raw {W : ℕ} (board : CatalogueRows.Board) (x : Expr) (m : Memory W) (wordArg : Word W)
    (room : board.rows<2^W) (range : (x.eval m wordArg).val<board.coreRows ∨ (x.eval m wordArg).val=board.rows) :
    (board.checkedEdge x).eval m wordArg=x.eval m wordArg := by
  apply Fin.ext
  rw [board.checkedEdge_val _ _ _ room]
  rcases range with real | sentinel
  · rw [ite_eq_left real]
  · have low : board.coreRows≤board.rows:=Nat.le_add_right ..
    rw [sentinel,ite_eq_right (Nat.not_lt.mpr low),ite_eq_right (Nat.lt_irrefl _)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2800000 in
private theorem elapsed_operands (a : Attempt) (limit : ℕ)
    (past : (A).base v.mesh (.attempt a)≤limit) (word : limit<2^w) (room : (b).rows<2^w) :
    (∀i,(StripChart.id F bs b a i).Fits w limit) ∧
      ∀mask mate,(tr a).catalystMate=some (mask,mate) →
        mask.Fits w limit ∧ ∃raw : Expr,mate=(b).checkedEdge raw ∧ raw.Fits w limit ∧
          ∀(m : Memory w) (r₀ : Word w),(raw.eval m r₀).val<(b).coreRows ∨ (raw.eval m r₀).val=(b).rows := by
  let : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  have first : (A).first≤limit:=(Nat.le_add_right ..).trans past
  have coreEnd:=(v.wideGeometryPrefix h width).2.2.trans ((v.catalyst_initial_le_first P h width).trans first)
  obtain ⟨_,indices,cols,atlas,keys⟩:=v.diagnostic_original h (WideMemory.K h v.W)
    (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs)
    (WideMemory.R v.sampler h v.W k) 0 (v.wideSources h width).2 limit coreEnd word
  let sample : Edges v.sampler h D k:=.inl (.inl ((.inl ⟨0,by positivity⟩ : Columns h D),⟨0,v.positive⟩,false))
  have nonempty : 0<(b).coreRows:=(Nat.zero_le _).trans_lt ((v.wideOrder h width).symm sample).isLt
  have ports := v.chronological_ports P h width a limit word past indices cols atlas keys
  refine ⟨v.native_price_tags P h width a limit word past ports, ?_⟩
  let hand := StripChart.header F (v.mounted (v.seed P h width) P width) a
  let tree := originalTree site v.mesh b (P).routes F (v.publicHeader P h width).payloadTree.base a
  have header : hand.stop≤limit := (v.forest_header_before P h width a).trans first
  intro mask mate issued
  exact StripChart.forest_pair_at site v.mesh b (P).routes hand tree a header word room nonempty ports
    mask mate issued

/-- A physical second-radius word at any scheduled date is either core or disposable. -/
theorem prior_mate_range (a : Attempt) (scheduled : Event.attempt a∈es)
    (word : floor<2^w) (room : (b).rows<2^w) (mask mate : Expr)
    (issued : (tr a).catalystMate=some (mask,mate)) (m : Memory w) (r₀ : Word w) :
    (b).CoreOrPad (mate.eval m r₀) := by
  have past : (A).base v.mesh (.attempt a)≤until (.attempt a):=Nat.le_add_right ..
  obtain ⟨_,raw,hmate,_,valid⟩:=(v.elapsed_operands h width a _ past
    (((A).within v.mesh _ scheduled).trans_lt word) room).2 mask mate issued
  rw [hmate, checked_raw b raw m r₀ room (valid _ _)]
  exact valid m r₀

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2800000 in
theorem elapsed_pair_words (a : Attempt) (left right : Memory w) (limit : ℕ)
    (past : (A).base v.mesh (.attempt a)≤limit) (word : limit<2^w) (room : (b).rows<2^w)
    (agree : PrefixAgreement.Low limit left right) :
    (∀r₀ : Word w,((gs a).edge.eval left r₀)=(gs a).edge.eval right r₀) ∧
    ∀mask mate,(tr a).catalystMate=some (mask,mate) →
      ∀r₀ : Word w,mask.eval left r₀=mask.eval right r₀ ∧ mate.eval left r₀=mate.eval right r₀ := by
  have ops:=v.elapsed_operands h width a limit past word room
  have read (x : Expr) (small : x.Fits w limit) (r₀ : Word w) : x.eval left r₀=x.eval right r₀ :=
    PrefixAgreement.expr x left right limit (PrefixAgreement.inputEnd_of_fits x small) agree r₀
  constructor
  · have role := v.native_price_role P h width a limit word past
    exact read _ ⟨choose_fits_bound _ _ _ _ ops.1 role,trivial⟩
  · intro mask mate issued r₀
    obtain ⟨maskFits,raw,rfl,rawFits,valid⟩:=ops.2 mask mate issued
    exact ⟨read _ maskFits _,(checked_raw b raw left r₀ room (valid _ _)).trans
      ((read raw rawFits _).trans (checked_raw b raw right r₀ room (valid _ _)).symm)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2800000 in
theorem prior_paid_pair_low (chk now : Memory w) (a : Attempt)
    (low : PrefixAgreement.Low (until (.attempt a)) chk now) (word : floor<2^w) (room : (b).rows<2^w)
    (occurred : Event.attempt a∈es) (edge : Fin (b).rows) :
    let direct:=PaidWidths.paidDirect (f a).pricedArea (f a).stockSource (gs a)
    direct.load chk edge=direct.load now edge ∧
      ∀mask mate,(tr a).catalystMate=some (mask,mate) →
        let second:=PaidWidths.paidMate (f a).pricedArea (f a).stockSource mask mate
        second.load chk edge=second.load now edge := by
  intro direct
  let cap:=until (.attempt a)
  have earlier : (A).base v.mesh (.attempt a)≤cap:=Nat.le_add_right ..
  have fits : cap<2^w:=((A).within v.mesh (.attempt a) occurred).trans_lt word
  have same:=v.elapsed_pair_words h width a chk now cap earlier fits room low
  have bank:=(v.prior_amount_banks h width a occurred word).1
  let amount : Expr:=.lookup (PaidWidths.archivedBank (f a).pricedArea.direct (f a).pricedArea.occurrences) .row
  have amountFits : amount.Fits w cap:=⟨bank,trivial⟩
  have credit (r₀ : Word w) : amount.eval chk r₀=amount.eval now r₀ :=
    PrefixAgreement.expr amount chk now cap (PrefixAgreement.inputEnd_of_fits _ amountFits) low r₀
  constructor
  · apply Finset.sum_congr rfl
    intro i _
    change (if ((gs a).edge.eval chk _).val=edge.val then (amount.eval chk _).val else 0)=
      (if ((gs a).edge.eval now _).val=edge.val then (amount.eval now _).val else 0)
    rw [same.1,credit]
  · intro mask mate issued second
    apply Finset.sum_congr rfl
    intro i _
    have fields:=same.2 mask mate issued (i.val:Word w)
    change (if (mate.eval chk _).val=edge.val then
        (if Comparison.eq.test (mask.eval chk (i.val:Word w)) 0 then (0:Word w) else amount.eval chk (i.val:Word w)).val else 0)=
      (if (mate.eval now _).val=edge.val then
        (if Comparison.eq.test (mask.eval now (i.val:Word w)) 0 then (0:Word w) else amount.eval now (i.val:Word w)).val else 0)
    rw [fields.2,fields.1,credit]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2800000 in
theorem prior_paid_pair (m : Memory w) (active : Calendar.mounted C es m) (word : floor<2^w) (room : (b).rows<2^w)
    (t : Fin (es).length) (j : ℕ) (past : t.val<j) (last : j≤(es).length)
    (a : Attempt) (date : (es).get t=.attempt a) (edge : Fin (b).rows) :
    let chk:=checkedOut C floor m
    let now:=StockBound.state C m j
    let direct:=PaidWidths.paidDirect (f a).pricedArea (f a).stockSource (gs a)
    direct.load chk edge=direct.load now edge ∧
      ∀mask mate,(tr a).catalystMate=some (mask,mate) →
        let second:=PaidWidths.paidMate (f a).pricedArea (f a).stockSource mask mate
        second.load chk edge=second.load now edge := by
  intro chk now direct
  have occurred : Event.attempt a∈es:=date ▸ (es).get_mem t
  have low : PrefixAgreement.Low (until (.attempt a)) chk now:=date ▸ v.prior_paid_low h width m active t j past last
  exact v.prior_paid_pair_low h width chk now a low word room occurred edge

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
