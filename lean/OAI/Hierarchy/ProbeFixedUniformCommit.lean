import OAI.Hierarchy.ProbeFixedPaidOperandWork
import OAI.Hierarchy.ProbeFixedUniformBatch
import OAI.Hierarchy.ProbeFixedUniformMarket
import OAI.Hierarchy.ProtocolRAMCommitPacketWork
import OAI.Hierarchy.ProtocolRAMPricedCommitResources

namespace OAI
/-! # Uniform text and per-height clock of the priced stock commit -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe StripDirectory StripChart CatalogueRows
open PurchaseStage PurchaseFrozen BoughtSockets StockCommit RepairHistogram
open scoped Classical

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

private def packetBound := packetWorkCap v.menu.alphabet (v.stripPorts (publicStages v.W)) v.menu.maximum v.ballotWork

private def operandBound :=
  let D := v.stripPorts (publicStages v.W)
  6 + v.packetBound + (1+D*(7+v.packetBound*8+2)) +
    (1+D*(7+(v.coordinateWork+1)*8+2)) + 16*(v.paidOperandWork+1)

private def commitRows :=
  let N := publicStages v.W
  let rows := treeRowsFactor (2^v.W) k v.sampler.degree v.depth
  rows+rows*v.stripPorts N+(1+N*(2*k))

private theorem slot_work {A E : Type*} [Fintype E] (ch : Channels A E) (head : PortHeader) (sink U : ℕ)
    (small : ∀ i,(ch.address i).work≤U) :
    (StripDirectory.destination head sink (PortPadding.extend ch.slot none)).work ≤
      1+head.ports*(7+(U+1)*8+2) := by
  have real (j) : ((ch.slot j).getD (.lit sink)).work≤U+1 := by
    unfold Channels.slot
    cases h : ch.account ((Fintype.equivFin _).symm j) with
    | none => exact Nat.le_add_left 1 U
    | some i => exact (small i).trans (Nat.le_add_right ..)
  have padded (i : Fin head.ports) : ((PortPadding.extend ch.slot none i).getD (.lit sink)).work≤U+1 := by
    unfold PortPadding.extend
    split
    · exact real _
    · exact Nat.le_add_left 1 U
  exact choose_work_bound _ 0 ((U+1)*8) _ head.fieldTerm
    (fun i => (substitute_work _ head.ballTerm).trans (Nat.mul_le_mul_right 8 (padded i)))

private theorem padded_slot_work {z d k q : ℕ} {A E : Type*} [Fintype E] (ch : Channels A E)
    (src : Format z d k q (Fintype.card E)) (ports start U : ℕ) (small : ∀ i,(ch.address i).work≤U) :
    (PortPadding.format ports start ch.slot src).stockSource.slot.work ≤ 1+ports*(7+(U+1)*8+2) :=
  slot_work ch ⟨start,src.market.rows,ports⟩ src.coordinates U small

variable (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "N" => Stages h (2^v.W)
local notation "D" => v.stripPorts N
local notation "sig" => (catalogue F (v.configured (v.seed P h width)) v.cost).alphabet
local notation "B" => v.nativeBoards P h width
local notation "fm" => v.nativeFormats P h width
local notation "W" => wordBits h (2^v.W) copies

private theorem wide_commit_shape (a : Attempt) :
    (fm a).pricedArea.rows≤2^h*v.commitRows ∧ (fm a).pricedArea.occurrences≤2^h*v.commitRows ∧
    (fm a).pricedArea.goods≤2^h*v.commitRows := by
  let rows := treeRowsFactor (2^v.W) k v.sampler.degree v.depth
  have n : N=publicStages v.W := fixed_stage_count h v.W
  have size := v.discrepancy_scan_rows P h width a
  have rowEq : (fm a).pricedArea.rows=rows*2^h := by cases a <;> exact size
  have occEq : (fm a).pricedArea.occurrences=(fm a).pricedArea.rows*D := by cases a <;> rfl
  have goodsEq : (fm a).pricedArea.goods=(1+N*(2*k))*2^h := by cases a <;> rfl
  have r : rows≤v.commitRows := by dsimp only [commitRows,rows];omega
  have d : rows*(v.stripPorts (publicStages v.W))≤v.commitRows := by dsimp only [commitRows,rows];omega
  have g : 1+(publicStages v.W)*(2*k)≤v.commitRows := by dsimp only [commitRows];omega
  refine ⟨?_,?_,?_⟩
  · rw [rowEq,Nat.mul_comm rows (2^h)]
    exact Nat.mul_le_mul_left _ r
  · rw [occEq,rowEq,n,Nat.mul_comm rows (2^h),Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ d
  · rw [goodsEq,n,Nat.mul_comm (1+publicStages v.W*(2*k)) (2^h)]
    exact Nat.mul_le_mul_left _ g

set_option maxHeartbeats 800000 in
private theorem compiled_slot {q₀ : ℕ} (s : StripChart.Boards h (2^v.W) k q₀ v.depth)
    (a : Attempt) (incoming : ℕ) :
    (StripChart.build F s a incoming).stockSource.slot.work ≤ 1+D*(7+(v.coordinateWork+1)*8+2) := by
  cases a with
  | outer phase trial =>
    dsimp only [StripChart.build, StripChart.shape, StripDirectory.payloadGeometry, PortPadding.Geometry.build]
    apply padded_slot_work (payloadChannels h N k)
    exact v.payload_coordinate h
  | inner phase trial j tick =>
    dsimp only [StripChart.build, StripChart.shape, StripDirectory.purchasedGeometry, PortPadding.Geometry.build]
    let sh := (s.outer phase trial).market.shelf
    let start := s.stratumHeader phase trial
    apply padded_slot_work (purchasedChannels (z:=h) (d:=2^v.W) (k:=k) sh s.sampler v.depth start)
    exact v.purchased_coordinate h sh s.sampler (StripDirectory.stratumHeader h (2^v.W) k s.sampler.degree v.depth start)

private theorem wide_commit_slot (a : Attempt) :
    (fm a).stockSource.slot.work ≤ 1+D*(7+(v.coordinateWork+1)*8+2) :=
  v.compiled_slot h B a (resolvedStock v.mesh (v.privateArena P h width) (P).joint.initial
    (StripChart.build F B) a)

set_option maxHeartbeats 1000000 in
/-- Clock and text of the actual commit, for arbitrary physical settlement bank addresses. -/
theorem wide_commit_resources (r : ℕ) (routes : RouteSettlement.Banks) (src tab dst : ℕ)
    (owners : Bank) (a : Attempt) :
    let C := v.nativeChart P h width r routes src tab dst owners
    (C.commit a).ticks ≤ pricedTimeCap v.commitRows v.operandBound*2^h ∧
      text (C.commit a).native ≤ pricedTextCap v.operandBound := by
  let f := fm a
  let b := enabledBatch f.market.layout f.board
  let g := v.stamp P h width r routes src tab dst owners a
  let head := f.occurrenceHeader (StripChart.start B a)
  let D₀ := v.stripPorts (publicStages v.W)
  let K := v.packetBound
  have n : N=publicStages v.W := fixed_stage_count h v.W
  have roles : D=D₀ := congrArg v.stripPorts n
  have alpha : sig=v.menu.alphabet := (v.catalogue_words (v.seed P h width) width).1
  have maxW : f.board.batch.maxWidth=v.menu.maximum := (v.ordinary_dimensions P h width a).1
  have cap : packetWorkCap sig D f.board.batch.maxWidth v.ballotWork=K :=
    ((congrArg (fun m => packetWorkCap sig D m v.ballotWork) maxW).trans
      (congrArg (fun d => packetWorkCap sig d v.menu.maximum v.ballotWork) roles)).trans
      (congrArg (fun q => packetWorkCap q D₀ v.menu.maximum v.ballotWork) alpha)
  have basic := packet_work f.market.layout f.board f.stockSource.price (v.native_row_work P h width a)
  change (∀i,(b.wire (f.board.wire i)).work≤packetWorkCap sig D f.board.batch.maxWidth v.ballotWork) ∧
    (∀i,(debit b i).work≤packetWorkCap sig D f.board.batch.maxWidth v.ballotWork) ∧
    (broadcastTerm b f.stockSource.price).work≤packetWorkCap sig D f.board.batch.maxWidth v.ballotWork at basic
  rw [cap] at basic
  have credit := choose_work_bound D 0 (K*8) _ head.fieldTerm (fun i =>
    (substitute_work (b.wire (f.board.wire i)) head.ballTerm).trans (Nat.mul_le_mul_right 8 (basic.1 i)))
  have debitCost := choose_work_bound D 0 (K*8) _ head.fieldTerm (fun i =>
    (substitute_work (debit b i) head.ballTerm).trans (Nat.mul_le_mul_right 8 (basic.2.1 i)))
  have sealed : f.withOccurrenceHeader (StripChart.start B a)=f :=
    occurrence_sealed F B v.mesh (v.privateArena P h width) (P).joint.initial a
  have bankCredit : f.stockSource.credit.work≤1+D*(7+K*8+2) :=
    (congrArg (fun x : Format h (2^v.W) k sig D => x.stockSource.credit.work) sealed).symm.le.trans credit
  have bankDebit : f.stockSource.charge.work≤1+D*(7+K*8+2) :=
    (congrArg (fun x : Format h (2^v.W) k sig D => x.stockSource.charge.work) sealed).symm.le.trans debitCost
  have fee : (g.geometry 5).work≤16 := (P).catalogue.select_work (P).catalogue.core.lengthCode (.lit 1)
  have edge := (v.wide_paid_operand_work h width r routes src tab dst owners a).1
  have label := (substitute_work (g.geometry 5) g.edge).trans (Nat.mul_le_mul fee (Nat.add_le_add_right edge 1))
  have banks := v.wide_commit_slot h width a
  have bounds := v.wide_commit_shape h width a
  have mode : f.stockSource.mode.work=6 := rfl
  have resources := priced_resources f.pricedArea f.stockSource g b W h v.commitRows v.operandBound
    bounds.1 bounds.2.1 bounds.2.2 (banks.trans (by rw [roles];dsimp only [operandBound,D₀];omega))
    (bankCredit.trans (by rw [roles];dsimp only [operandBound,D₀,K];omega))
    (bankDebit.trans (by rw [roles];dsimp only [operandBound,D₀,K];omega))
    (by rw [mode];dsimp only [operandBound];omega)
    (basic.2.2.trans (by dsimp only [operandBound,K];omega))
    (label.trans (by dsimp only [operandBound];omega))
  exact resources

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage ProbeStage.Native CoreBoard ReportSockets CatalystArchive StripChart StockCommit
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

/-- A single constant bounds the text at all dates and the commit time per input row. -/
theorem wide_uniform_commit :
    ∃ K : ℕ, ∀ h width : ℕ, ∀ a : Attempt, Event.attempt a∈events v.mesh →
      let P:=v.widePlacement h width
      let C:=v.wideSignedChart h width (v.fixedTerminalStock P h width)
      (C.commit a).ticks≤K*2^h ∧ ProbeStage.Native.text (C.commit a).native≤K := by
  refine ⟨max (pricedTimeCap v.commitRows v.operandBound) (pricedTextCap v.operandBound),?_⟩
  intro h width a _
  let P := v.widePlacement h width
  let stock := v.fixedTerminalStock P h width
  let page := v.wideSignedPage h width stock
  let r := Fintype.card (CoreRoute.Slots h (2^v.W) k)
  let ledger := ownerLedger (v.nativeBoards P h width) v.mesh P.catalogue P.routes F (v.privateArena P h width)
  let count := rowOnlyCount v.mesh (declaredRows v.mesh ledger)
  let owners := sinkBank (v.catalystStaticStart P h width) count r P.catalogue.rows
  obtain ⟨clock,size⟩ := v.wide_commit_resources h width r (TerminalLayout.settlement page stock)
    (TerminalLayout.source page) (TerminalLayout.table page) (TerminalLayout.destination page) owners a
  exact ⟨clock.trans (Nat.mul_le_mul_right _ (le_max_left ..)),size.trans (le_max_right ..)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
