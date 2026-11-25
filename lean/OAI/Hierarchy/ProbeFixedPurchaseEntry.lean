import OAI.Hierarchy.ProbeFixedQuietCash
import OAI.Hierarchy.ProbeFixedBirthFees
import OAI.Hierarchy.ProbeFixedAcquisitionScale
import OAI.Hierarchy.ProbeRetainedRows
import OAI.Hierarchy.ProtocolRAMCalendarHalfRead

namespace OAI
/-! # Integer half, saved reserve, and fees at an actual native acquisition -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart
open StockCommit PurchaseStage RepairHistogram PurchaseFrozen ReportSockets
open ThreeFlat.RAM
open scoped Classical BigOperators Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "st" => v.taskCommit P z width
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "input" => v.stage P z width r banks src tab dst owners
local notation "keys" => v.cashKeys P z width r banks src tab dst owners
local notation "arena" => v.privateArena P z width

variable (mem fixture : Memory (wordBits z (2^v.W) copies)) (phase trial : ℕ)
local notation "a" => Attempt.outer phase trial
local notation "entry" => trialState C mem phase trial
local notation "snap" => postSnapshot ((C).layout a) (repair C a) (prepared C a entry)
local notation "term" => postOutput ((C).layout a) (repair C a) (prepared C a entry)
local notation "ar" => (f a).pricedArea
local notation "s" => (f a).stockSource
local notation "cut" => (arena).base v.mesh (.attempt a)
local notation "record" => StockBound.TrialData C a entry fixture ar s (g a) v.keepLimit width cut
variable (scheduled : Event.attempt (Attempt.outer phase trial) ∈ events v.mesh)
  (live : ready (v.nativeChart P z width r banks src tab dst owners) (.attempt (Attempt.outer phase trial))
    (trialState (v.nativeChart P z width r banks src tab dst owners) mem phase trial))
  (data : StockBound.TrialData (v.nativeChart P z width r banks src tab dst owners) (Attempt.outer phase trial)
    (trialState (v.nativeChart P z width r banks src tab dst owners) mem phase trial) fixture
    (v.nativeFormats P z width (Attempt.outer phase trial)).pricedArea
    (v.nativeFormats P z width (Attempt.outer phase trial)).stockSource
    (v.stamp P z width r banks src tab dst owners (Attempt.outer phase trial)) v.keepLimit width
    ((v.privateArena P z width).base v.mesh (.attempt (Attempt.outer phase trial))))
  (buy : observedMode (v.nativeChart P z width r banks src tab dst owners) mem phase trial = 3)
  (bounded : ∀ u, ((v.billedAccount P z width r banks src tab dst owners).trial
    (v.nativeChart P z width r banks src tab dst owners) mem phase trial).bits u ≤ v.keepLimit*width)

set_option maxHeartbeats 4000000 in
include live data buy in
private theorem purchase_masked_delta (j : Fin (st a).occurrences) :
    delta (st a).columns (input a entry) j = 0 := by
  obtain ⟨ports⟩ := data.ports
  have disabled := v.rows_off_of_ne P z width r banks src tab dst owners a entry live data.toTrialLayout
    (show observedMode C mem phase trial ≠ 2 by omega) (ports.enum.symm j).1
  obtain ⟨add,sub⟩ := ports.off j (by
    simpa only [StockCommit.liveRows,Finset.mem_filter,Finset.mem_univ,true_and,
      FixedProtocolFormat.ballot,FixedProtocolFormat.stage] using disabled)
  have plus : (st a).columns.credit.eval (input a entry) (j.val : Word W) = 0 := Fin.ext add
  have minus : (st a).columns.charge.eval (input a entry) (j.val : Word W) = 0 := Fin.ext sub
  simp [delta,plus,minus]

private theorem purchase_printed_mode {wordWidth alphabet goods : ℕ}
    (chart : Chart wordWidth alphabet goods) (initial : Memory wordWidth) (outerPhase outerTrial : ℕ)
    (mounted : ready chart (.attempt (.outer outerPhase outerTrial)) (trialState chart initial outerPhase outerTrial))
    (board : Board (chart.layout (.outer outerPhase outerTrial)) (repair chart (.outer outerPhase outerTrial)) wordWidth)
    (positive : 0 < (chart.layout (.outer outerPhase outerTrial)).candidates) (wide : 4 ≤ 2^wordWidth)
    (chosen : observedMode chart initial outerPhase outerTrial = 3) :
    (postOutput (chart.layout (.outer outerPhase outerTrial)) (repair chart (.outer outerPhase outerTrial))
      (prepared chart (.outer outerPhase outerTrial) (trialState chart initial outerPhase outerTrial))
      (chart.modeAt (.outer outerPhase outerTrial))).val = 3 := by
  let date := Attempt.outer outerPhase outerTrial
  let shape := chart.layout date
  let transaction := repair chart date
  let origin := prepared chart date (trialState chart initial outerPhase outerTrial)
  let image := postSnapshot shape transaction origin
  let row : Fin shape.candidates := ⟨0,positive⟩
  let outputPass : Pass := ⟨transaction.modeOut,shape.candidates,AttemptGate.mode transaction.policy⟩
  have checked : AuditReady (audits shape transaction) image := mounted.2.2.2.2.2.2.1
  have written : postOutput shape transaction origin (transaction.modeOut + row.val) =
      (AttemptGate.mode transaction.policy).eval image (row.val : Word wordWidth) :=
    post_read shape transaction origin checked board outputPass
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) row
  have evaluated := AttemptGate.mode_eval transaction.policy image (row.val : Word wordWidth)
  have code : AttemptGate.actual transaction.policy image = 3 := chosen
  have returned := written.trans evaluated
  rw [code] at returned
  change (postOutput shape transaction origin (transaction.modeOut + row.val)).val = 3
  exact (congrArg Fin.val returned).trans (Fin.val_cast_of_lt (by omega : 3 < 2^wordWidth))

private theorem purchase_priced_split {wordWidth rowCount colCount : ℕ}
    (area : Area) (sourceBank : Sources) (labels : LabelSource) (batch : Batch rowCount colCount)
    (posted initialData : Memory wordWidth) (component : Fin area.goods) (gateAddr bound oldBits : ℕ)
    (window : StockWindow area sourceBank labels gateAddr bound wordWidth) (prefixFit : PrefixFits area sourceBank batch)
    (mounted : (pricedSegment area sourceBank labels wordWidth batch).ready posted)
    (oldAt : (posted (sourceBank.old.base + component.val)).val = oldBits) (small : oldBits ≤ bound)
    (tableAt : ∀ addr, sourceBank.half.base ≤ addr → addr < sourceBank.half.base + sourceBank.half.size →
      posted addr = FeedROM.halfAdvice sourceBank.half initialData addr)
    (modeAt : (posted gateAddr).val = 3)
    (inactive : ∀ j : Fin area.occurrences, delta (area.columns sourceBank) (stageInput area sourceBank labels posted) j = 0) :
    let result := (pricedSegment area sourceBank labels wordWidth batch).after posted
    (result (area.output + component.val)).val = oldBits / 2 ∧
      (result (area.output + area.goods + component.val)).val = oldBits - oldBits / 2 ∧
      result (area.output + area.goods + area.goods + component.val) = 0 := by
  have limit : (posted (sourceBank.old.base + component.val)).val < sourceBank.half.size :=
    oldAt.le.trans_lt (small.trans_lt window.halfRoom)
  have facts := calibrated_buy area sourceBank labels batch posted initialData component prefixFit window.room
    window.capacity.1 window.old window.label window.table limit tableAt gateAddr window.mode window.modeBefore modeAt inactive
  have result := priced_buy area sourceBank labels batch posted component mounted prefixFit window.room window.wide
    window.capacity.1 window.old facts.idle facts.bought facts.half
  simpa only [oldAt] using result

set_option maxHeartbeats 4000000 in
include live data buy bounded in
private theorem purchase_priced_words (u : Commodity (Fin (2^z)) N k) :
    let index := v.nativeSlots P z width a u
    let result := (pricedSegment ar s (g a) W (b a)).after term
    let old := ((A).trial C mem phase trial).bits u
    (result ((ar).output + index.val)).val = old / 2 ∧
      (result ((ar).output + (ar).goods + index.val)).val = old - old / 2 ∧
      result ((ar).output + (ar).goods + (ar).goods + index.val) = 0 := by
  intro index result old
  have pre (addr : ℕ) (below : addr < cut) : term addr = entry addr :=
    postOutput_prior C a entry addr live ((v.event_prefix P z width r banks src tab dst owners (.attempt a) addr below).1)
  have sourceAt : (term ((s).old.base + index.val)).val = old := by
    rw [pre _ ((Nat.add_lt_add_left index.isLt _).trans_le data.oldLow)]
    change (entry ((s).old.base + index.val)).val =
      (entry ((v.nativeAccount P z width (v.issued P z width r banks src tab dst owners)).stockAt a u)).val
    exact congrArg (fun addr : ℕ => (entry addr).val)
      ((congrArg ((s).old.base + ·) (v.slot_index P z width a u)).trans
        (v.stock_pointer P z width (v.issued P z width r banks src tab dst owners) a u).symm)
  have readySegment : (pricedSegment ar s (g a) W (b a)).ready term := live.2.2.2.2.2.2.2.2.2.2.1
  exact purchase_priced_split ar s (g a) (b a) term fixture index ((C).modeAt a) (v.keepLimit*width) old
    data.window data.inputs readySegment sourceAt (bounded u)
    (fun addr lo hi => (pre addr (hi.trans_le data.halfLow)).trans (data.half addr lo hi))
    (purchase_printed_mode C mem phase trial live data.board data.positive data.window.wide buy)
    (v.purchase_masked_delta P z width r banks src tab dst owners mem fixture phase trial live data buy)

set_option maxHeartbeats 4000000 in
include scheduled live data in
private theorem purchase_retained_word (u : Commodity (Fin (2^z)) N k) :
    ((A).inner C mem phase trial 0 0).bits u =
      (((pricedSegment ar s (g a) W (b a)).after term) ((ar).output + (v.nativeSlots P z width a u).val)).val := by
  let slotMap := v.nativeSlots P z width a
  let addr := (ar).output + (slotMap u).val
  let nextDate := Attempt.inner phase trial 0 0
  let posted := after C (.attempt a) entry
  let nativeOut := ((st a).native W (f a).market.rows (b a)).after (input a entry)
  have history : ((A).inner C mem phase trial 0 0).bits u = ((A).read nextDate posted).bits u :=
    congrArg (fun image : Memory W => ((A).read nextDate image).bits u)
      ((inner_zero C mem phase trial 0).trans (reserve_zero C mem phase trial))
  have published := (v.repair_stock P z width r banks src tab dst owners a entry scheduled live data.toTrialLayout).2 (slotMap u)
  change ((A).read nextDate posted).bits (slotMap.symm (slotMap u)) = (nativeOut addr).val at published
  rw [Equiv.symm_apply_apply] at published
  have compiled : (pricedSegment ar s (g a) W (b a)).after term = nativeOut := priced_after ar s (g a) (b a) term
  exact history.trans (published.trans (congrArg (fun image : Memory W => (image addr).val) compiled.symm))

private theorem purchase_reindex_read {wordWidth : ℕ} {before afterImage : Memory wordWidth}
    {left right : ℕ} (images : before = afterImage) (slots : left = right) (base : ℕ) :
    afterImage (base + right) = before (base + left) := by
  cases images
  cases slots
  rfl

set_option maxHeartbeats 4000000 in
include scheduled live data buy bounded in
/-- The measured half and complementary saved bits at this actual three-mode
transition. Every declared commodity reads its original physical address. -/
theorem purchase_initial_stock (u : Commodity (Fin (2^z)) N k) :
    let old:=((A).trial C mem phase trial).bits u
    let m':=reserveState C mem phase trial 0
    ((A).inner C mem phase trial 0 0).bits u=old/2 ∧
      PurchaseInventory.stock ((ar).output+(ar).goods) m' u=old-old/2 ∧
      m' ((ar).output+(ar).goods+(ar).goods+PurchaseInventory.slot u)=0 := by
  intro old m'
  let result := (pricedSegment ar s (g a) W (b a)).after term
  let nativeOut := ((st a).native W (f a).market.rows (b a)).after (input a entry)
  have compiled : result = nativeOut := priced_after ar s (g a) (b a) term
  have returned : result = m' :=
    compiled.trans ((v.native_end P z width r banks src tab dst owners a entry).trans (reserve_zero C mem phase trial).symm)
  have slots := v.slot_index P z width a u
  have words := v.purchase_priced_words P z width r banks src tab dst owners mem fixture phase trial live data buy bounded u
  have retained := v.purchase_retained_word P z width r banks src tab dst owners mem fixture phase trial scheduled live data u
  exact ⟨retained.trans words.1,
    (congrArg Fin.val (purchase_reindex_read returned slots ((ar).output + (ar).goods))).trans words.2.1,
    (purchase_reindex_read returned slots ((ar).output + (ar).goods + (ar).goods)).trans words.2.2⟩

set_option maxHeartbeats 1000000 in
include scheduled live data buy bounded in
/-- All signed repair terms, tree words and spill words vanish on acquisition;
the remaining physical rows form the original candidate opening bill. -/
theorem purchase_open_bill (positive : 0<width) :
    ((A).inner C mem phase trial 0 0).paid=((A).trial C mem phase trial).paid+
      purchaseFee C mem phase trial Λ p q Q (dyadicScale v.W) := by
  let t:=st a
  let u:=input a entry
  let B:=repair C a
  let out:=(t.native W (f a).market.rows (b a)).after u
  let E:=v.nativeSlots P z width a
  obtain ⟨ports⟩:=data.ports
  have entered:=v.entered P z width r banks src tab dst owners a entry live
  have off:=v.rows_off_of_ne P z width r banks src tab dst owners a entry live data.toTrialLayout
    (show observedMode C mem phase trial≠2 by omega)
  have muted (e : Fin t.occurrences) : installedBits t.columns u e=0 ∧ consumedBits t.columns u e=0 :=
    ports.off e (by simpa only [StockCommit.liveRows,Finset.mem_filter,Finset.mem_univ,true_and,
      FixedProtocolFormat.ballot,FixedProtocolFormat.stage] using off (ports.enum.symm e).1)
  have bc:=fresh_broadcastRoom _ _ _ data.inputs data.window.room
  have noTree (j : Fin (f a).market.rows) : out (t.broadcast+j.val)=0 :=
    (t.read_broadcast (b a) u j entered bc.fits ports.termRoom ports.copyRoom ports.sumRoom (bc.keeps j)).trans
      (ite_eq_right (off j))
  have outReserve : out=reserveState C mem phase trial 0 :=
    (v.native_end P z width r banks src tab dst owners a entry).trans (reserve_zero C mem phase trial).symm
  have noSpill (i : Fin t.goods) : out (t.plan.activeOut+t.goods+t.goods+i.val)=0:=by
    have rep:=v.purchase_initial_stock P z width r banks src tab dst owners mem fixture phase trial scheduled live data
      buy bounded (E.symm i)
    have hit:PurchaseInventory.slot (E.symm i)=i.val :=
      (v.slot_index P z width a (E.symm i)).symm.trans (congrArg Fin.val (E.apply_symm_apply i))
    have column := rep.2.2
    change reserveState C mem phase trial 0
      ((ar).output+(ar).goods+(ar).goods+PurchaseInventory.slot (E.symm i))=0 at column
    rw [hit] at column
    change out ((ar).output+(ar).goods+(ar).goods+i.val)=0
    exact (congrFun outReserve _).trans column
  have amount:=t.buy_price (b a) u B.purchaseOut width (b a).copies positive entered
    (eventBoard _ _ _ data.inputs data.window.room) (keys a) (v.printedCharge P z width a)
    (fun _ _=>v.cost.atAttempt a) (v.coreCharge P z width a) (fun _=>v.openingCharge) muted noTree noSpill
  have posted:=v.posting P z width r banks src tab dst owners a entry scheduled live
  let opening (state : Memory W) : ℝ :=
    ∑ j : Fin (f a).market.rows,(state (B.purchaseOut+j.val)).val*v.openingCharge (state ((keys a).buy j)).val
  let idx:=Succession v.mesh (.attempt a)
  have physical : ((A).read idx.2 out).paid=((A).read idx.1 entry).paid+opening out :=
    posted.trans (congrArg (((A).read idx.1 entry).paid + ·) amount)
  have charged : ((A).read idx.2 (reserveState C mem phase trial 0)).paid =
      ((A).read idx.1 entry).paid+opening (reserveState C mem phase trial 0) :=
    outReserve ▸ physical
  have fee : opening (reserveState C mem phase trial 0)=purchaseFee C mem phase trial Λ p q Q (dyadicScale v.W) := by
    rw [reserve_zero]
    rfl
  exact charged.trans (congrArg (((A).read idx.1 entry).paid + ·) fee)

/-- The active frozen flags fit the compiled dyadic decision bank; both
branches of the original-date lookup give the ordinary physical unit length. -/
theorem purchase_format :
    (v.frozenMarket P z width phase trial).rows≤2^(f a).batch.decisionBits ∧
      (f a).batch.purchaseLink.lengthCode=.lit 1 := by
  constructor
  · let n:=count z (2^v.W) k*paths z v.sampler.degree v.depth
    change n≤ProtocolRAMPurchaseSampler.span n
    exact (ProtocolRAMPurchaseSampler.lt_span n).le
  · rfl

set_option maxHeartbeats 1600000 in
/-- All genuine native flags at a date occupy at most the original number
of payload rows, including the union over stages, signs, and groups. -/
theorem purchase_fee_bound (π : Equiv.Perm (Fin (2^z))) (romImage : Memory W)
    (archive : ArchiveRoom C mem (v.mesh.inject+v.mesh.cool)) (hp : phase<v.mesh.inject+v.mesh.cool)
    (ht : trial<v.mesh.outerFuel) :
    let sh:=v.frozenMarket P z width phase trial
    let frozen:=v.frozenInput P z width r banks src tab dst owners mem phase trial
    sh.shelf.Incoming (k:=k) sh.sampler π sh.depth sh.phase sh.temperature sh.kind frozen →
    (∀i : Key z (2^v.W) k,sh.shelf.Prepared sh.sampler sh.depth romImage i frozen) →
    purchaseCount C mem phase trial≤2^z ∧
      (purchaseCount C mem phase trial:ℝ)*(Λ*(dyadicScale v.W)^p)≤(2^z:ℕ)*(Λ*(dyadicScale v.W)^p) := by
  intro sh frozen incoming rom
  let marks:=Shelf.catalogueMarks (k:=k) (observedMode C mem phase trial) sh.shelf sh.phase sh.temperature sh.kind frozen
  have numeral:=priced_purchaseCount_all v.mesh v.finish (v.basePhase width) f
    (feedColumns («N»:=N) v.mesh arena f P.joint.initial width v.keepLimit)
    (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase
    (fun event=>(StripChart.header F (v.nativeBoards P z width) event).fieldTerm)
    (StripChart.id F (v.nativeBoards P z width) P.catalogue) mem phase trial (v.mesh.inject+v.mesh.cool)
    π romImage incoming rom archive hp ht (v.purchase_format P z width phase trial).1
  have exclusive : ∀t l l' i,i∈marks t l → i∈marks t l' → l=l' := by
    intro t l l' i one two
    by_cases bought : observedMode C mem phase trial=3
    · apply StripDirectory.actualMarks_unique sh.shelf sh.phase sh.temperature sh.kind frozen t l l' i
      · simpa only [marks,Shelf.catalogueMarks,ite_eq_left bought] using one
      · simpa only [marks,Shelf.catalogueMarks,ite_eq_left bought] using two
    · simp [marks,Shelf.catalogueMarks,bought] at one
  have small:purchaseCount C mem phase trial≤2^z:=numeral.trans_le
    (purchased_card_le sh.sampler π sh.depth marks exclusive (stages_le_purchased_tiles v.geometry v.positive z))
  exact ⟨small,v.acquisition_fee small⟩

set_option maxHeartbeats 1600000 in
include scheduled live data buy bounded in
/-- The charged candidate rows are exactly the native frozen decisions. This
is an equality of the two actual cash states on the acquired calendar. -/
theorem purchase_initial_cash (positive : 0<width) (π : Equiv.Perm (Fin (2^z))) (romImage : Memory W)
    (archive : ArchiveRoom C mem (v.mesh.inject+v.mesh.cool)) (hp : phase<v.mesh.inject+v.mesh.cool)
    (ht : trial<v.mesh.outerFuel) :
    let sh:=v.frozenMarket P z width phase trial
    let frozen:=v.frozenInput P z width r banks src tab dst owners mem phase trial
    sh.shelf.Incoming (k:=k) sh.sampler π sh.depth sh.phase sh.temperature sh.kind frozen →
    (∀i : Key z (2^v.W) k,sh.shelf.Prepared sh.sampler sh.depth romImage i frozen) →
    ((A).inner C mem phase trial 0 0).paid=((A).trial C mem phase trial).paid+
      (purchaseCount C mem phase trial:ℝ)*(Λ*(dyadicScale v.W)^p) := by
  intro sh frozen incoming rom
  obtain ⟨padding,literal⟩:=v.purchase_format P z width phase trial
  have cost:=priced_actual_fee v.mesh v.finish (v.basePhase width) f
    (feedColumns («N»:=N) v.mesh arena f P.joint.initial width v.keepLimit)
    (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase
    (fun event=>(StripChart.header F (v.nativeBoards P z width) event).fieldTerm)
    (StripChart.id F (v.nativeBoards P z width) P.catalogue) mem phase trial (v.mesh.inject+v.mesh.cool)
    v.W Λ p q Q π romImage incoming rom archive hp ht padding literal
  have count:=priced_purchaseCount_all v.mesh v.finish (v.basePhase width) f
    (feedColumns («N»:=N) v.mesh arena f P.joint.initial width v.keepLimit)
    (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase
    (fun event=>(StripChart.header F (v.nativeBoards P z width) event).fieldTerm)
    (StripChart.id F (v.nativeBoards P z width) P.catalogue) mem phase trial (v.mesh.inject+v.mesh.cool)
    π romImage incoming rom archive hp ht padding
  have billed := v.purchase_open_bill P z width r banks src tab dst owners mem fixture phase trial
    scheduled live data buy bounded positive
  have unitCost := congrArg (fun n : ℕ => (n : ℝ) * (Λ*(dyadicScale v.W)^p)) count.symm
  exact billed.trans (congrArg (fun fee : ℝ => ((A).trial C mem phase trial).paid + fee)
    (cost.trans unitCost))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
