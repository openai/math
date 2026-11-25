import OAI.Hierarchy.ProbeFixedAttemptSpill
import OAI.Hierarchy.ProbeFixedPurchaseEntry
import OAI.Hierarchy.ProbeFixedQuietInputs
import OAI.Hierarchy.ProbeFixedQuietAttemptStock

namespace OAI
/-! # Per-commodity conservation at an actual chronological attempt -/

set_option quotPrecheck false
set_option maxRecDepth 4096

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native StripChart
open StockCommit PurchaseStage RepairHistogram CoreBoard PurchaseFrozen
open ThreeFlat.RAM
open scoped BigOperators Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "st" => v.taskCommit P z width
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "input" => v.stage P z width r banks src tab dst owners
local notation "keys" => v.cashKeys P z width r banks src tab dst owners
variable (a : Attempt) (entry : Memory (wordBits z (2^v.W) copies))
local notation "layoutType" => StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
  ((v.privateArena P z width).base v.mesh (.attempt a))

variable (S : v.RepairSlot P z width r banks src tab dst owners a entry)

local notation "u" => input a entry
local notation "s" => st a
local notation "ar" => (f a).pricedArea
local notation "tag" => RepairHistogram.kind (goods:=(s).goods) (s).plan.bank (s).columns u
local notation "add" => installedBits (n:=(s).occurrences) (s).columns u
local notation "sub" => consumedBits (n:=(s).occurrences) (s).columns u

set_option maxHeartbeats 1000000 in
include S in
/-- The scatter, cap and excess write share the same signed histogram. -/
private theorem repair_balance (i : Fin (ar).goods)
    (funded : resourceBits tag sub i ≤ (u ((s).plan.bank.base+i.val)).val)
    (credit : resourceBits tag add i ≤ v.menu.maximum*v.menu.copiesAt v.copyScale width) :
    let out:=after C (.attempt a) entry
    (u ((s).plan.bank.base+i.val)).val+resourceBits tag add i =
      (out ((ar).output+i.val)).val+(out ((ar).output+(ar).goods+(ar).goods+i.val)).val+resourceBits tag sub i := by
  intro out
  let layout:=S.layout
  have run:=S.slot.currentReady
  have before:=(v.repair_stock P z width r banks src tab dst owners a entry S.event run layout).1 i
  have held : (u ((s).plan.bank.base+i.val)).val≤v.keepLimit*width:=
    before.symm.le.trans (S.held ((v.nativeSlots P z width a).symm i))
  have upper:=(Nat.add_le_add held credit).trans_lt S.rateRoom
  have mode:=(v.repair_words P z width r banks src tab dst owners a entry run layout.board
    layout.positive layout.window S.failed).1 i
  have room:=fresh_stockRoom ar (f a).stockSource (b a) layout.inputs width v.keepLimit layout.window.wide
    layout.window.room layout.window.budget (layout.window.budget.le.trans_lt layout.window.wordRoom)
  have ord:=(eventBoard ar (f a).stockSource (b a) layout.inputs layout.window.room).order
  have direct_le : (s).direct ≤ (s).broadcast :=
    (Nat.le_add_right (s).direct (s).occurrences).trans
      ((Nat.le_add_right ((s).direct + (s).occurrences) (s).occurrences).trans ord)
  obtain ⟨balance,kept,spill⟩:=(s).repair_receipt (b a) u i
    (v.entered P z width r banks src tab dst owners a entry run) direct_le room.address room.credit room.debit
    room.seed room.space room.wide width v.keepLimit room.limit room.room room.excess
    room.clipCap room.excessCap room.bankCap funded upper mode
  let raw:=v.repairRaw P z width r banks src tab dst owners a entry i
  change (u ((s).plan.bank.base+i.val)).val+resourceBits tag add i=raw+resourceBits tag sub i at balance
  change (out ((ar).output+i.val)).val=min raw (v.keepLimit*width) at kept
  change (out ((ar).output+(ar).goods+(ar).goods+i.val)).val=raw-min raw (v.keepLimit*width) at spill
  rw [kept,spill]
  have h:=Nat.min_le_left raw (v.keepLimit*width)
  omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native CoreBoard StripChart
open StockCommit PurchaseStage RepairHistogram CatalystArchive StripDirectory PurchaseFrozen CatalogueRows
open scoped BigOperators Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "bs" => v.nativeBoards P z width
local notation "f" => v.nativeFormats P z width
local notation "arena" => v.privateArena P z width

section
variable (phase trial : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.outer phase trial
variable (fitted : v.payloadStageSizes P z width r banks src tab dst owners phase trial entry)
variable (s : v.RepairSlot P z width r banks src tab dst owners (Attempt.outer phase trial) entry)

open private payload_failed_charges from OAI.Hierarchy.ProbeFixedSelectedRepair

attribute [local irreducible] permutationFabric
set_option cleanup.letToHave false
set_option maxHeartbeats 2500000 in
include fitted s in
omit [Nonempty (Fin k)] in
private theorem payload_funds (i : Fin (f ev).pricedArea.goods) :
    let t:=v.taskCommit P z width ev
    let u:=v.stage P z width r banks src tab dst owners ev entry
    let knd:=RepairHistogram.kind (n:=t.occurrences) (goods:=t.goods) t.plan.bank t.columns u
    resourceBits knd (consumedBits (n:=t.occurrences) t.columns u) i ≤ (u (t.plan.bank.base+i.val)).val ∧
      resourceBits knd (installedBits (n:=t.occurrences) t.columns u) i ≤ v.menu.maximum*v.menu.copiesAt v.copyScale width := by
  exact payload_failed_charges v P z width r banks src tab dst owners phase trial entry fitted s.layout
    (v.payload_spill_placed P z width r banks src tab dst owners phase trial entry fitted s) i
end

section
variable (phase trial slice inner : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.inner phase trial slice inner
variable (fitted : v.purchasedStageSizes P z width r banks src tab dst owners phase trial slice inner entry)
variable (s : v.RepairSlot P z width r banks src tab dst owners (Attempt.inner phase trial slice inner) entry)
local notation "sh" => ((bs).outer phase trial).market.shelf
local notation "S" => (bs).sampler
local notation "h₀" => stratumHeader z (2^v.W) k (S).degree v.depth ((bs).stratumHeader phase trial)


open private purchased_failed_charges from OAI.Hierarchy.ProbeFixedSelectedRepair
attribute [local irreducible] permutationFabric
set_option cleanup.letToHave false
set_option maxHeartbeats 2500000 in
include fitted s in
omit [Nonempty (Fin k)] in
private theorem bought_funds (perm : Equiv.Perm (Fin (2^z))) (headLow : (h₀).stop≤(arena).base v.mesh (.attempt ev))
    (born : PurchasedBirth sh S perm v.depth ((bs).stratumHeader phase trial) entry k) (i : Fin (f ev).pricedArea.goods) :
    let t:=v.taskCommit P z width ev
    let u:=v.stage P z width r banks src tab dst owners ev entry
    let knd:=RepairHistogram.kind (n:=t.occurrences) (goods:=t.goods) t.plan.bank t.columns u
    resourceBits knd (consumedBits (n:=t.occurrences) t.columns u) i ≤ (u (t.plan.bank.base+i.val)).val ∧
      resourceBits knd (installedBits (n:=t.occurrences) t.columns u) i ≤ v.menu.maximum*v.menu.copiesAt v.copyScale width := by
  intro t u knd
  have placed := v.purchased_spill_placed P z width r banks src tab dst owners phase trial slice inner
    entry fitted s perm headLow born
  exact purchased_failed_charges v P z width r banks src tab dst owners phase trial slice inner
    entry fitted s.layout placed i
end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe AdaptiveProbe.OuterBank
open StripChart StockCommit PurchaseCT PurchaseFrozen CatalystArchive PurchaseStage RepairHistogram
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  {v : FixedProtocolFormat F k p q Q σ Λ} {P : v.Placement} {z width r : ℕ}
  {banks : RouteSettlement.Banks} {src tab dst : ℕ} {owners : Bank}
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "G" => v.privateArena P z width
local notation "H" => v.publicHeader P z width
variable {π : Equiv.Perm (Fin (2^z))} {mem fixture : Memory (wordBits z (2^v.W) copies)}
  (D : v.ReadbackRun P z width r banks src tab dst owners π mem fixture)


private theorem attempt_inner_bounds (c : Mesh) (p h j b : ℕ) (incl : Event.attempt (.inner p h j b)∈events c) :
    p<c.inject+c.cool ∧ h<c.outerFuel ∧ j<c.reserveSteps ∧ b<c.innerFuel := by
  obtain ⟨u,hu,phase⟩:=List.mem_flatMap.mp incl
  rcases List.mem_append.mp phase with attempts|endPhase
  · obtain ⟨a,ha,trial⟩:=List.mem_flatMap.mp attempts
    rcases List.mem_cons.mp trial with outer|inside
    · cases outer
    · obtain ⟨v,hv,slice⟩:=List.mem_flatMap.mp inside
      rcases List.mem_append.mp slice with actions|endSlice
      · obtain ⟨t,ht,same⟩:=List.mem_map.mp actions
        cases same
        exact ⟨List.mem_range.mp hu,List.mem_range.mp ha,List.mem_range.mp hv,List.mem_range.mp ht⟩
      · simp at endSlice
  · simp at endPhase


local notation "f" => v.nativeFormats P z width
local notation "T" => v.taskCommit P z width
local notation "stage" => v.stage P z width r banks src tab dst owners
local notation "stamps" => v.stamp P z width r banks src tab dst owners
local notation "ballots" => v.ballot P z width r banks src tab dst owners
local notation "fees" => v.issued P z width r banks src tab dst owners

/-- The old and reserve input pointers are the actual preceding account banks. -/
theorem attempt_stock_banks (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
    (a : Attempt) :
    ((v.nativeFormats P z width a).stockSource.old.base=(v.stockBanks P z width).previous v.mesh (.attempt a)) ∧
    ((v.nativeFormats P z width a).stockSource.reserve.base=(v.stockBanks P z width).reserve (.attempt a)) :=
  StockBound.strip_pointers F (v.mounted (v.seed P z width) P width) v.mesh (v.privateArena P z width)
    P.joint.initial (v.emptyReserve P z width) a

set_option maxHeartbeats 1000000 in
include D in
/-- The mode used for the chronological branch is the actual retained mode cell. -/
theorem ReadbackRun.attempt_mode (a : Attempt) (prior tail : List Event) (entry : Memory (wordBits z (2^v.W) copies))
    (slot : Slot C mem (.attempt a) prior tail entry) :
    ((after C (.attempt a) entry) ((C).modeAt a)).val=
      AttemptGate.actual (repair C a).policy (postSnapshot ((C).layout a) (repair C a) (prepared C a entry)) := by
  have occurs : Event.attempt a∈events v.mesh := by change _∈events (C).mesh; rw [slot.events]; simp
  let layout:=(D.boards a occurs).1
  let B:=repair C a
  let L:=(C).layout a
  let i : Fin L.candidates:=⟨0,layout.positive⟩
  let test:=postSnapshot L B (prepared C a entry)
  let modePass : Pass := ⟨B.modeOut,L.candidates,AttemptGate.mode B.policy⟩
  have read : after C (.attempt a) entry (B.modeOut + i.val) =
      (AttemptGate.mode B.policy).eval test (i.val : Word W) :=
    attempt_read C a entry slot.currentReady layout.board modePass
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) i
  have code := read.trans (AttemptGate.mode_eval B.policy test (i.val : Word W))
  exact (congrArg Fin.val code).trans
    (Fin.val_cast_of_lt ((AttemptGate.actual_lt B.policy test).trans_le layout.window.wide))

set_option maxHeartbeats 4000000 in
include D in
/-- The balance mentions the predecessor and published words in the actual
chronological memories and both signed columns of the actual native stage. -/
private theorem ReadbackRun.attempt_conservation_funded (B : RepairWordBounds v P z width) (a : Attempt)
    (prior tail : List Event) (entry : Memory (wordBits z (2^v.W) copies)) (slot : Slot C mem (.attempt a) prior tail entry)
    (i : Fin (f a).pricedArea.goods) :
    let ar:=(f a).pricedArea
    let out:=after C (.attempt a) entry
    let mode:=AttemptGate.actual (repair C a).policy (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))
    let old:=(entry ((f a).stockSource.old.base+i.val)).val
    let active:=(out (ar.output+i.val)).val
    let saved:=(out (ar.output+ar.goods+i.val)).val
    let spill:=(out (ar.output+ar.goods+ar.goods+i.val)).val
    let t:=T a
    let u:=stage a entry
    let tag:=RepairHistogram.kind (n:=t.occurrences) (goods:=t.goods) t.plan.bank t.columns u
    let put:=resourceBits tag (installedBits (n:=t.occurrences) t.columns u) i
    let take:=resourceBits tag (consumedBits (n:=t.occurrences) t.columns u) i
    (mode=2 → old+put=active+spill+take ∧ take≤old) ∧
    (mode=3 → old=active+saved) ∧ (mode≠2 → mode≠3 → old=active) ∧ (mode≠2 → spill=0) := by
  classical
  let : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  intro ar out mode old active saved spill t u tag put take
  have occurs : Event.attempt a∈events v.mesh := by change _∈events (C).mesh; rw [slot.events]; simp
  let data:=v.slot_inputs P z width r banks src tab dst owners mem fixture D.boards a prior tail entry slot
  let layout:=data.toTrialLayout
  let E:=v.nativeSlots P z width a
  let good:=E.symm i
  have idx : PurchaseInventory.slot good=i.val :=
    (v.slot_index P z width a good).symm.trans (congrArg Fin.val (E.apply_symm_apply i))
  have prev : ((A).read (Succession v.mesh (.attempt a)).1 entry).bits good=old := by
    rw [show (Succession v.mesh (.attempt a)).1=a by cases a <;> rfl]
    change (entry ((A).stockAt a good)).val=old
    exact congrArg (fun address : ℕ => (entry address).val)
      ((v.stock_pointer P z width fees a good).trans
        (congrArg ((f a).stockSource.old.base + ·) idx))
  refine ⟨?_,?_,?_,?_⟩
  · intro fail
    let signed:=RepairSlot.ofWords v P z width r banks src tab dst owners mem D.nativeStock D.valid
      D.resident D.prices D.charges D.digitBudget B.late B.threshold B.alphabet B.rate D.widths
      a prior tail entry slot layout fail
    have cover : take ≤ (u (t.plan.bank.base+i.val)).val ∧
        put ≤ v.menu.maximum*v.menu.copiesAt v.copyScale width := by
      cases a with
      | outer phase trial =>
        let fit:=v.payload_fit_at_slot P z width r banks src tab dst owners phase trial entry signed D.payload
        exact payload_funds v P z width r banks src tab dst owners phase trial entry fit signed i
      | inner phase trial slice inner =>
        obtain ⟨hp,hh,hj,hb⟩:=attempt_inner_bounds v.mesh phase trial slice inner occurs
        obtain ⟨_,other⟩:=inner_slot C mem phase trial slice inner hp hh hj hb D.nativeStock.mounted_all
        have same : innerState C mem phase trial slice inner=entry:=other.entryMemory.symm.trans slot.entryMemory
        have born:=D.purchased ⟨phase,hp⟩ ⟨trial,hh⟩ ⟨slice,hj⟩ ⟨inner,hb⟩
        rw [same] at born
        let fit:=v.purchased_fit_at_slot P z width r banks src tab dst owners phase trial slice inner entry signed D.payload
        have low:=((D.keys phase trial).1).trans
          (show (G).first≤(G).base v.mesh (.attempt (.inner phase trial slice inner)) from Nat.le_add_right ..)
        exact bought_funds v P z width r banks src tab dst owners phase trial slice inner entry fit signed π low born i
    have before:=(v.repair_stock P z width r banks src tab dst owners a entry occurs slot.currentReady layout).1 i
    change ((A).read (Succession v.mesh (.attempt a)).1 entry).bits good=(u (t.plan.bank.base+i.val)).val at before
    have oldAt : old = (u (t.plan.bank.base+i.val)).val := prev.symm.trans before
    have balance := repair_balance v P z width r banks src tab dst owners a entry signed i cover.1 cover.2
    exact ⟨(congrArg (· + put) oldAt).trans balance, cover.1.trans oldAt.ge⟩
  · intro buy
    let s:=(f a).stockSource
    let term:=postOutput ((C).layout a) (repair C a) (prepared C a entry)
    let cut:=(G).base v.mesh (.attempt a)
    let window:=data.window
    obtain ⟨ports⟩:=data.ports
    have live:=slot.currentReady
    have typed : (pricedSegment ar s (stamps a) W (ballots a)).ready term:=live.2.2.2.2.2.2.2.2.2.2.1
    have pre (x : ℕ) (h : x<cut) : term x=entry x:=
      postOutput_prior C a entry x live ((v.event_prefix P z width r banks src tab dst owners (.attempt a) x h).1)
    have before : (term (s.old.base+i.val)).val=old:=
      congrArg Fin.val (pre _ ((Nat.add_lt_add_left i.isLt _).trans_le data.oldLow))
    have pointer:=(StockBound.strip_pointers F (v.mounted (v.seed P z width) P width) v.mesh G P.joint.initial
      (v.emptyReserve P z width) a).1
    change (f a).market.shelf.stockBase=(v.stockBanks P z width).previous v.mesh (.attempt a) at pointer
    have held : old≤v.keepLimit*width:=by
      change (entry ((f a).market.shelf.stockBase+i.val)).val≤_
      rw [pointer,←idx]
      exact (D.nativeStock.slot slot).1 good
    have off : mode≠2:=by omega
    have masked (j : Fin (T a).occurrences) : delta (T a).columns (stage a entry) j=0:=by
      have disabled:=v.rows_off_of_ne P z width r banks src tab dst owners a entry live layout
        (show mode≠2 from off) (ports.enum.symm j).1
      obtain ⟨add,sub⟩:=ports.off j (by simpa only [StockCommit.liveRows, Finset.mem_filter, Finset.mem_univ, true_and,
        FixedProtocolFormat.ballot, FixedProtocolFormat.stage] using disabled)
      have plus : (T a).columns.credit.eval (stage a entry) (j.val:Word W)=0:=Fin.ext add
      have minus : (T a).columns.charge.eval (stage a entry) (j.val:Word W)=0:=Fin.ext sub
      simp [delta,plus,minus]
    let j : Fin ((C).layout a).candidates:=⟨0,data.positive⟩
    let ballot := repair C a
    let checked := postSnapshot ((C).layout a) ballot (prepared C a entry)
    let modePass : Pass := ⟨ballot.modeOut,((C).layout a).candidates,AttemptGate.mode ballot.policy⟩
    have printer : term (ballot.modeOut + j.val) =
        (AttemptGate.mode ballot.policy).eval checked (j.val : Word W) :=
      post_read ((C).layout a) ballot (prepared C a entry) live.2.2.2.2.2.2.1 data.board modePass
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) j
    have printed : term ((C).modeAt a) = (mode : Word W) :=
      printer.trans (AttemptGate.mode_eval ballot.policy checked (j.val : Word W))
    have signal : (term ((C).modeAt a)).val=3 := by
      rw [buy] at printed
      exact (congrArg Fin.val printed).trans (Fin.val_cast_of_lt (by have := window.wide; omega : 3 < 2^W))
    have facts:=calibrated_buy ar s (stamps a) (ballots a) term fixture i data.inputs window.room window.capacity.1 window.old
      window.label window.table (by rw [before];exact held.trans_lt window.halfRoom)
      (fun x lo hi=>(pre x (hi.trans_le data.halfLow)).trans (data.half x lo hi)) ((C).modeAt a)
      window.mode window.modeBefore signal masked
    obtain ⟨act,save,_⟩:=priced_buy ar s (stamps a) (ballots a) term i typed data.inputs window.room window.wide
      window.capacity.1 window.old facts.idle facts.bought facts.half
    have published : (pricedSegment ar s (stamps a) W (ballots a)).after term = out :=
      (priced_after ar s (stamps a) (ballots a) term).trans
        (v.native_end P z width r banks src tab dst owners a entry)
    rw [published] at act save
    change active=(term (s.old.base+i.val)).val/2 at act
    change saved=(term (s.old.base+i.val)).val-(term (s.old.base+i.val)).val/2 at save
    rw [before] at act save
    omega
  · intro off nobuy
    have range:=AttemptGate.actual_lt (repair C a).policy (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))
    change mode<4 at range
    obtain ⟨ports⟩:=data.ports
    have quietMode : mode < 2 := by omega
    have quiet:=v.quiet_words P z width r banks src tab dst owners a entry slot.currentReady layout ports quietMode i
    exact (congrArg Fin.val quiet.1).symm
  · intro off
    have empty:=v.nonrepair_spill P z width r banks src tab dst owners a entry slot.currentReady layout off i
    simpa only [Fin.val_zero] using congrArg Fin.val empty

include D in
theorem ReadbackRun.attempt_conservation (B : RepairWordBounds v P z width) (a : Attempt)
    (prior tail : List Event) (entry : Memory (wordBits z (2^v.W) copies)) (slot : Slot C mem (.attempt a) prior tail entry)
    (i : Fin (f a).pricedArea.goods) :
    let ar:=(f a).pricedArea
    let out:=after C (.attempt a) entry
    let mode:=AttemptGate.actual (repair C a).policy (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))
    let old:=(entry ((f a).stockSource.old.base+i.val)).val
    let active:=(out (ar.output+i.val)).val
    let saved:=(out (ar.output+ar.goods+i.val)).val
    let spill:=(out (ar.output+ar.goods+ar.goods+i.val)).val
    let t:=T a
    let u:=stage a entry
    let tag:=RepairHistogram.kind (n:=t.occurrences) (goods:=t.goods) t.plan.bank t.columns u
    let put:=resourceBits tag (installedBits (n:=t.occurrences) t.columns u) i
    let take:=resourceBits tag (consumedBits (n:=t.occurrences) t.columns u) i
    (mode=2 → old+put=active+spill+take) ∧
    (mode=3 → old=active+saved) ∧ (mode≠2 → mode≠3 → old=active) ∧ (mode≠2 → spill=0) := by
  have h := D.attempt_conservation_funded B a prior tail entry slot i
  exact ⟨fun repair => (h.1 repair).1,h.2⟩

set_option maxHeartbeats 1200000 in
include D in
/-- Every signed debit is funded by this commodity's predecessor stock. On
a nonrepair event each occurrence in the native debit column is zero. -/
theorem ReadbackRun.repair_pre_stock (B : RepairWordBounds v P z width) (a : Attempt)
    (prior tail : List Event) (entry : Memory (wordBits z (2^v.W) copies)) (cut : Slot C mem (.attempt a) prior tail entry)
    (i : Fin (f a).pricedArea.goods) :
    let t := T a
    let u := stage a entry
    let tag := RepairHistogram.kind (n:=t.occurrences) (goods:=t.goods) t.plan.bank t.columns u
    resourceBits tag (consumedBits (n:=t.occurrences) t.columns u) i ≤
      (entry ((f a).stockSource.old.base+i.val)).val := by
  classical
  intro t u tag
  by_cases failed : AttemptGate.actual (repair C a).policy
      (postSnapshot ((C).layout a) (repair C a) (prepared C a entry)) = 2
  · exact ((D.attempt_conservation_funded B a prior tail entry cut i).1 failed).2
  · let data := v.slot_inputs P z width r banks src tab dst owners mem fixture D.boards a prior tail entry cut
    obtain ⟨ports⟩ := data.ports
    have zero (j : Fin t.occurrences) : consumedBits t.columns u j = 0 := by
      have absent := v.rows_off_of_ne P z width r banks src tab dst owners a entry cut.currentReady
        data.toTrialLayout failed (ports.enum.symm j).1
      exact (ports.off j (by
        simpa only [StockCommit.liveRows, Finset.mem_filter, Finset.mem_univ, true_and,
          FixedProtocolFormat.ballot, FixedProtocolFormat.stage] using absent)).2
    have take : resourceBits tag (consumedBits (n:=t.occurrences) t.columns u) i = 0 := by
      unfold resourceBits
      apply Finset.sum_eq_zero
      intro j _
      simp [zero j]
    rw [take]
    exact Nat.zero_le _

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
