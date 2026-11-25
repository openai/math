import OAI.Hierarchy.ProbeFixedReceipts
import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProtocolRAMCalendarLiveFee
import OAI.Hierarchy.ProtocolRAMCalendarRemainders

namespace OAI
/-! # The active capacity bill of the fixed native calendar -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory ReportSockets PurchaseStage PurchaseFrozen
open ThreeFlat.RAM
open scoped BigOperators Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dest : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "fmt" => v.nativeFormats P z width
local notation "C" => v.nativeChart P z width r banks src tab dest owners
local notation "sink" => P.catalogue.sink r banks src tab dest owners
local notation "rec" => v.receipts P z width r banks src tab dest owners

def frozenMarket (u h : ℕ) := (fmt (.outer u h)).atTime v.mesh v.finish (v.basePhase width) (.outer u h)

def frozenInput (m : Memory W) (u h : ℕ) :=
  let a:=Attempt.outer u h
  (v.frozenMarket P z width u h).failures.pass.apply ((guard C a).apply (trialState C m u h))

/-- Each flat date reads the actual outer gate mode and frozen marks, at that
date's own prior stock. Dormant dates add no capacity fee. -/
def birthMarks (m : Memory W) : Marks z v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel) :=
  fun i=>
    let ⟨u,h⟩:= (outerDates v.mesh) i
    let sh:=v.frozenMarket P z width u h
    Shelf.catalogueMarks (observedMode C m u h) sh.shelf sh.phase sh.temperature sh.kind
      (v.frozenInput P z width r banks src tab dest owners m u h)

theorem attempt_word (init state : Memory W) (a : Attempt) (early later : List Event)
    (cut : Slot C init (.attempt a) early later state) (x : ℕ) (below : x<(fmt a).pricedArea.stop) :
    run C (events (C).mesh) init x=after C (.attempt a) state x := by
  apply cut.word
  intro e tail
  exact (v.event_prefix P z width r banks src tab dest owners e x
    (below.trans_le ((v.attempt_room P z width a).trans
      ((v.privateArena P z width).apart v.mesh (cut.later e tail))))).1

theorem inner_not_opened (m : Memory W) (u h j b : ℕ)
    (inside : Event.attempt (.inner u h j b)∈events v.mesh)
    (mountedAll : Calendar.mounted C (events (C).mesh) m) (archive : ArchiveRoom C m (v.mesh.inject+v.mesh.cool))
    (i : Fin (fmt (.inner u h j b)).pricedArea.rows) :
    (run C (events (C).mesh) m ((repair C (.inner u h j b)).purchaseOut+i.val)).val=0 := by
  have range : u<v.mesh.inject+v.mesh.cool ∧ h<v.mesh.outerFuel ∧ j<v.mesh.reserveSteps ∧ b<v.mesh.innerFuel := by
    simp only [events,outerBlock,trialBlock,reserveBlock,List.mem_flatMap,List.mem_map,List.mem_range,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at inside
    aesop
  let a := Attempt.inner u h j b
  let L:=(C).layout a
  let B:=repair C a
  let now:=innerState C m u h j b
  obtain ⟨rest,cut⟩:=inner_slot C m u h j b range.1 range.2.1 range.2.2.1 range.2.2.2 mountedAll
  obtain ⟨_,_,board,_⟩:=archive.innerHead u range.1 h range.2.1 j range.2.2.1 b range.2.2.2
  let pass : Pass := ⟨B.purchaseOut,L.candidates,buyWord L B⟩
  have included : pass∈writes L B := List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have address : B.purchaseOut+i.val<(fmt a).pricedArea.stop :=
    (Nat.add_lt_add_left i.isLt _).trans_le (fmt a).chargeColumns.2.2.1
  rw [v.attempt_word P z width r banks src tab dest owners m now a _ rest cut _ address]
  have flag:=attempt_read C a now cut.currentReady board pass included i
  have never:=AttemptGate.reserve_no_purchase B.policy (postSnapshot L B (prepared C a now)) (by rfl)
  change after C (.attempt a) now (B.purchaseOut+i.val)=(buyWord L B).eval _ (i.val:Word W) at flag
  rw [flag]
  simp [buyWord,AttemptGate.ifPurchase,AttemptGate.ifMode_eval _ 3 _ _ _ _ archive.wide (by decide),Expr.eval]
  intro mode
  exact (never mode).elim

theorem archived_opening (m : Memory W) (u : Fin (v.mesh.inject+v.mesh.cool)) (h : Fin v.mesh.outerFuel)
    (runReady : Calendar.mounted C (events (C).mesh) m) :
    let final:=run C (events (C).mesh) m
    (rec final (.attempt (.outer u.val h.val))).opening=
      purchaseFee C m u h Λ p q Q (dyadicScale v.W) := by
  intro final
  let a:=Attempt.outer u.val h.val
  let B:=repair C a
  let now:=trialState C m u h
  obtain ⟨rest,cut⟩:=outer_slot C m u h u.isLt h.isLt runReady
  change (∑i : Fin (fmt a).pricedArea.rows,((final (B.purchaseOut+i.val)).val:ℝ)*
    v.openingCharge (final (B.boughtFields 5+i.val)).val)=_
  unfold purchaseFee
  apply Finset.sum_congr rfl
  intro i _
  have room:=(fmt a).chargeColumns
  have flagBound : B.purchaseOut+i.val<(fmt a).pricedArea.stop :=
    (Nat.add_lt_add_left i.isLt _).trans_le room.2.2.1
  have keyBound : B.boughtFields 5+i.val<(fmt a).pricedArea.stop :=
    (Nat.add_lt_add_left i.isLt _).trans_le room.2.2.2.1
  rw [show final (B.purchaseOut+i.val)=after C (.attempt a) now _ from
      v.attempt_word P z width r banks src tab dest owners m now a _ rest cut _ flagBound,
    show final (B.boughtFields 5+i.val)=after C (.attempt a) now _ from
      v.attempt_word P z width r banks src tab dest owners m now a _ rest cut _ keyBound]
  rfl

/-- One constant-capacity opening per genuine frozen accepted chain at this
particular date, under the original ROM and calendar admission checks. -/
theorem born_capacity (m : Memory W) (π : Equiv.Perm (Fin (2^z))) (u : Fin (v.mesh.inject+v.mesh.cool))
    (h : Fin v.mesh.outerFuel) (fixture : Memory W) :
    let a:=Attempt.outer u.val h.val
    let sh:=v.frozenMarket P z width u h
    let frozen:=v.frozenInput P z width r banks src tab dest owners m u h
    let all:=v.birthMarks P z width r banks src tab dest owners m
    sh.shelf.Incoming (k:=k) sh.sampler π sh.depth sh.phase sh.temperature sh.kind frozen →
    (∀i : Key z (2^v.W) k,sh.shelf.Prepared sh.sampler sh.depth fixture i frozen) →
    ArchiveRoom C m (v.mesh.inject+v.mesh.cool) → Calendar.mounted C (events (C).mesh) m →
    sh.rows≤2^(fmt a).batch.decisionBits → (fmt a).batch.purchaseLink.lengthCode=.lit 1 →
    (rec (run C (events (C).mesh) m) (.attempt a)).opening=
      (Fintype.card (LiveChains v.sampler π v.depth (all (finProdFinEquiv (u,h)))):ℝ)*(Λ*(dyadicScale v.W)^p) := by
  intro a sh frozen all incoming rom archive ready padded unit
  rw [v.archived_opening P z width r banks src tab dest owners m u h ready]
  have result := priced_actual_fee v.mesh v.finish (v.basePhase width) fmt
    (feedColumns («N»:=N) v.mesh (v.privateArena P z width) fmt P.joint.initial width v.keepLimit)
    sink P.catalogue.idBase (fun a=>(StripChart.header F (v.nativeBoards P z width) a).fieldTerm)
    (StripChart.id F (v.nativeBoards P z width) P.catalogue) m u h (v.mesh.inject+v.mesh.cool) v.W
    Λ p q Q π fixture incoming rom archive u.isLt h.isLt padded unit
  let marks := Shelf.catalogueMarks (k:=k) (observedMode C m u h)
    sh.shelf sh.phase sh.temperature sh.kind frozen
  have recorded : all (finProdFinEquiv (u,h)) = marks := by
    simp only [all,birthMarks,outerDates,Equiv.symm_apply_apply]; rfl
  change purchaseFee C m u h Λ p q Q (dyadicScale v.W) =
    (Fintype.card (LiveChains sh.sampler π sh.depth marks) : ℝ) * (Λ*(dyadicScale v.W)^p) at result
  have sampler : sh.sampler = v.sampler := rfl
  have depth : sh.depth = v.depth := rfl
  rw [sampler,depth] at result
  rw [recorded]
  exact result

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
