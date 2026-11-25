import OAI.Hierarchy.ProtocolRAMCalendarTestsReady
import OAI.Hierarchy.ProtocolRAMCatalystPostExtent
import OAI.Hierarchy.ProbeFixedCatalystMask
import OAI.Hierarchy.ProbeFixedGlobalWordRoom
import OAI.Hierarchy.ProbeFixedDiscrepancyScan
import OAI.Hierarchy.ProbeFixedDatedMarket

namespace OAI
/-! # The dated stock and failure tests of the actual installed ballot -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory
open PurchaseCT PurchaseStage AttemptGate
open scoped Classical BigOperators Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width : ℕ) (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "G" => v.privateArena P z width
local notation "fs" => v.nativeFormats P z width
local notation "bills" => v.issued P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "L" => JointHeader.scores P.joint z N k
variable (a : Attempt)
local notation "f" => fs a
local notation "B" => repair C a
local notation "mk" => (f).atTime v.mesh v.finish (v.basePhase width) a
local notation "spot" => (G).base v.mesh (.attempt a)
local notation "old" => (f).stockSource.old
local notation "pg" => DeadlineROM.scorePage v.mesh L z N k a
local notation "s" => deadline v.mesh v.finish (v.basePhase width) a
local notation "margin" => envelope v.W ((dyadicScale v.W)^8) (time v.mesh v.finish a)

theorem dated_threshold_checks :
    (B).tests.excess=GlobalTests.check pg z N k false (B).tests.excess.out (GlobalTests.bound pg z margin) old ∧
    (B).tests.payload=GlobalTests.check pg z N k true (B).tests.payload.out (GlobalTests.bound pg z 1) old := by
  cases a <;> exact ⟨rfl,rfl⟩

set_option cleanup.letToHave false in
set_option maxHeartbeats 2000000 in
/-- The complete native three-pass readiness criterion. The receipt belongs
to the already executed market prefix, while the amount and sum are read from
the guarded entry tape. No post-stage readiness is used. -/
theorem dated_tests_with_discrepancy (entry : Memory W) (scheduled : Event.attempt a∈events v.mesh)
    (room : (G).endAddress v.mesh<2^W) (precision : P.joint.precision=v.precision)
    (height : v.voteHeight≤z) (discHeight : v.discrepancyScanHeight≤z)
    (localCut : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W) (stride : (L).stride≤2^z)
    (frozen : ((C).frozen a).ready ((guard C a).apply entry))
    (scores : GlobalTests.Resident pg z N k s ((guard C a).apply entry))
    (limits : ∀ t, (entry ((A).stockAt a t)).val<(L).stride)
    (sumDisc : (∑i,(f).market.failures.value ((guard C a).apply entry) i)<2^W) :
    TestsReady B (prepared C a entry) := by
  let m := (guard C a).apply entry
  have ft : (mk).ready m := frozen
  have before : spot≤ (mk).failures.base ∧ spot≤ (mk).shelf.firstBase ∧ spot≤(f).testsStart :=
    v.stock_order P z width a
  have atEnd := (G).within v.mesh (.attempt a) scheduled
  have spotFit : spot<2^W := ((Nat.le_add_right ..).trans atEnd).trans_lt room
  have fit := v.attempt_room P z width a
  have post := (f).post_ends
  have area : (f).pricedArea.start+(f).pricedArea.pad+(f).pricedArea.rows≤(f).pricedArea.stop := by
    unfold Area.stop Area.output Area.excess Area.clip Area.src Area.broadcast Area.direct
    omega
  change (f).board.verdict+1+(f).occurrences+(f).pricedArea.pad+(f).market.rows≤(f).pricedArea.stop at area
  have vroom : (f).board.verdict<2^W :=
    (show (f).board.verdict≤(f).pricedArea.stop by omega).trans_lt ((fit.trans atEnd).trans_lt room)
  have excessEnd : (B).tests.excess.out+((B).tests.excess.rows+1)<2^W := post.1.trans_lt vroom
  have payloadEnd : (B).tests.payload.out+((B).tests.payload.rows+1)<2^W := post.2.1.trans_lt vroom
  have discEnd : (B).tests.discrepancy.out+((B).tests.discrepancy.rows+1)<2^W := post.2.2.1.trans_lt vroom
  have core := v.catalystMaskBounds P z width r banks src tab dst owners a localCut
  have prior := core.prior
  have fcut : (mk).failures.base≤(B).tests.excess.out ∧ (mk).failures.base≤(B).tests.payload.out ∧
      (mk).failures.base≤(B).tests.discrepancy.out :=
    ⟨(Nat.le_add_right ..).trans prior.1,(Nat.le_add_right ..).trans prior.2.1,(Nat.le_add_right ..).trans prior.2.2⟩
  have checks := v.dated_threshold_checks P z width r banks src tab dst owners a
  have tbl := (v.election_public P z width a).2.1
  have padded : GlobalTests.rows z N k≤(old).size := by
    rw [v.stock_old_size P z width a]
    exact (ProtocolRAMPurchaseSampler.lt_span _).le
  have rawEnd : (old).base+(old).size ≤ spot := by
    rw [v.stock_old_size P z width a]
    exact v.stock_padded_old P z width a
  have rowRoom : GlobalTests.rows z N k<2^W :=
    ((padded.trans (Nat.le_add_left ..)).trans rawEnd).trans_lt spotFit
  have both (pay : Bool) (out cutoff : ℕ) :
      (GlobalTests.check pg z N k pay out cutoff old).term.Fits W (mk).failures.base :=
    ProtocolRAMGeneratedWrite.fits_mono _ before.1
      (GlobalTests.score_before pg z N k out cutoff pay old spot spotFit tbl rawEnd)
  have amounts (i : Fin (GlobalTests.rows z N k)) : (m ((old).base+i.val)).val<(pg).stride := by
    let e := PurchaseInventory.slotEquiv z N k
    let t := e.symm i
    have ptr : PurchaseInventory.slot t=i.val := congrArg Fin.val (e.apply_symm_apply i)
    change (((guard C a).apply entry) ((old).base + i.val)).val < (pg).stride
    rw [←ptr,v.guard_quote_stock P z width bills r banks src tab dst owners a entry t]
    exact limits t
  have deadlinePos := v.date_time_positive a (dateInTable_of_event v.mesh a scheduled)
  have global (pay : Bool) (out cutoff : ℕ) :=
    v.vote_sum_size P z width a precision height pay out cutoff old m scores rowRoom stride padded amounts deadlinePos
  have bounds := v.vote_cutoff (time v.mesh v.finish a)
  have fitL : CheckLayout (B).tests.excess W (mk).failures.base := by
    refine ⟨?_,fcut.1,excessEnd,?_⟩
    · exact (congrArg (fun check : Check=>check.term.Fits W (mk).failures.base) checks.1).mpr (both false _ _)
    · exact (congrArg (fun check : Check=>check.bound<2^W) checks.1).mpr
        (v.vote_bound_size P z a precision height bounds.2)
  have fitR : CheckLayout (B).tests.payload W (mk).failures.base := by
    refine ⟨?_,fcut.2.1,payloadEnd,?_⟩
    · exact (congrArg (fun check : Check=>check.term.Fits W (mk).failures.base) checks.2).mpr (both true _ _)
    · exact (congrArg (fun check : Check=>check.bound<2^W) checks.2).mpr
        (v.vote_bound_size P z a precision height bounds.1)
  have fitD : CheckLayout (B).tests.discrepancy W (mk).failures.base :=
    ⟨ft.1.1.2.1,fcut.2.2,discEnd,v.discrepancy_scan_threshold P z width discHeight a⟩
  apply (mk).native_tests_ready B m ft fitL fitR fitD
  · exact (congrArg (fun check : Check=>(∑i,check.score m i)<2^W) checks.1).mpr (global false _ _)
  · exact (congrArg (fun check : Check=>(∑i,check.score m i)<2^W) checks.2).mpr (global true _ _)
  · exact sumDisc

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
