import OAI.Hierarchy.ProbeFixedNativeStockRun
import OAI.Hierarchy.ProtocolRAMCalendarLifetimes
import OAI.Hierarchy.ProtocolRAMCalendarTailPositions
import OAI.Hierarchy.ProtocolRAMPurchaseMarketBelow

namespace OAI
/-! # Lifetimes of the native mode words during every replay and phase -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart PurchaseStage
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners

/-- The frozen market ends at the guard cell. All four writable gates of
the following test pass occur strictly after that guard. -/
theorem mode_stop_room (a : Attempt) (entry : Memory W) (run : ready C (.attempt a) entry) :
    stopRoom C a := by
  let s:=f a
  let market:=s.atTime v.mesh v.finish (v.basePhase width) a
  have source : market.failures.base+market.failures.rows ≤ market.shelf.firstBase := run.2.1.2.1
  have flags := market.shelf.first_le_flags market.sampler z (2^v.W) k market.depth
  refine ⟨Or.inr ?_,?_,?_,?_,?_⟩
  · change max (market.failures.base+market.failures.rows) (market.flags+market.rows) ≤ market.flags+market.rows
    exact max_le ((source.trans flags).trans (Nat.le_add_right ..)) le_rfl
  · change s.testsStart<s.testsStart+1
    omega
  · change s.testsStart<s.testsStart+1+_+1
    omega
  · change s.testsStart<s.testsStart+1+_+1+_+1
    omega
  · change s.testsStart<s.testsStart+1+(_+1)+(_+1)+(_+1)
    omega

theorem mode_lifetimes_of_boards (mem : Memory W) (whole : Calendar.mounted C (events v.mesh) mem)
    (head : ∀a,Event.attempt a∈events v.mesh→
      PurchaseStage.Board ((C).layout a) (repair C a) W ∧ 0<((C).layout a).candidates) : ModeLifetimes C := by
  have formed (a : Attempt) {pre rest : List Event} {state : Memory W}
      (dated : Slot C mem (.attempt a) pre rest state) :
      stopRoom C a ∧ PurchaseStage.Board ((C).layout a) (repair C a) W ∧ 0<((C).layout a).candidates := by
    have here : Event.attempt a∈events v.mesh := by
      change Event.attempt a∈events (C).mesh
      rw [dated.events]
      simp
    exact ⟨v.mode_stop_room P z width r banks src tab dst owners a state dated.currentReady,head a here⟩
  have older (a : Attempt) (e : Event) (earlier : position v.mesh (.attempt a)<position v.mesh e) :
      protected C ((C).modeAt a) e := by
    have wall : (C).modeAt a<(G).base v.mesh (.attempt a)+(G).stride := v.stock_mode_room P z width a
    exact (v.event_prefix P z width r banks src tab dst owners e _
      (wall.trans_le ((G).apart v.mesh earlier))).1
  refine ⟨?_,v.clock.outer_pos,v.clock.inner_pos,?_,?_,?_,?_,?_,?_,?_⟩
  · exact Nat.le_trans (by decide : 4≤2^2) (Nat.pow_le_pow_right (by decide) (by unfold wordBits;omega))
  · intro u hu a ha
    obtain ⟨_,s⟩:=outer_slot C mem u a hu ha whole
    exact formed _ s
  · intro u hu a ha j hj b hb
    obtain ⟨_,s⟩:=inner_slot C mem u a j b hu ha hj hb whole
    exact formed _ s
  · intro u _ a n _ e he
    exact older _ _ (trialTail_after v.mesh u a n e he)
  · intro u n _ b _ h e he
    exact older _ _ (phaseTail_after v.mesh u h n b (Nat.sub_lt v.clock.outer_pos (by decide)) e he)
  · intro u _ a _ j _ b _ e he
    exact older _ _ (purchaseTail_after v.mesh u a j b e he)
  · intro u _ a _ j _ b n _ e he
    exact older _ _ (innerTail_after v.mesh u a j b n e he)
  · intro u _ a _ j n _ b _ h e he
    exact older _ _ (reserveTail_after v.mesh u a j h n b (Nat.sub_lt v.clock.inner_pos (by decide)) e he)

/-- Only the tested native board and mounting are needed. Candidate positivity
comes from the real stage, axis, and printable path counts. -/
theorem mode_lifetimes_of_post (mem : Memory W) (whole : Calendar.mounted C (events v.mesh) mem)
    (post : ∀a,Event.attempt a∈events v.mesh→ PurchaseStage.Board ((C).layout a) (repair C a) W) :
    ModeLifetimes C := by
  apply v.mode_lifetimes_of_boards P z width r banks src tab dst owners mem whole
  intro a ha
  refine ⟨post a ha,?_⟩
  have count : (f a).market.rows=PurchaseFrozen.count z (2^v.W) k*PurchaseFrozen.paths z v.sampler.degree v.depth :=
    candidate_count F v.mesh G P.joint.initial (v.nativeBoards P z width) a
  change 0<(f a).market.rows
  rw [count,PurchaseFrozen.count_eq]
  have axis := v.positive
  have degree := v.sampler_live
  unfold PurchaseFrozen.paths
  positivity

/-- The same authentic per-attempt stock layouts that check the native run
also give every board in the historical mode archive. -/
theorem mode_lifetimes (mem : Memory W)
    (stock : StockBound.Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width))
    (trial : ∀a, Event.attempt a∈events v.mesh →
      StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (v.stamp P z width r banks src tab dst owners a)
        v.keepLimit width ((G).base v.mesh (.attempt a))) : ModeLifetimes C :=
  v.mode_lifetimes_of_boards P z width r banks src tab dst owners mem stock.mounted_all
    (fun a dated=>⟨(trial a dated).board,(trial a dated).positive⟩)

theorem mode_archive (mem : Memory W)
    (stock : StockBound.Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width))
    (trial : ∀a, Event.attempt a∈events v.mesh →
      StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (v.stamp P z width r banks src tab dst owners a)
        v.keepLimit width ((G).base v.mesh (.attempt a))) :
    ArchiveRoom C mem (v.mesh.inject+v.mesh.cool) :=
  (v.mode_lifetimes P z width r banks src tab dst owners mem stock trial).archive stock.mounted_all

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
