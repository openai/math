import OAI.Hierarchy.ProbeFixedWideSettlement
import OAI.Hierarchy.ProbeFixedSpillCongestion
import OAI.Hierarchy.ProtocolRAMCoreRoutePaid

namespace OAI
/-! # Reading original route recipes and core ports at financial settlement -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalogueRows CatalystArchive StripChart PurchaseCT
open scoped Classical Fin.CommRing

private theorem installed_frame {z W k w : ℕ} (p : Recipes) (o : Orders z (2^W) k)
    (ci : Commodity (Fin (2^z)) (Stages z (2^W)) k → ℕ) (cj : Columns z (2^W)×Fin k → ℕ)
    (m out : Memory w) (stop : ℕ) (was : Installed p o ci cj m)
    (kEnd : p.kind.base+p.kind.size ≤ stop) (mEnd : p.mode.base+p.mode.size ≤ stop)
    (oEnd : p.operand.base+p.operand.size ≤ stop) (frame : ∀i<stop,out i=m i) :
    Installed p o ci cj out := by
  have read (b : Bank) (h : b.base+b.size ≤ stop) (x : Word w) : b.read out x=b.read m x := by
    apply frame
    exact (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le h
  intro i
  simpa only [read p.kind kEnd,read p.mode mEnd,read p.operand oEnd] using was i

namespace FixedProtocolFormat
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ) (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
local notation "r" => Fintype.card (Slots h D k)
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh (P).catalogue (P).routes F A))
local notation "start" => v.catalystStaticStart P h width
local notation "owner" => sinkBank start cnt r (P).catalogue.rows
local notation "order" => wideRouteOrder h D k
local notation "route" => source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "endCore" => CoreRoute.stop v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "recipe" => routeBanks start cnt r
local notation "pair" => fun j : Columns h D×Fin k => (pairKeys (Columns h D) k j).val
local notation "page" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement page stock

/-- The original CT choice of the core edge and the original commodity row of
every repeated traversal are stored below the private calendar. -/
def WideSpillSource (π : Equiv.Perm (Fin (2^h))) (mem : Memory w) : Prop :=
  Readable route v.sampler h v.W k v.wideJobs (v.wideOrder h width) π mem ∧
    Installed recipe (spillOrder h v.W k) PurchaseInventory.slot pair mem

set_option cleanup.letToHave false in
set_option maxHeartbeats 2000000 in
/-- One authentic boot supplies both the pre-verdict and post-verdict price
reporters. The original recipe includes the repeated row occurrences. -/
theorem wide_spill_source (size : ℕ) (extent : (A).endAddress v.mesh ≤ size)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D)
    (room : (A).endAddress v.mesh < 2^w) :
    let m := v.wideSignedMidAt h width size stock v.radius π order raw
    Calendar.mounted C (events v.mesh) m →
      v.WideSpillSource h width π (run C (events v.mesh) m) ∧
      v.WideSpillSource h width π (v.wideSignedCheckoutAt h width size stock v.radius π order raw) := by
  intro m live
  obtain ⟨_,_,seen,_,_,_,_,fixed,_⟩ :=
    v.wide_signed_boot_at h width size extent stock v.radius π order raw room
  have coreEnd : endCore ≤ (A).first := (v.wideGeometryPrefix h width).2.2.trans (v.catalyst_initial_le_first P h width)
  have floor : (A).first ≤ (A).endAddress v.mesh := Nat.le_add_right ..
  have firstWord := floor.trans_lt room
  have ownerEnd : (owner).base+(owner).size ≤ (A).first := (v.catalyst_static_end P h width A).le
  have space := allocated_space start cnt r (P).catalogue.rows w (⟨0,page+2⟩ : Bank) (8*2^page)
    (ownerEnd.trans_lt firstWord)
  have kind := space.kindEnd
  have mode := space.modeEnd
  have operand := space.operandEnd
  have one : (recipe).kind.base+(recipe).kind.size ≤ (A).first := by omega
  have two : (recipe).mode.base+(recipe).mode.size ≤ (A).first := by omega
  have three : (recipe).operand.base+(recipe).operand.size ≤ (A).first := by omega
  have transport (out : Memory w) (same : ∀i<(A).first,out i=m i) : v.WideSpillSource h width π out := by
    have now := seen.frame (coreEnd.trans_lt firstWord) (fun i hi => same i (hi.trans_le coreEnd))
    exact ⟨now.readable ((Nat.le_add_right ..).trans (coreEnd.trans firstWord.le)),
      installed_frame recipe order PurchaseInventory.slot pair m out (A).first fixed.route one two three same⟩
  have low (i : ℕ) (hi : i<(A).first) : run C (events v.mesh) m i=m i :=
    run_frame C _ m i live (fun e _ => (v.event_prefix P h width r banks (TerminalLayout.source page)
      (TerminalLayout.table page) (TerminalLayout.destination page) owner e i (hi.trans_le (Nat.le_add_right ..))).1)
  exact ⟨transport _ low,transport _ (fun i hi => (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _
    (.inl (hi.trans_le floor))).trans (low i hi))⟩

end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
