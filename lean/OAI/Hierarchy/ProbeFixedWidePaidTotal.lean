import OAI.Hierarchy.ProbeFixedPaidAttemptCeiling
import OAI.Hierarchy.ProbeFixedWidePaidRun
import OAI.Hierarchy.ProbeFixedWideSpillCases
import OAI.Hierarchy.ProbeArchiveRowBound
import OAI.Hierarchy.TaggedWideWidthRoom

namespace OAI
/-! # Natural-number fit of every recorded paid prefix, including the total -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StockCommit
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

/-- The coefficient depends only on the fixed format and the actual finite selector menu. -/
def paidWordFactor (bits : ℕ) :=
  (events v.mesh).length * (Classical.choose v.wideArena*(2*v.menu.maximum+bits) +
    v.overflowFactor v.menu.maximum + FeedLayout.lanes (publicStages v.W) k*v.overflowFactor (v.keepLimit+1))

/-- On the actual original signed checkout, every paid cardinality fits a
native word before casting, with the same bound for a stopped history. -/
theorem wide_paid_total_bill (bits : ℕ) :
    ∀ᶠ h : ℕ in Filter.atTop,∀ width, width≤2^h → v.widthFloor≤width → v.keepLimit*width+1≤2^h →
      v.paidWordFactor bits*width≤2^h →
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let funds:=v.fixedTerminalStock placed h width
      let ordering:=wideRouteOrder h (2^v.W) k
      ∀ size,arena.endAddress v.mesh ≤ size → ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),
      let final:=v.wideSignedCheckoutAt h width size funds v.radius π ordering raw
      final (arena.endAddress v.mesh)=0 → ∀e : Fin placed.catalogue.rows,
        PaidWidths.total (v.widePaidSlices h width bits) final e≤2^h*2^h := by
  filter_upwards [v.wide_paid_spill_cases,Filter.eventually_ge_atTop v.wideStockHeight] with h casesAt late
  intro width small floor budget paid placed arena funds ordering size extent π raw final accept e
  let boards := v.nativeBoards placed h width
  let N := Stages h (2^v.W)
  let r := Fintype.card (Slots h (2^v.W) k)
  let start := v.catalystStaticStart placed h width
  let cnt := rowOnlyCount v.mesh (declaredRows v.mesh
    (ownerLedger boards v.mesh placed.catalogue placed.routes F arena))
  let page := v.wideSignedPage h width funds
  let banks := TerminalLayout.settlement page funds
  let src := TerminalLayout.source page
  let tab := TerminalLayout.table page
  let dst := TerminalLayout.destination page
  let owners := sinkBank start cnt r placed.catalogue.rows
  let sink := placed.catalogue.sink r banks src tab dst owners
  let chart := v.wideSignedChart h width funds
  let fmt := v.nativeFormats placed h width
  let lay := FeedLayout.atEvent (N:=N) v.mesh arena fmt placed.joint.initial width v.keepLimit
  let route := CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
    (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
  let coreSpill := v.paidSpillPath placed h width (routeBanks start cnt r) route ordering
  let feedSpill := v.paidFeedPath placed h width route lay
  let original := v.wideSignedMidAt h width size funds v.radius π ordering raw
  let stages:=v.wide_stock_sizes h width late budget small
  have run:=v.wide_stock_at h width size extent v.radius π raw late budget small
  have native:=v.wide_stock_layout h width size extent v.radius π raw stages.words budget
    stages.width stages.alphabet stages.rowsMass stages.roles
  have spill:=casesAt width small floor budget size extent π raw accept
  let branch:=v.overflowFactor v.menu.maximum
  let feeds:=v.overflowFactor (v.keepLimit+1)
  let U:=arena.first*(2*v.menu.maximum+bits)+branch+FeedLayout.lanes N k*feeds
  let rows := v.wideEventSlices h width bits
  have price (ev : Event) (active : ev∈events v.mesh) : PaidWidths.total (rows ev) final e≤U*width := by
    cases ev with
    | attempt a =>
      obtain ⟨before,after,split⟩:=List.append_of_mem active
      let atTime:=Calendar.run chart before original
      have cut:=slot_of_split chart original (.attempt a) before after atTime split rfl run.mounted_all
      have single:=v.paid_attempt_ceiling placed h width r banks src tab dst owners a original atTime before after cut
        (native a active).1 stages.strip small stages.words.addresses sink placed.catalogue.idBase (StripChart.header F boards a).fieldTerm
        (StripChart.id F boards placed.catalogue a) (coreSpill a) bits branch e (spill.1 a active e)
      exact single.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    | feed b =>
      have single:=boundary_per_row (lay b) (feedSpill b) final (feeds*width) e
        (fun c hc=>spill.2 b active c hc e)
      have scaled : FeedLayout.lanes N k*feeds≤U:=Nat.le_add_left _ _
      change PaidWidths.total (rows (.feed b)) final e ≤ FeedLayout.lanes N k*(feeds*width) at single
      rw [← Nat.mul_assoc] at single
      exact single.trans (Nat.mul_le_mul_right width scaled)
  have maxlen:=paid_history_prefix v.mesh rows final e U width (events v.mesh).length price
  rw [←event_count,List.take_length] at maxlen
  have full : PaidWidths.total (v.widePaidSlices h width bits) final e≤(events v.mesh).length*U*width:=maxlen
  let a:=Classical.choose v.wideArena
  let cost:=2*v.menu.maximum+bits
  let L:=FeedLayout.lanes (publicStages v.W) k
  have first : arena.first≤a*2^h:=(Nat.le_add_right _ _).trans (Classical.choose_spec v.wideArena h width budget)
  have positive : 1≤2^h:=Nat.one_le_two_pow
  have high : U≤2^h*(a*cost+branch+L*feeds) := by
    change arena.first*cost+branch+FeedLayout.lanes N k*feeds≤_
    rw [show N=publicStages v.W from fixed_stage_count h v.W]
    calc arena.first*cost+branch+L*feeds
        ≤ (a*2^h)*cost+(2^h)*branch+(2^h)*(L*feeds) := by
            exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ first)
              (by simpa using Nat.mul_le_mul_right branch positive))
              (by simpa using Nat.mul_le_mul_right (L*feeds) positive)
      _ = _ := by ring
  calc PaidWidths.total (v.widePaidSlices h width bits) final e
      ≤ (events v.mesh).length*U*width:=full
    _ ≤ (events v.mesh).length*(2^h*(a*cost+branch+L*feeds))*width:=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ high)
    _ = 2^h*(v.paidWordFactor bits*width) := by
      unfold paidWordFactor
      dsimp only [a,cost,branch,L,feeds]
      ring
    _ ≤ 2^h*2^h:=Nat.mul_le_mul_left _ paid

private theorem paid_square_room (h : ℕ) : 2^h*2^h<2^(Native.wordBits h (2^v.W) Native.copies) := by
  rw [←pow_add]
  apply Nat.pow_lt_pow_right (by decide)
  rw [Native.wordBits_linear]
  omega

/-- On the actual original signed checkout, every paid cardinality fits a
native word before casting, with the same bound for a stopped history. -/
theorem wide_paid_total_fits (bits : ℕ) :
    ∀ᶠ h : ℕ in Filter.atTop,∀ width, width≤2^h → v.widthFloor≤width → v.keepLimit*width+1≤2^h →
      v.paidWordFactor bits*width≤2^h →
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let funds:=v.fixedTerminalStock placed h width
      let ordering:=wideRouteOrder h (2^v.W) k
      ∀ size,arena.endAddress v.mesh ≤ size → ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),
      let final:=v.wideSignedCheckoutAt h width size funds v.radius π ordering raw
      final (arena.endAddress v.mesh)=0 → ∀e : Fin placed.catalogue.rows,
        PaidWidths.total (v.widePaidSlices h width bits) final e<2^(Native.wordBits h (2^v.W) Native.copies) := by
  filter_upwards [v.wide_paid_total_bill bits] with h cost
  intro width small floor budget factor placed arena funds ordering size extent π raw final accepted e
  exact (cost width small floor budget factor size extent π raw accepted e).trans_lt (v.paid_square_room h)

/-- The live paid total has room for the entire terminal return, counted with multiplicity. -/
theorem cofinal_terminal_bill {κ B : ℝ} (bits : ℕ) :
    ∀ᶠ x : Tagged.WideParent κ B in Tagged.WideParent.large κ B,
      let placed:=v.widePlacement x.h x.w
      let arena:=v.privateArena placed x.h x.w
      let funds:=v.fixedTerminalStock placed x.h x.w
      let lanes:=wideRouteOrder x.h (2^v.W) k
      ∀ size,arena.endAddress v.mesh ≤ size → ∀ (π : Equiv.Perm (Fin (2^x.h))) (raw : Boot.Tape x.h (2^v.W)),
      let final:=v.wideSignedCheckoutAt x.h x.w size funds v.radius π lanes raw
      final (arena.endAddress v.mesh)=0 → ∀e : Fin placed.catalogue.rows,
        PaidWidths.total (v.widePaidSlices x.h x.w bits) final e+(v.overflowFactor v.keepLimit+fuel v.mesh)*x.w<2^(Native.wordBits x.h (2^v.W) Native.copies) := by
  have heights : Filter.Tendsto (Tagged.WideParent.h (κ:=κ) (A:=B)) (Tagged.WideParent.large κ B)
      Filter.atTop:=Filter.tendsto_comap
  let ret:=v.overflowFactor v.keepLimit+fuel v.mesh
  filter_upwards [heights.eventually (v.wide_paid_total_bill bits),
    heights.eventually (Filter.eventually_ge_atTop v.widthFloor),
    Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=B) 1,
    Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=B) v.keepLimit,
    Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=B) (v.paidWordFactor bits),
    Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=B) ret] with x uniform floor small budget factor extra
  intro placed arena funds lanes size extent π raw final accept e
  let H:=2^x.h
  have paid:=uniform x.w (by simpa only [one_mul] using (Nat.le_succ _).trans small)
    (floor.trans x.property.1.2.1) budget ((Nat.le_succ _).trans factor) size extent π raw accept e
  have unit : 1≤H:=Nat.one_le_two_pow
  have room : H*H+H<2^(Native.wordBits x.h (2^v.W) Native.copies) := by
    calc H*H+H≤H*H+H*H:=Nat.add_le_add_left (by simpa using Nat.mul_le_mul_left H unit) _
         _ = 2^(x.h+x.h+1) := by rw [pow_succ,pow_add];change H*H+H*H=H*H*2;omega
         _ < _ := by apply Nat.pow_lt_pow_right (by decide);rw [Native.wordBits_linear];omega
  exact (Nat.add_le_add paid ((Nat.le_succ _).trans extra)).trans_lt room

/-- Uniform in all allowed payloads of the wide step. The space needed by the
fixed catalogue and every dated paid total follows from the allowed width range. -/
theorem cofinal_paid_total_fits {κ B : ℝ} (bits : ℕ) :
    ∀ᶠ x : Tagged.WideParent κ B in Tagged.WideParent.large κ B,
      let placed:=v.widePlacement x.h x.w
      let arena:=v.privateArena placed x.h x.w
      let funds:=v.fixedTerminalStock placed x.h x.w
      let lanes:=wideRouteOrder x.h (2^v.W) k
      ∀ size,arena.endAddress v.mesh ≤ size → ∀ (π : Equiv.Perm (Fin (2^x.h))) (raw : Boot.Tape x.h (2^v.W)),
      let final:=v.wideSignedCheckoutAt x.h x.w size funds v.radius π lanes raw
      final (arena.endAddress v.mesh)=0 → ∀e : Fin placed.catalogue.rows,
        PaidWidths.total (v.widePaidSlices x.h x.w bits) final e<2^(Native.wordBits x.h (2^v.W) Native.copies) := by
  have heights : Filter.Tendsto (Tagged.WideParent.h (κ:=κ) (A:=B)) (Tagged.WideParent.large κ B)
      Filter.atTop:=Filter.tendsto_comap
  filter_upwards [heights.eventually (v.wide_paid_total_fits bits),
    heights.eventually (Filter.eventually_ge_atTop v.widthFloor),
    Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=B) 1,
    Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=B) v.keepLimit,
    Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=B) (v.paidWordFactor bits)]
    with x uniform floor small budget factor
  exact uniform x.w (by simpa only [one_mul] using (Nat.le_succ _).trans small)
    (floor.trans x.property.1.2.1) budget ((Nat.le_succ _).trans factor)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
