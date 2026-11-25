import OAI.Hierarchy.ProbeFixedWideSpillMiddleBounds
import OAI.Hierarchy.ProbeFixedSharpPaidRows
import OAI.Hierarchy.TaggedWideSourceAlignmentUnique
import OAI.Hierarchy.TaggedWideSpillChordLimits

namespace OAI
/-! # The original paid per-event unit covers every dated spill-only bit aperture -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires WireTelescope
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
set_option quotPrecheck false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "order" => v.wideOrder h width
local notation "stock" => v.fixedTerminalStock P h width
local notation "last" => (events v.mesh).length
local notation "o" => wideRouteOrder h D k
local notation "cells" => PurchaseInventory.footprint h N k

variable (bits size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "mount" => (P).catalogue.coreMount π (siteNumber h D k) order chk
local notation "value" => v.wideDatedValue h width bits mid chk

local notation "lim" => max v.menu.maximum (v.keepLimit+1)

/-- The originally chosen sharp per-event tariff already pays both the worst
full commodity return and the largest raw spill. The unclipped inventory also
has its own separate original reserve of 2*keepLimit+1. -/
theorem wide_spill_unit_room (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost) :
    lim≤v.wideHistoryUnit unitCost ∧ v.overflowFactor lim≤v.wideHistoryUnit unitCost ∧
      (2*v.keepLimit+1)+lim≤v.wideHistoryUnit unitCost := by
  let factorMax:=max (v.overflowFactor v.menu.maximum) (v.overflowFactor (v.keepLimit+1))
  have fee : factorMax≤v.sharpPaidUnit := by
    change factorMax≤ max (2*v.paidRoleRate+v.forestFactor+factorMax) _
    exact (Nat.le_add_left ..).trans (le_max_left ..)
  have fixed : v.overflowFactor lim≤factorMax:=by
    by_cases h:v.menu.maximum≤v.keepLimit+1
    · rw [max_eq_right h];exact le_max_right ..
    · rw [max_eq_left (Nat.le_of_not_ge h)];exact le_max_left ..
  have positive : 0<(1+publicStages v.W*(2*k))*(2*publicStages v.W+2) := Nat.mul_pos (by omega) (by omega)
  have spans : lim≤v.overflowFactor lim := Nat.le_mul_of_pos_left _ positive
  have counted : 0<HistoryRoles.clock v.mesh:=by unfold HistoryRoles.clock;have started:=v.clock.inject_pos;positivity
  have lift:=Nat.le_mul_of_pos_left unitCost counted
  unfold wideHistoryUnit
  omega

variable (first : ℕ) (j : Fin (events v.mesh).length)
    (input : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "region" => v.wideSpillPage h width bits first j.val
local notation "spill" => fun x : Goods h v.W k=>RouteSettlement.actual (region).overflow input (PurchaseInventory.slot x)
local notation "mass" => routeLoad (mount).ordinary spill
local notation "pad" => publicChord h D k
local notation "shape" => (mount).datedLayout (siteNumber h D k).injective pad
variable (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost)
    (age : v.wideSpillOverflowHeight≤h)
    (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size)
    (floor : v.widthFloor≤width) (small : width≤2^h) (budget : v.keepLimit*width+1≤2^h)
    (scalar : PurchaseInventory.footprint h (Stages h (2^v.W)) k≤2^(Native.wordBits h (2^v.W) Native.copies))
    (rad : M=v.radius)
    (accepted : v.wideSignedCheckoutAt h width size (v.fixedTerminalStock (v.widePlacement h width) h width)
      M π (wideRouteOrder h (2^v.W) k) (v.wideFundedRaw h width bits raw)
      ((v.privateArena (v.widePlacement h width) h width).endAddress v.mesh)=0)
    (sourceFrame : ∀a<(v.privateArena (v.widePlacement h width) h width).endAddress v.mesh,
      input a=v.wideSignedCheckoutAt h width size (v.fixedTerminalStock (v.widePlacement h width) h width)
        M π (wideRouteOrder h (2^v.W) k) (v.wideFundedRaw h width bits raw) a)
include rate age extent floor small budget scalar rad accepted sourceFrame

theorem wide_spill_row_caps :
    (∀g,spill g≤v.wideHistoryUnit unitCost*width) ∧
      ∀e,mass e≤v.wideHistoryUnit unitCost*width := by
  have initialBound:=v.wide_spill_overflow_bound h width bits size M π raw first j input age extent floor small budget scalar rad accepted sourceFrame
  have new:=v.wide_spill_route_bound h width bits size M π raw region input initialBound
  have prices:=v.wide_spill_unit_room unitCost rate
  exact ⟨fun g=>(initialBound g).trans (Nat.mul_le_mul_right width prices.1),
    fun e=>(new e).trans (Nat.mul_le_mul_right width prices.2.1)⟩

theorem wide_spill_chord_measured (marks : Marks h v.W k v.wideJobs) (exclusive : Exclusive marks) :
    (∀c,installedWidths (shape).family ((shape).bits spill) c≤HistoryRoles.stride k v.sampler.degree v.wideJobs*(v.wideHistoryUnit unitCost*width)) ∧
      ∀c,installedWidths (shape).edge (routeLoad (shape).routes ((shape).bits spill)) c≤HistoryRoles.stride k v.sampler.degree v.wideJobs*(v.wideHistoryUnit unitCost*width) := by
  obtain ⟨before,after⟩:=v.wide_spill_row_caps h width bits size M π raw first j input unitCost rate age extent floor small budget scalar rad accepted sourceFrame
  let purchased:=v.wide_dated_bought_rows h width
  let axis:=pairKeys (Columns h D) k
  let names:=timeRows v.sampler π v.depth marks (P).catalogue order purchased axis
  let fields:=HistoryRoles.chord_width_room v.sampler π v.depth marks exclusive names
  constructor
  · intro c
    apply DatedSpillOffsets.old_chord_limit v.sampler π v.depth marks (P).catalogue order purchased axis chk pad spill _ _ c
    intro ch
    apply fields _ (v.wideHistoryUnit unitCost*width) _ ch
    intro i
    simp only [Function.comp_apply]
    generalize names i=a
    rcases a with t|g|b
    · exact Nat.zero_le _
    · exact before g
    · exact Nat.zero_le _
  · intro c
    apply DatedSpillOffsets.new_chord_limit v.sampler π v.depth marks (P).catalogue order purchased axis chk pad spill _ _ c
    intro ch
    apply fields _ (v.wideHistoryUnit unitCost*width) _ ch
    intro i
    simp only [Function.comp_apply]
    generalize names i=a
    cases a with
    | inl b=>exact after _
    | inr x=>exact Nat.zero_le _

omit rate age extent floor small budget scalar rad accepted sourceFrame in
theorem wide_neighbor_strict (u : ℕ) :
    HistoryRoles.stride k v.sampler.degree v.wideJobs*(v.wideHistoryUnit u*width)<v.wideNeighborCap width u := by
  unfold wideNeighborCap wideNeighborDigits
  rw [←Nat.mul_assoc]
  exact (Nat.le_pow_clog (by decide : 1<2) _)

omit rate age extent floor small budget scalar rad accepted sourceFrame in
theorem wide_neighbor_word (u : ℕ) (price : HistoryRoles.stride k v.sampler.degree v.wideJobs *
    v.wideHistoryUnit u≤h) (smallWidth : width≤2^h) : v.wideNeighborCap width u≤2^w := by
  have limit:=v.wide_spill_mul_room h width _ price smallWidth
  apply Nat.pow_le_pow_right (by decide)
  apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr
  exact limit

omit rate age extent floor small budget scalar rad accepted sourceFrame in
theorem wide_neighbor_chord_lt (u : ℕ) (π : Equiv.Perm (Fin (2^h)))
    (marks : Marks h v.W k v.wideJobs) (ex : Exclusive marks)
    {n : ℕ} (chart : Fin n≃HistoryRoles.Source v.sampler π v.depth marks) (qty : Fin n→ℕ)
    (bounded : ∀i,qty i≤v.wideHistoryUnit u*width) (c) :
    installedWidths (HistoryRoles.sorted v.sampler π v.depth marks ∘ chart) qty c<v.wideNeighborCap width u :=
  (HistoryRoles.chord_width_room v.sampler π v.depth marks ex chart qty _ bounded c).trans_lt
    (v.wide_neighbor_strict width u)

theorem wide_spill_chord_strict (marks : Marks h v.W k v.wideJobs) (exclusive : Exclusive marks) :
    (∀c,installedWidths (shape).family ((shape).bits spill) c<v.wideNeighborCap width unitCost) ∧
      ∀c,installedWidths (shape).edge (routeLoad (shape).routes ((shape).bits spill)) c<v.wideNeighborCap width unitCost := by
  have count:=v.wide_spill_chord_measured h width bits size M π raw first j input unitCost rate age extent floor small budget scalar rad accepted sourceFrame marks exclusive
  have positive:=v.wide_neighbor_strict width unitCost
  exact ⟨fun c=>(count.1 c).trans_lt positive,fun c=>(count.2 c).trans_lt positive⟩

theorem wide_spill_chord_caps (marks : Marks h v.W k v.wideJobs) (exclusive : Exclusive marks) :
    (∀c,installedWidths (shape).family ((shape).bits spill) c≤v.wideNeighborCap width unitCost) ∧
      ∀c,installedWidths (shape).edge (routeLoad (shape).routes ((shape).bits spill)) c≤v.wideNeighborCap width unitCost := by
  have cap:=v.wide_spill_chord_strict h width bits size M π raw first j input unitCost rate age extent floor small budget scalar rad accepted sourceFrame marks exclusive
  exact ⟨fun c=>(cap.1 c).le,fun c=>(cap.2 c).le⟩

variable (marks : Marks h v.W k v.wideJobs) (exclusive : Exclusive marks)
local notation "cardData" => v.wide_dated_bought_rows h width
local notation "recordRows" => timeRows v.sampler π v.depth marks (P).catalogue order cardData (pairKeys (Columns h D) k)
local notation "storedKey" => DatedRows.embed v.sampler π v.depth marks (P).catalogue order cardData
local notation "limitQty" => v.wideHistoryUnit unitCost*width
local notation "sortedRecords" => HistoryRoles.sorted v.sampler π v.depth marks ∘ recordRows
variable (issued : Attempt→CatalystArchive.Entry (Fintype.card (Columns h (2^v.W))*k) width)
local notation "afterQty" => value issued (j.val+1)
local notation "middleQty" => FeedTransfer.middleAmounts mount afterQty spill ∘ storedKey ∘ recordRows

/-- A positive source can be present at this date even if its final inventory is zero.
The bound for its uncut amount uses the actual stock at the end of the event. -/
theorem wide_spill_preclip_rows (horizon : v.wideFundedSize h width bits≤ size)
    (fundedAge : v.wideFundedHeight≤h)
    (regular : ∀i,(afterQty ∘ storedKey ∘ recordRows) i≤limitQty) :
    ∀i,middleQty i≤limitQty := by
  have run:=v.wide_funded_stock_at_size h width M π raw bits size horizon fundedAge budget small
  have upper:=v.wide_spill_overflow_bound h width bits size M π raw first j input age extent floor small budget scalar rad accepted sourceFrame
  have margin:=(v.wide_spill_unit_room unitCost rate).2.2
  intro i
  have bound:=regular i
  simp only [Function.comp_apply] at bound ⊢
  cases idEq:recordRows i with
  | inl e=>
    rw [idEq] at bound
    exact (Nat.sub_le ..).trans bound
  | inr s₀=>cases s₀ with
    | inl g₀=>
      have held:=v.wide_spill_held_bound h width mid (j.val+1) j.isLt run g₀
      exact (Nat.add_le_add held (upper g₀)).trans
        (by rw [←Nat.add_mul];exact Nat.mul_le_mul_right width margin)
    | inr c=>
      rw [idEq] at bound
      exact bound

include exclusive in
theorem wide_spill_full_chords (horizon : v.wideFundedSize h width bits≤ size) (fundedAge : v.wideFundedHeight≤h)
    (regular : ∀(t : Fin (last+1)) i,(value issued t.val ∘ storedKey ∘ recordRows) i≤limitQty) :
    (∀(t : Fin (last+1)) c,installedWidths sortedRecords (value issued t.val ∘ storedKey ∘ recordRows) c <
      v.wideNeighborCap width unitCost) ∧
      ∀c,installedWidths sortedRecords middleQty c < v.wideNeighborCap width unitCost := by
  have uncut:=v.wide_spill_preclip_rows h width bits size M π raw first j input unitCost rate age extent floor small
    budget scalar rad accepted sourceFrame marks issued horizon fundedAge (regular j.succ)
  exact ⟨fun t=>v.wide_neighbor_chord_lt h width unitCost π marks exclusive recordRows _ (regular t),
    v.wide_neighbor_chord_lt h width unitCost π marks exclusive recordRows _ uncut⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
