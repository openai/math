import OAI.Hierarchy.TaggedWidePruneRoom
import OAI.Hierarchy.TaggedWidePruneCodes
import OAI.Hierarchy.TaggedWideWindowWidthCap
import OAI.Hierarchy.TaggedWideWidthRoom

namespace OAI
/-! # Word bounds for pruning the signed, settled original rows -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart StripDirectory CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open Filter Tagged CorrectionFrame
open scoped Classical Fin.CommRing BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
set_option quotPrecheck false
set_option maxRecDepth 8192
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h

open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "order" => v.wideOrder h width

local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "original" => TerminalLayout.reserve start cnt page
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width

local notation "o" => wideRouteOrder h D k

local notation "place" => siteNumber h D k
local notation "ss" => v.widePaidSlices h width v.maxBits
variable (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "seed" => v.wideFundedRaw h width v.maxBits raw
local notation "chk" => v.wideSignedCheckoutAt h width size stock v.radius π o seed
local notation "mount" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mount o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))

/-- The common native pruning comparison uses the settled row lengths, widths
and the original column reserve in every direction. -/
structure PrunePrices (output : Fin rows → ProtocolRAMEmit.Row) : Prop where
  metric : BoughtSockets.Public.maxMetric v.radius < 2^w
  locations : Fintype.card (Location k) < 2^w
  codes : ∀i,(output i).lengthCode ≤ BoughtSockets.Public.maxMetric v.radius
  score : (∑i, PruneFlag.charge (boardLayout h D k width (fuel v.mesh*width)) (output i)) < 2^w
  threshold : 2*v.radius*(∑ _ : Fin k,Fintype.card (Columns h D)*(fuel v.mesh*width))-2^h*width < 2^w

/-- The estimate is uniform in the individual row values and the choice of tape. -/
theorem wide_prune_scalar {κ B : ℝ} (unitCost : ℕ) :
    ∀ᶠ x : WideParent κ B in WideParent.large κ B,
      ∀ output : Fin (v.widePlacement x.h x.w).catalogue.rows → ProtocolRAMEmit.Row,
        (∀i,(output i).lengthCode ≤ BoughtSockets.Public.maxMetric v.radius) →
        (∀i,(output i).width ≤ v.wideInstalledCap unitCost*x.w) →
        v.PrunePrices x.h x.w output := by
  let coef := k*siteFactor D k*fuel v.mesh
  let power := max 0 B
  have pos : 0 ≤ power := le_max_left ..
  have grow : Tendsto (WideParent.h (κ:=κ) («A»:=B)) (WideParent.large κ B) atTop := tendsto_comap
  filter_upwards [grow.eventually (Tagged.eventually_pruning_fits power pos v.rowFactor coef
      (v.wideInstalledCap unitCost) (BoughtSockets.Public.maxMetric v.radius) v.radius 1),
    grow.eventually (BoughtSockets.Public.metric_eventually v.W v.radius),
    grow.eventually (eventually_ge_atTop (Fintype.card (Location k)))] with x bill metric tall
  intro output codes widths
  have xnonneg : 0≤(x.h:ℝ) := Nat.cast_nonneg _
  have wide : (x.w:ℝ) ≤ (2*(x.h:ℝ))^power :=
    x.property.1.2.2.trans ((Real.rpow_le_rpow_of_exponent_le x.formats.1.le (le_max_right ..)).trans
      (Real.rpow_le_rpow xnonneg (by linarith) pos))
  let W := Native.wordBits x.h D Native.copies
  have word : 2*x.h+1 ≤ W := by
    change 2*x.h+1 ≤ Native.wordBits x.h D Native.copies
    rw [Native.wordBits_linear]
    omega
  have columns := CoreRoute.column_count x.h D k Nat.one_le_two_pow
  have reserve : (∑ _ : Fin k,Fintype.card (Columns x.h D)*(fuel v.mesh*x.w)) ≤ coef*2^x.h*x.w := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    calc
      _ ≤ k*((siteFactor D k*2^x.h)*(fuel v.mesh*x.w)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ columns)
      _ = _ := by dsimp only [coef]; ring
  obtain ⟨score,threshold⟩ := bill (W:=W) (boardLayout x.h D k x.w (fuel v.mesh*x.w)) output
    word wide (v.wideCatalogueRows x.h x.w) codes widths reserve
  have loc := (tall.trans_lt Nat.lt_two_pow_self).trans_le
    ((Native.height_extent x.h D).trans (Native.extent_word x.h D Native.copies).le)
  exact ⟨metric,loc,codes,score,by simpa only [mul_one] using threshold⟩

def WidePrunePricesAt : Prop :=
  chk ((A).endAddress v.mesh)=0 →
  ∀ {entries : ℕ} (site : Fin entries→Fin num) (debit : Fin entries→ℕ) (cj : Columns h D×Fin k→Fin num),
    Whole.Reconciliation sink original supply site debit ord ci cj archive →
    let closed:=ReserveUse.output original old supply site debit archive
    let output:=(sink).terminalRows closed ord ci (fun j=>(cj j).val)
    v.PrunePrices h width output

theorem wide_prune_prices {κ B : ℝ} (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost) :
    ∀ᶠ x : WideParent κ B in WideParent.large κ B, ∀ size, v.wideFundedSize x.h x.w v.maxBits≤ size →
      ∀ (π : Equiv.Perm (Fin (2^x.h))) (raw : Boot.Tape x.h (2^v.W)),
        v.WidePrunePricesAt x.h x.w size π raw := by
  have grow : Tendsto (WideParent.h (κ:=κ) («A»:=B)) (WideParent.large κ B) atTop := tendsto_comap
  filter_upwards [v.wide_prune_scalar (κ:=κ) (B:=B) unitCost,
    grow.eventually v.wide_funded_length_codes,
    v.wideWindow_raw_cap (κ:=κ) (B:=B) unitCost rate,
    WideParent.fixed_mul_width (κ:=κ) («A»:=B) 1,
    WideParent.fixed_mul_width (κ:=κ) («A»:=B) v.keepLimit] with x price codes widths small budget
  intro size extent π raw good entries site debit cj receipt closed output
  apply price output
  · have below : x.w≤2^x.h := by simpa only [one_mul] using (Nat.le_add_right (1*x.w) 1).trans small
    exact codes x.w v.maxBits size extent below budget
      π raw site debit (fun j=>(cj j).val)
  · exact widths size extent π raw good site debit cj receipt

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
