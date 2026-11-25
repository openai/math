import OAI.Hierarchy.ProbeFixedWideTestWordRoom
import OAI.Hierarchy.ProbeFixedWideFrozenReady
import OAI.Hierarchy.ProbeFixedWideStockOrigin
import OAI.Hierarchy.ProbeFixedDiscrepancyCeilings
import OAI.Hierarchy.ProbeFixedStripCounts

namespace OAI
/-! # Scalar capacities and both initial stock banks for the wide signed run -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CoreRoute
open CatalystArchive StripChart StripDirectory StockBound Filter
open scoped Classical Fin.CommRing
section Sizes
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "N" => Stages h (2^v.W)
local notation "w" => wordBits h (2^v.W) copies
local notation "G" => v.privateArena P h width
local notation "H" => v.publicHeader P h width
local notation "cells" => PurchaseInventory.footprint h N k
local notation "slots" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "tbl" => sliceROM ((P).joint.initial+cells) v.mesh.reserveSteps (v.keepLimit*width+1)

private abbrev stockMarketHeight := max (2*k+v.sampler.degree) (max v.menu.maximum ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊)

/-- The single height at which the two finite menus, their real discrepancy
words, the stock board and all table pages fit for the whole next family. -/
def wideStockHeight := max (max v.wideTestHeight (stockMarketHeight v))
  (max v.stripHeight (Classical.choose (Filter.eventually_atTop.mp v.discrepancy_word_room)))

structure WideStockSizes : Prop where
  words : v.TestWordRoom P h width
  market : (stockMarketHeight v)≤h
  strip : v.stripHeight≤h
  roles : slots≤2^w
  alphabet : v.menu.alphabet≤2^w
  copies : v.menu.copiesAt v.copyScale width<2^w
  mass : v.menu.alphabet*v.menu.copiesAt v.copyScale width<2^w
  rowsMass : v.menu.alphabet*width<2^w
  widthFit : width<2^w
  payloadWord : (H).payload.maxWord<2^w
  purchasedWord : (H).bought.maxWord<2^w

theorem wide_stock_sizes (late : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (payload : width≤2^h) :
    v.WideStockSizes h width := by
  have test : v.wideTestHeight≤h:=(le_max_left ..).trans ((le_max_left ..).trans late)
  have market : (stockMarketHeight v)≤h:=(le_max_right ..).trans ((le_max_left ..).trans late)
  have strip : v.stripHeight≤h:=(le_max_left ..).trans ((le_max_right ..).trans late)
  have disc:=Classical.choose_spec (Filter.eventually_atTop.mp v.discrepancy_word_room) h
    ((le_max_right ..).trans ((le_max_right ..).trans late)) P width
  have sum : v.stripPorts (publicStages v.W)+v.menu.alphabet+(1+v.menuCodes (publicStages v.W))+v.menu.maximum≤h :=
    (le_max_left ..).trans strip
  have roleEq : slots=v.stripPorts (publicStages v.W):=by rw [←fixed_stage_count h v.W];rfl
  have roles : slots≤h:=by rw [roleEq];omega
  have letters : v.menu.alphabet≤h:=by omega
  have date:=v.date_prefix_fit h
  have ht : h<2^w:=Nat.lt_two_pow_self.trans date
  have num : v.menu.copiesAt v.copyScale width≤width:=Nat.div_le_self ..
  have all : v.menu.alphabet*width<2^w:=by
    exact (Nat.mul_le_mul_left _ payload).trans_lt
      (by simpa only [Nat.mul_comm v.menu.alphabet] using linear_count h (2^v.W) copies v.menu.alphabet letters)
  exact ⟨v.wide_testWordRoom h width test budget,market,strip,roles.trans ht.le,letters.trans ht.le,
    (num.trans payload).trans_lt date,(Nat.mul_le_mul_left _ num).trans_lt all,all,payload.trans_lt date,
    disc.1,disc.2⟩

theorem wide_initial_room : (P).joint.initial+cells+(tbl).size≤(G).first := by
  let half:=JointHeader.half (P).joint h N k
  let score:=JointHeader.scores (P).joint h N k
  have row : (P).joint.initial+cells+(tbl).size=half.base:=rfl
  have first : half.base ≤ score.base:=Nat.le_add_right ..
  have tail : score.base≤(H).ports.base:=Nat.le_add_right ..
  exact row.le.trans (first.trans (tail.trans ((Nat.le_add_right ..).trans (v.catalyst_ports_le_first P h width))))

end Sizes
theorem WideStockSizes.width {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    {v : FixedProtocolFormat F k p q Q σ Λ} {h width : ℕ}
    (S : v.WideStockSizes h width) : width<2^(wordBits h (2^v.W) ProbeStage.Native.copies) := S.widthFit

section Origin
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "N" => Stages h (2^v.W)
local notation "w" => wordBits h (2^v.W) copies
local notation "G" => v.privateArena P h width

private theorem stockMarketHeight_eq_wideMarketHeight : stockMarketHeight v = v.wideMarketHeight := rfl

theorem wide_initial_stock (size : ℕ) (extent : (G).endAddress v.mesh ≤ size) (stock : Bank)
    (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (order : Orders h (2^v.W) k) (raw : Boot.Tape h (2^v.W))
    (room : (G).endAddress v.mesh<2^w) (late : v.stripHeight≤h) :
    let mid:=v.wideSignedMidAt h width size stock M π order raw
    (∀i : Commodity (Fin (2^h)) N k,PurchaseInventory.stock (P).joint.initial mid i=0) ∧
    ∀i : Commodity (Fin (2^h)) N k,PurchaseInventory.stock (v.emptyReserve P h width).base mid i=0 := by
  intro mid
  obtain ⟨_,_,_,_,_,prices,empty,_⟩:=v.wide_signed_boot_at h width size extent stock M π order raw room
  exact StockBound.boot_zeros (P).joint (DeadlineROM.prices v.mesh v.finish (v.basePhase width)) mid
    (v.emptyReserve P h width) prices empty (ProtocolRAMPurchaseSampler.lt_span _).le
    (v.purchased_table_room h late).2.2.2

end Origin
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
