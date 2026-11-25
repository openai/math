import OAI.Hierarchy.ProbeFixedFailureWords
import OAI.Hierarchy.ProbeFixedRowKey
import OAI.Hierarchy.ProtocolRAMCalendarEconomicBoot

namespace OAI
/-! # Exact score, packet, alphabet, and selector-charge pages of the mounted rows -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width : ℕ)
local notation "N" => Stages z (2^v.W)
local notation "H" => v.publicHeader P z width
local notation "bs" => v.nativeBoards P z width
local notation "fm" => v.nativeFormats P z width
local notation "phaseRows" => DeadlineROM.prices v.mesh v.finish (v.basePhase width)
local notation "FEE" => StripChart.charges F (v.sized (v.seed P z width) width) v.cost (H).stop
local instance rowPagesPayloadRoleNonempty : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
local instance rowPagesPurchasedRoleNonempty : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
variable (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "W" => wordBits z (2^v.W) copies

theorem rowPhase_params (u : Fin (DeadlineROM.count v.mesh)) :
    (phaseRows u).M=(v.radius:ℝ) ∧ (phaseRows u).precision=v.precision := by
  let slot : Fin (DeadlineROM.rows v.mesh) × Fin (DeadlineROM.levels v.mesh) :=
    finProdFinEquiv.symm u
  by_cases outer : slot.2.val = 0
  · dsimp only [slot] at outer
    simp only [DeadlineROM.prices, ite_eq_left outer]; exact ⟨rfl,rfl⟩
  · dsimp only [slot] at outer
    simp only [DeadlineROM.prices, ite_eq_right outer]; exact ⟨rfl,rfl⟩

section
variable (phase trial : ℕ)
local notation "ev" => Attempt.outer phase trial
local notation "u₀" => DeadlineROM.index v.mesh ev
local notation "surface" => (bs).outer phase trial
local notation "channels" => payloadChannels z N k
local notation "old" => ({(surface).old with base:=(fm ev).market.shelf.stockBase})
local notation "J" => PayloadStrip.Quotes N k
local notation "menu" => payloadMenu F N k (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos
  ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum

/-- The quoted instruction and row predicate in the installed market. -/
def payloadTest : StripTest (Fintype.card J) :=
  tested {(surface).test with live:=(channels).live,rows:=(fm ev).market.rows,population:=2^z}
    (surface).price (GlobalTests.offsets (surface).globalTests) old (channels).digit

local notation "test" => v.payloadTest P z width phase trial

theorem payload_failure : (fm ev).market.failures=(test).failure := rfl

def payloadPagePrice (u : Fin (DeadlineROM.count v.mesh))
    (key : Fin (Fintype.card J) → Fin v.digitRadix) := PayloadStrip.prices N k v.radius (payloadGrid v.digitRadix (phaseRows u).precision key)

local notation "grid₀" => v.payloadPagePrice z width

theorem payload_page_grid (u : Fin (DeadlineROM.count v.mesh)) (key : Fin (Fintype.card J) → Fin v.digitRadix) :
    grid₀ u key = PayloadStrip.prices N k v.radius (payloadGrid v.digitRadix v.precision key) := by
  dsimp only [payloadPagePrice]
  rw [(v.rowPhase_params width u).2]

theorem payload_vector_word (u : Fin (DeadlineROM.count v.mesh)) (key : Fin (Fintype.card J) → Fin v.digitRadix) :
    (H).payload.word u key =
      AttemptGate.discrepancyWord F (PayloadStrip.wires N k) (PayloadStrip.demands N k) (grid₀ u) v.precision key := by
  change AttemptGate.discrepancyWord F _ _
    (fun h => PayloadStrip.prices N k (phaseRows u).M (payloadGrid v.digitRadix (phaseRows u).precision h))
    v.precision key=_
  rw [(v.rowPhase_params width u).1]
  rfl

theorem payload_vector (entry : Memory W) (header : (H).Resident entry)
    (maxWord : (H).payload.maxWord < 2^W) (key : Fin (Fintype.card J) → Fin v.digitRadix) :
    (test).table.read entry ((finFunctionFinEquiv key).val:Word W)=
      (AttemptGate.discrepancyWord F (PayloadStrip.wires N k) (PayloadStrip.demands N k) (grid₀ u₀) v.precision key:Word W) ∧
      AttemptGate.discrepancyWord F (PayloadStrip.wires N k) (PayloadStrip.demands N k) (grid₀ u₀) v.precision key<2^W := by
  rw [←v.payload_vector_word P z width u₀ key]
  exact ⟨header.payload u₀ key,((H).payload.word_le u₀ key).trans_lt maxWord⟩

/-- Both tables serve the real compiled packet query. The same pages are used
by the raw inspection and the stock-gated ballot. -/
theorem payload_page_read (state : Memory W) (header : (H).Resident state) :
    (MenuROM.menus menu (H).bought.stop v.digitRadix grid₀).Resident state ∧
    (MenuROM.alphabets menu (H).menus.right.stop).Resident state := ⟨header.menus.left,header.menus.leftAlphabet⟩

theorem payload_page_operands :
    (b ev).menu=(MenuROM.menus menu (H).bought.stop v.digitRadix grid₀).bank u₀ ∧
    (b ev).radix=(test).radix ∧ (b ev).quotes=List.ofFn (test).quoted ∧
    (b ev).termCount=(MenuROM.alphabets menu (H).menus.right.stop).bank 0 := ⟨rfl,rfl,rfl,rfl⟩

theorem payload_charge_page (state : Memory W) (pages : (FEE).Resident state) :
    (v.taskCommit P z width ev).price=(MenuROM.selectorCharges menu (H).stop).bank 0 ∧
      (MenuROM.selectorCharges menu (H).stop).Resident state := ⟨rfl,pages.1⟩

end

section
variable (phase trial slice inner : ℕ)
local notation "ev" => Attempt.inner phase trial slice inner
local notation "u₀" => DeadlineROM.index v.mesh ev
local notation "surface" => (bs).inner phase trial slice inner
local notation "channels" => (purchasedChannels (z:=z) (d:=2^v.W) (k:=k) ((bs).outer phase trial).market.shelf (bs).sampler v.depth ((bs).stratumHeader phase trial))
local notation "old" => ({(surface).old with base:=(fm ev).market.shelf.stockBase})
local notation "J" => ChainStrip.Axes v.depth k
local notation "menu" => purchasedMenu F v.depth k (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos
  ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum

/-- The quoted instruction and row predicate in the installed market. -/
def purchasedTest : StripTest (Fintype.card J) :=
  tested {(surface).test with live:=(channels).live,rows:=(fm ev).market.rows,population:=2^z}
    (surface).price (GlobalTests.offsets (surface).globalTests) old (channels).digit

local notation "test" => v.purchasedTest P z width phase trial slice inner

theorem purchased_failure : (fm ev).market.failures=(test).failure := rfl

def purchasedPagePrice (u : Fin (DeadlineROM.count v.mesh))
    (key : Fin (Fintype.card J) → Fin v.digitRadix) := phaseGrid (depth:=v.depth) (k:=k) (phaseRows u) v.radius v.digitRadix key

local notation "grid₀" => v.purchasedPagePrice width

theorem purchased_page_grid (u : Fin (DeadlineROM.count v.mesh)) (key : Fin (Fintype.card J) → Fin v.digitRadix) :
    grid₀ u key = ChainStrip.prices v.depth k v.radius (gridAxes v.digitRadix v.precision key) := by
  dsimp only [purchasedPagePrice,phaseGrid]
  rw [(v.rowPhase_params width u).2]

theorem purchased_vector_word (u : Fin (DeadlineROM.count v.mesh)) (key : Fin (Fintype.card J) → Fin v.digitRadix) :
    (H).bought.word u key =
      AttemptGate.discrepancyWord F (ChainStrip.wires v.depth k) (ChainStrip.demands v.depth k) (grid₀ u) v.precision key := by
  change AttemptGate.discrepancyWord F _ _
    (phaseGrid (depth:=v.depth) (k:=k) (phaseRows u) (phaseRows u).M v.digitRadix)
    v.precision key=_
  rw [(v.rowPhase_params width u).1]
  rfl

theorem purchased_vector (entry : Memory W) (header : (H).Resident entry)
    (maxWord : (H).bought.maxWord < 2^W) (key : Fin (Fintype.card J) → Fin v.digitRadix) :
    (test).table.read entry ((finFunctionFinEquiv key).val:Word W)=
      (AttemptGate.discrepancyWord F (ChainStrip.wires v.depth k) (ChainStrip.demands v.depth k) (grid₀ u₀) v.precision key:Word W) ∧
      AttemptGate.discrepancyWord F (ChainStrip.wires v.depth k) (ChainStrip.demands v.depth k) (grid₀ u₀) v.precision key<2^W := by
  rw [←v.purchased_vector_word P z width u₀ key]
  exact ⟨header.bought u₀ key,((H).bought.word_le u₀ key).trans_lt maxWord⟩

/-- Both tables serve the real compiled packet query. The same pages are used
by the raw inspection and the stock-gated ballot. -/
theorem purchased_page_read (state : Memory W) (header : (H).Resident state) :
    (MenuROM.menus menu (H).menus.left.stop v.digitRadix grid₀).Resident state ∧
    (MenuROM.alphabets menu (H).menus.leftAlphabet.stop).Resident state := ⟨header.menus.right,header.menus.rightAlphabet⟩

theorem purchased_page_operands :
    (b ev).menu=(MenuROM.menus menu (H).menus.left.stop v.digitRadix grid₀).bank u₀ ∧
    (b ev).radix=(test).radix ∧ (b ev).quotes=List.ofFn (test).quoted ∧
    (b ev).termCount=(MenuROM.alphabets menu (H).menus.leftAlphabet.stop).bank 0 := ⟨rfl,rfl,rfl,rfl⟩

theorem purchased_charge_page (state : Memory W) (pages : (FEE).Resident state) :
    (v.taskCommit P z width ev).price=(MenuROM.selectorCharges menu (FEE).payload.stop).bank 0 ∧
      (MenuROM.selectorCharges menu (FEE).payload.stop).Resident state := ⟨rfl,pages.2⟩

end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
