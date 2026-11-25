import OAI.Hierarchy.ProbeFixedSpillWord
import OAI.Hierarchy.ProbeFixedSpillPlacement

namespace OAI
/-! # Clipping on the actual placed payload and purchased port banks -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native CoreBoard StripChart
open StockCommit PurchaseStage RepairHistogram CatalystArchive StripDirectory PurchaseFrozen CatalogueRows
open scoped BigOperators Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "bs" => v.nativeBoards P z width
local notation "H" => v.publicHeader P z width
local notation "f" => v.nativeFormats P z width
local notation "bills" => v.issued P z width r banks src tab dst owners
local notation "FEE" => charges F (v.sized (v.seed P z width) width) v.cost (H).stop
local notation "arena" => v.privateArena P z width

section
set_option maxRecDepth 4096
variable (phase trial : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.outer phase trial
local notation "pre" => (guard C ev).apply entry
local notation "checked" => postSnapshot ((C).layout ev) (repair C ev) (prepared C ev entry)
local notation "stage" => v.stage P z width r banks src tab dst owners ev entry
local notation "t" => Calendar.time v.mesh v.finish ev
variable (fitted : v.payloadStageSizes P z width r banks src tab dst owners phase trial entry)
local notation "x" => v.payloadStageInput P z width r banks src tab dst owners phase trial entry fitted
local notation "π" => v.payloadStage_compile P z width r banks src tab dst owners phase trial entry fitted
variable (s : v.RepairSlot P z width r banks src tab dst owners (.outer phase trial) entry)
local notation "live" => s.slot.currentReady
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry s.layout live π
local notation "test" => v.payloadTest P z width phase trial


attribute [local irreducible] permutationFabric
set_option cleanup.letToHave false
set_option maxHeartbeats 2500000 in
include fitted s in
omit [Nonempty (Fin k)] in
theorem payload_spill_word (i : Fin (f ev).pricedArea.goods) :
    let ar:=(f ev).pricedArea
    let out:=after C (.attempt ev) entry
    (out (ar.output+ar.goods+ar.goods+i.val)).val=
      v.repairRaw P z width r banks src tab dst owners ev entry i-(out (ar.output+i.val)).val ∧
    (out (ar.output+ar.goods+ar.goods+i.val)).val≤v.menu.maximum*width := by
  intro ar out
  have placed:=v.payload_spill_placed P z width r banks src tab dst owners phase trial entry fitted s
  have credit:=(x).credit_bound placed i
  have dims:=v.catalogue_words (v.seed P z width) width
  have maximum : (x).board.maxWidth=v.menu.maximum:=dims.2.1
  have copiesEq : (x).board.copies=v.menu.copiesAt v.copyScale width:=dims.2.2
  have creditAt := Nat.le_trans credit (congrArg₂ Nat.mul maximum copiesEq).le
  obtain ⟨site,reads⟩:=placed
  have seed (j : Fin (x).raw.coordinates) :
      (x).form.stockSource.old.read (x).mem (j.val:Word W)=(x).mem ((x).form.pricedArea.start+j.val) :=
    stage_seed_word_prefix (f ev).pricedArea (f ev).stockSource (v.stamp P z width r banks src tab dst owners ev)
      (postOutput ((C).layout ev) (repair C ev) (prepared C ev entry))
      (s.layout.window.old.trans s.layout.window.label)
      ((Nat.le_add_left _ _).trans (Nat.le_of_lt (x).bankFit)) s.layout.window.capacity.1 j
  exact v.repair_spill_word P z width r banks src tab dst owners ev entry s i ((x).funded site reads seed i) creditAt
end

section
set_option maxRecDepth 4096
variable (phase trial slice inner : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.inner phase trial slice inner
local notation "pre" => (guard C ev).apply entry
local notation "checked" => postSnapshot ((C).layout ev) (repair C ev) (prepared C ev entry)
local notation "stage" => v.stage P z width r banks src tab dst owners ev entry
local notation "t" => Calendar.time v.mesh v.finish ev
variable (fitted : v.purchasedStageSizes P z width r banks src tab dst owners phase trial slice inner entry)
local notation "x" => v.purchasedStageInput P z width r banks src tab dst owners phase trial slice inner entry fitted
local notation "π" => v.purchasedStage_compile P z width r banks src tab dst owners phase trial slice inner entry fitted
variable (s : v.RepairSlot P z width r banks src tab dst owners (.inner phase trial slice inner) entry)
local notation "live" => s.slot.currentReady
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry s.layout live π
local notation "test" => v.purchasedTest P z width phase trial slice inner
local notation "sh" => ((bs).outer phase trial).market.shelf
local notation "S" => (bs).sampler
local notation "h₀" => stratumHeader z (2^v.W) k (S).degree v.depth ((bs).stratumHeader phase trial)


attribute [local irreducible] permutationFabric
set_option cleanup.letToHave false
set_option maxHeartbeats 2500000 in
include fitted s in
omit [Nonempty (Fin k)] in
theorem purchased_spill_word (perm : Equiv.Perm (Fin (2^z))) (headLow : (h₀).stop≤(arena).base v.mesh (.attempt ev))
    (born : PurchasedBirth sh S perm v.depth ((bs).stratumHeader phase trial) entry k) (i : Fin (f ev).pricedArea.goods) :
    let ar:=(f ev).pricedArea
    let out:=after C (.attempt ev) entry
    (out (ar.output+ar.goods+ar.goods+i.val)).val=
      v.repairRaw P z width r banks src tab dst owners ev entry i-(out (ar.output+i.val)).val ∧
    (out (ar.output+ar.goods+ar.goods+i.val)).val≤v.menu.maximum*width := by
  intro ar out
  have placed:=v.purchased_spill_placed P z width r banks src tab dst owners phase trial slice inner entry fitted s perm headLow born
  have credit:=(x).credit_bound placed i
  have dims:=v.catalogue_words (v.seed P z width) width
  have maximum : (x).board.maxWidth=v.menu.maximum:=dims.2.1
  have copiesEq : (x).board.copies=v.menu.copiesAt v.copyScale width:=dims.2.2
  have creditAt := Nat.le_trans credit (congrArg₂ Nat.mul maximum copiesEq).le
  obtain ⟨site,reads⟩:=placed
  have seed (j : Fin (x).raw.coordinates) :
      (x).form.stockSource.old.read (x).mem (j.val:Word W)=(x).mem ((x).form.pricedArea.start+j.val) :=
    stage_seed_word_prefix (f ev).pricedArea (f ev).stockSource (v.stamp P z width r banks src tab dst owners ev)
      (postOutput ((C).layout ev) (repair C ev) (prepared C ev entry))
      (s.layout.window.old.trans s.layout.window.label)
      ((Nat.le_add_left _ _).trans (Nat.le_of_lt (x).bankFit)) s.layout.window.capacity.1 j
  exact v.repair_spill_word P z width r banks src tab dst owners ev entry s i ((x).funded site reads seed i) creditAt
end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
