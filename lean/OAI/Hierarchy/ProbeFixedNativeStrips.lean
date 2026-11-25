import OAI.Hierarchy.ProbeFixedFailureWords
import OAI.Hierarchy.ProbeFixedBranchFunds
import OAI.Hierarchy.ProbeFixedStripCurvature

namespace OAI
/-! # Literal strip inputs extracted from both branches of the fixed native chart -/

noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM Calendar Calendar.StockCommit PurchaseStage RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical Fin.CommRing

variable {A B C H F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype H] [Field F]
  {k sites N w q D z d : ℕ} [Nonempty (Fin sites)] [Nonempty (Fin k)] [Nonempty (Role C H (A⊕B) k)]
  {M ε tree : ℝ} {len : H→ℝ} {cap : A→ℝ}

variable {e : Role C H (A⊕B) k → Chord sites}

namespace StripInput
variable {menu : Probe.FixedMenu F e
    (demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B)))
    ((fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap)
    ε tree N}
  (x : _root_.OAI.Hierarchy.ProtocolRAM.CatalystArchive.StripInput (A:=A) (B:=B) (C:=C) (H:=H) (k:=k) menu w z d q D)


/-- Transport the plan before specializing it to the physical native board. -/
def alignedPlan (f : Format z d k q D) (b : Batch q D) (m : Memory w)
    (formEq : x.form=f) (ballotEq : x.ballot=b) (memoryEq : x.mem=m) :
    PortPlan (fresh f.pricedArea f.stockSource) b m f.market.rows := by
  subst f b m
  exact x.plan

end StripInput
end Hierarchy.ProtocolRAM.CatalystArchive

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart
open PurchaseStage StockCommit CatalystArchive StripDirectory PurchaseFrozen
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
variable [Nonempty (Fin k)]
local notation "N₀" => Stages z (2^v.W)
local notation "bs" => v.nativeBoards P z width
local notation "d₀" => Fintype.card (PayloadRole N₀ k)
local notation "d₁" => Fintype.card (PurchasedRole v.depth k)
local notation "D" => max d₀ d₁
local notation "stock[" a "]" => resolvedStock v.mesh (v.privateArena P z width) P.joint.initial (build F bs) a
local notation "snap[" a "," m "]" => v.stage P z width r banks src tab dst owners a m

section Payload
variable (phase trial : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.outer phase trial
local notation "surface" => ({(bs).outer phase trial with market:={((bs).outer phase trial).market with sampler:=(bs).sampler,depth:=v.depth}})
local notation "menu" => payloadMenu F N₀ k (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos
  ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum
local notation "raw" => (surface).build (payloadFormat F z (2^v.W) k _ (bs).positive (bs).radius (bs).radius_nonneg
  (bs).tolerance (bs).tolerance_pos ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum) stock[ev]
local notation "slots" => (payloadChannels z N₀ k).slot

abbrev payloadStageSizes := StripSizes raw slots ((bs).outer phase trial).start D (Fintype.card (menu).index)
  (PacketWidths.ofMenu menu).maximum snap[ev,entry]
local notation "Sizes" => v.payloadStageSizes P z width r banks src tab dst owners phase trial entry

def payloadStageInput (fitted : Sizes) :=
  StripInput.of_payload (F:=F) (z:=z) (d:=2^v.W) (k:=k) («D»:=D) (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos
    ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum surface stock[ev] ((bs).outer phase trial).start snap[ev,entry] fitted

local notation "actual[" f "]" => v.payloadStageInput P z width r banks src tab dst owners phase trial entry f

omit [Nonempty (Fin k)] in
theorem payloadStage_format (fitted : Sizes) : (actual[fitted]).form=v.nativeFormats P z width ev := rfl

omit [Nonempty (Fin k)] in
theorem payloadStage_ballot (fitted : Sizes) :
    (actual[fitted]).ballot=v.ballot P z width r banks src tab dst owners ev := rfl

omit [Nonempty (Fin k)] in
theorem payloadStage_memory (fitted : Sizes) : (actual[fitted]).mem=snap[ev,entry] := by
  simp only [payloadStageInput, StripInput.of_payload, StripInput.ofBoard]

def payloadStage_compile (fitted : Sizes) :
    PortPlan (v.taskCommit P z width ev) (v.ballot P z width r banks src tab dst owners ev)
      snap[ev,entry] (v.nativeFormats P z width ev).market.rows :=
  (actual[fitted]).alignedPlan (v.nativeFormats P z width ev) (v.ballot P z width r banks src tab dst owners ev)
    snap[ev,entry] (v.payloadStage_format P z width r banks src tab dst owners phase trial entry fitted)
    (v.payloadStage_ballot P z width r banks src tab dst owners phase trial entry fitted)
    (v.payloadStage_memory P z width r banks src tab dst owners phase trial entry fitted)

end Payload

section Purchased
variable (phase trial slice inner : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.inner phase trial slice inner
local notation "sh" => ((bs).outer phase trial).market.shelf
local notation "key₀" => (bs).stratumHeader phase trial
local notation "surface" => ({(bs).inner phase trial slice inner with market:={((bs).inner phase trial slice inner).market with
  sampler:=(bs).sampler,depth:=v.depth}})
local notation "menu" => purchasedMenu F v.depth k (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos
  ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum
local notation "raw" => (surface).build (purchasedFormat F z (2^v.W) k _ v.depth key₀ sh (bs).sampler
  (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum) stock[ev]
local notation "slots" => (purchasedChannels (z:=z) (d:=2^v.W) (k:=k) sh (bs).sampler v.depth key₀).slot

abbrev purchasedStageSizes := StripSizes raw slots ((bs).inner phase trial slice inner).start D (Fintype.card (menu).index)
  (PacketWidths.ofMenu menu).maximum snap[ev,entry]
local notation "Sizes" => v.purchasedStageSizes P z width r banks src tab dst owners phase trial slice inner entry

def purchasedStageInput (fitted : Sizes) :=
  StripInput.of_purchased (F:=F) (z:=z) (d:=2^v.W) (k:=k) («D»:=D) v.depth key₀ sh (bs).sampler (bs).positive (bs).radius (bs).radius_nonneg
    (bs).tolerance (bs).tolerance_pos ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum surface stock[ev] ((bs).inner phase trial slice inner).start snap[ev,entry] fitted

local notation "actual[" f "]" => v.purchasedStageInput P z width r banks src tab dst owners phase trial slice inner entry f

omit [Nonempty (Fin k)] in
theorem purchasedStage_format (fitted : Sizes) : (actual[fitted]).form=v.nativeFormats P z width ev := rfl

omit [Nonempty (Fin k)] in
theorem purchasedStage_ballot (fitted : Sizes) :
    (actual[fitted]).ballot=v.ballot P z width r banks src tab dst owners ev := rfl

omit [Nonempty (Fin k)] in
theorem purchasedStage_memory (fitted : Sizes) : (actual[fitted]).mem=snap[ev,entry] := by
  simp only [purchasedStageInput, StripInput.of_purchased, StripInput.ofBoard]

def purchasedStage_compile (fitted : Sizes) :
    PortPlan (v.taskCommit P z width ev) (v.ballot P z width r banks src tab dst owners ev)
      snap[ev,entry] (v.nativeFormats P z width ev).market.rows :=
  (actual[fitted]).alignedPlan (v.nativeFormats P z width ev) (v.ballot P z width r banks src tab dst owners ev)
    snap[ev,entry] (v.purchasedStage_format P z width r banks src tab dst owners phase trial slice inner entry fitted)
    (v.purchasedStage_ballot P z width r banks src tab dst owners phase trial slice inner entry fitted)
    (v.purchasedStage_memory P z width r banks src tab dst owners phase trial slice inner entry fitted)

end Purchased

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
