import OAI.Hierarchy.ProbeFixedEarnedStamp
import OAI.Hierarchy.ProbeFixedBoughtFlagRead
import OAI.Hierarchy.ProbeFixedWidePaidRows
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueSupport

namespace OAI
/-! # The parent purchase word at an elected inner ballot's own DFS ordinal -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe PurchaseFrozen
open CatalogueRows BoughtSockets StripChart StripDirectory StockCommit StockBound CatalystArchive
open scoped Fin.CommRing Classical

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (h width : ℕ)
local notation "D" => 2^v.W
local notation "W" => wordBits h D copies
local notation "N" => Stages h D

section
variable (P : v.Placement) (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "C" => v.nativeChart P h width r banks src tab dst owners
local notation "A" => v.privateArena P h width
local notation "B" => v.nativeBoards P h width
local notation "f" => v.nativeFormats P h width
variable (π : Equiv.Perm (Fin (2^h))) (m out : Memory (Native.wordBits h (2^v.W) Native.copies))
    (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
local notation "day" => finProdFinEquiv (phase,trial)
local notation "a" => Attempt.outer phase.val trial.val
local notation "days" => v.birthMarks P h width r banks src tab dst owners m
local notation "mark" => v.frozenMarket P h width phase.val trial.val
local notation "frozen" => v.frozenInput P h width r banks src tab dst owners m phase.val trial.val
local notation "keys" => stratumHeader h D k v.sampler.degree v.depth ((B).stratumHeader phase trial)
local notation "co" => checkedOut (w := W) C ((A).endAddress v.mesh) m
local notation "origin" => StripChart.build F B a 0

/-- The original, mode-gated catalogue of this particular day is equivalent
to the positive words in that day's physical checkout bank. Its equivalence
preserves the packed DFS ordinal, including multiple live chains in one tile. -/
theorem chain_parent_flag (whole : Calendar.mounted (w := W) C (events v.mesh) m)
    (archive : ArchiveRoom (w := W) C m (v.mesh.inject+v.mesh.cool)) (geometry : Shelf.Geometry (d := D) π m)
    (heap : heapEnd h D copies≤(A).first) (keyLow : (keys).stop≤(A).first) (keyData : (keys).Loaded m)
    (same : ∀x,x<(A).endAddress v.mesh→ out x=co x)
    (path : LiveChains v.sampler π v.depth (days day)) :
    out ((origin).board.purchaseOut+(BoughtLocation.relative path).val)≠0 := by
  let mode:=observedMode C m phase trial
  let base:=(repair C a).purchaseOut
  obtain ⟨fixture,incoming,prepared,_⟩:=v.activation_parent P h width r banks src tab dst owners m π phase trial
    phase.isLt trial.isLt whole geometry heap keyLow keyData
  obtain ⟨small,flags⟩:=v.checkout_flags P h width r banks src tab dst owners m phase trial whole archive
  let E:=BoughtLocation.catalogueEquiv mode (mark).shelf v.sampler π v.depth (Nat.two_pow_pos _)
    (mark).phase (mark).temperature (mark).kind frozen fixture co base incoming prepared small flags
  have nativePath (x : LiveChains v.sampler π v.depth (Shelf.catalogueMarks (k:=k)
      mode (mark).shelf (mark).phase (mark).temperature (mark).kind frozen)) :
      co (base+(BoughtLocation.relative x).val)≠0 := by
    have real := BoughtSockets.catalogueEquiv_val mode (mark).shelf v.sampler π v.depth (Nat.two_pow_pos _)
      (mark).phase (mark).temperature (mark).kind frozen fixture co base incoming prepared small flags x
    change (E x).val=BoughtLocation.relative x at real
    have bit:=(E x).property
    change co (base+(E x).val.val)≠0 at bit
    rwa [real] at bit
  let marks := Shelf.catalogueMarks (k := k) mode (mark).shelf
    (mark).phase (mark).temperature (mark).kind frozen
  have atDay : days day = marks := by
    simp only [birthMarks, outerDates, Equiv.symm_apply_apply]; rfl
  let hasFlag (ms : StageAt h D → (Fin k × Bool) → Finset (Fin (2^h))) : Prop :=
    ∀ x : LiveChains v.sampler π v.depth ms, co (base+(BoughtLocation.relative x).val)≠0
  have packed : hasFlag (days day) := (congrArg hasFlag atDay).mpr nativePath
  have inside : base+(mark).rows≤(A).base v.mesh (.attempt a)+(A).stride :=
    (f a).chargeColumns.2.2.1.trans (v.attempt_room P h width a)
  have meshEq : (C).mesh = v.mesh := rfl
  have mountedAt : Calendar.mounted (w := W) C (events (C).mesh) m :=
    (congrArg (fun mesh : Mesh => Calendar.mounted (w := W) C (events mesh) m) meshEq).mpr whole
  have hp : phase.val < (C).mesh.inject + (C).mesh.cool :=
    (congrArg (fun mesh : Mesh => phase.val < mesh.inject + mesh.cool) meshEq).mpr phase.isLt
  have ht : trial.val < (C).mesh.outerFuel :=
    (congrArg (fun mesh : Mesh => trial.val < mesh.outerFuel) meshEq).mpr trial.isLt
  obtain ⟨_,slot⟩ := outer_slot C m phase trial hp ht mountedAt
  have member : Event.attempt a ∈ events (C).mesh := by rw [slot.events]; simp
  have occurs : Event.attempt a ∈ events v.mesh :=
    (congrArg (fun mesh : Mesh => Event.attempt a ∈ events mesh) meshEq).mp member
  have before : (BoughtLocation.relative path).val< (mark).rows:=(BoughtLocation.relative path).isLt
  change out (base+(BoughtLocation.relative path).val)≠0
  have word := same _ ((Nat.add_lt_add_left before _).trans_le (inside.trans ((A).within v.mesh _ occurs)))
  exact fun zero => packed path (word.symm.trans zero)

end

private theorem outer_checkout_rows (F : Type*) [Field F] {z d k jobs depth : ℕ}
    [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z d)) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
    (boards : StripChart.Boards z d k jobs depth) (phase trial : ℕ) :
    (StripChart.build F boards (.outer phase trial) 0).market.rows =
      PurchaseFrozen.count z d k * PurchaseFrozen.paths z boards.sampler.degree depth := rfl

section
variable [Nonempty (Fin k)]
local notation "P" => v.widePlacement h width
variable (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "C" => v.nativeChart P h width r banks src tab dst owners
local notation "f" => v.nativeFormats P h width
local notation "B" => v.nativeBoards P h width
local notation "H" => StripChart.header F B
local notation "candidateRows" => StripChart.candidate_count F v.mesh (v.privateArena P h width)
  (P).joint.initial B
variable (π : Equiv.Perm (Fin (2^h))) (m out : Memory (Native.wordBits h (2^v.W) Native.copies))
    (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (slice : Fin v.mesh.reserveSteps) (inner : Fin v.mesh.innerFuel)
local notation "ev" => Attempt.inner phase.val trial.val slice.val inner.val
local notation "old" => Attempt.outer phase.val trial.val
local notation "origin" => StripChart.build F B old 0
local notation "b" => v.ballot P h width r banks src tab dst owners ev
local notation "input" => v.stage P h width r banks src tab dst owners ev
variable (boot : CoreRoute.Seen (z := h) («W» := v.W) (v.wideOrder h width) v.radius
      (WideMemory.groups h v.W) (WideMemory.dir h v.W k v.wideJobs) (v.wideSources h width).2 v.depth π m)
    («public» : (v.publicHeader (v.widePlacement h width) h width).Resident m)
    (room : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh <
      2^(Native.wordBits h (2^v.W) Native.copies))
    (whole : Calendar.mounted (w := Native.wordBits h (2^v.W) Native.copies)
      (v.nativeChart (v.widePlacement h width) h width r banks src tab dst owners) (events v.mesh) m)
    (late : v.stripHeight≤h) (small : width≤2^h) (limit : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤h)
    (layout : TrialLayout (v.nativeChart (v.widePlacement h width) h width r banks src tab dst owners)
      (.inner phase.val trial.val slice.val inner.val)
      (v.nativeFormats (v.widePlacement h width) h width (.inner phase.val trial.val slice.val inner.val)).pricedArea
      (v.nativeFormats (v.widePlacement h width) h width (.inner phase.val trial.val slice.val inner.val)).stockSource
      (v.stamp (v.widePlacement h width) h width r banks src tab dst owners (.inner phase.val trial.val slice.val inner.val))
      v.keepLimit width ((v.privateArena (v.widePlacement h width) h width).base v.mesh
        (.attempt (.inner phase.val trial.val slice.val inner.val))))
    (archive : ArchiveRoom (w := Native.wordBits h (2^v.W) Native.copies)
      (v.nativeChart (v.widePlacement h width) h width r banks src tab dst owners) m (v.mesh.inject+v.mesh.cool))
    (same : ∀ x, x < (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh →
      out x = checkedOut (w := Native.wordBits h (2^v.W) Native.copies)
        (v.nativeChart (v.widePlacement h width) h width r banks src tab dst owners)
        ((v.privateArena (v.widePlacement h width) h width).endAddress v.mesh) m x)
include boot «public» room whole late small limit layout archive same

/-- At an elected inner candidate the original producer has published its
affirmative mode-gated purchase word on this very candidate. -/
theorem wide_elected_parent_word (row : Fin (f ev).market.rows)
    (hit : row∈StockCommit.liveRows (w := W) b (input (entryMemory (w := W) C m ev)) (f ev).market.rows) :
    out ((origin).board.purchaseOut+row.val)≠0 := by
  obtain ⟨path,atRow⟩:=v.wide_paid_paths h width r banks src tab dst owners π m phase trial slice inner
    boot «public» room whole late small limit layout archive row hit
  obtain ⟨geo,heap,keyLow,keyData⟩:=v.paid_initial_tables h width π m boot
  have actual:=v.chain_parent_flag h width P r banks src tab dst owners π m out phase trial
    whole archive geo heap keyLow keyData same path
  simpa only [atRow] using actual

/-- The physical retained-guard expression at the original role occurrence
reads the affirmative parent word, on any later processing tape preserving
the checkout prefix. -/
theorem wide_elected_retained (row : Fin (H ev).rows)
    (hit : Fin.cast (candidateRows ev).symm row ∈ StockCommit.liveRows (w := W) b (input (entryMemory (w := W) C m ev)) (f ev).market.rows)
    (field : Fin (H ev).ports) (loaded : (H ev).Loaded out) :
    (retainedAt F B ev).eval out ((v.roleOccurrence P h width ev row field).val:Word W)≠0 := by
  have fromCheckout := outer_checkout_rows F B phase.val trial.val
  have size : (origin).market.rows ≤ 2^W :=
    (congrArg (fun n : ℕ => n ≤ 2^W) (fromCheckout.trans (candidateRows old).symm)).mpr
      (v.market_rows_fit P h width late old)
  have before : row.val < (origin).market.rows :=
    (congrArg (fun n : ℕ => row.val < n) fromCheckout).mpr row.isLt
  have word := v.retained_parent_word P h width phase trial slice inner out row field loaded before size
  have paid := v.wide_elected_parent_word h width r banks src tab dst owners π m out phase trial slice inner
    boot «public» room whole late small limit layout archive same (Fin.cast (candidateRows ev).symm row) hit
  exact fun zero => paid (word.symm.trans zero)

end
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
