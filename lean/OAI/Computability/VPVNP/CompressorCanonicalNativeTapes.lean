import OAI.Computability.VPVNP.PairSimulationSelectorReindex
import OAI.Computability.VPVNP.CompressorShrinkTermOnline
import OAI.Computability.VPVNP.CompressorRefreshCorePackets

/-!
# Canonical tapes and the physical term packets

Shrinking orders motifs by their dense bundle and CD rank and orders each
layout's supply by role. Refresh uses the base vertex number followed by
the residual lane and the expander's port-major supply order. In these
coordinates the term tapes of both native passes are the canonical worker
tapes of their actual mathematical choices.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.CanonicalWorker

open BurstRAM Compression Compression.Refresh SelectedTerms PairSimulation.LocalHistory
open PortRefresh
open scoped Classical

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)

section Shrink

variable (i : Fin S.steps) {g : ℕ}
variable (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
variable (s : X.ShrinkSelection B.shrink) (w : ℕ)
local notation "o" => PassOrigin.shrink (B := B) (f := f) (hf := hf) i rfl X

/-- The two descriptions of the complete shrinking term tape agree at
each physical motif ordinal. -/
theorem shrink_tapes : ShrinkTermSelection.tapes B.shrink X s w = workerTapes o w s := by
  funext j
  rfl

theorem shrink_choices : ShrinkTermPackets.choices (w := w) B i X s .select =
    List.ofFn (workerTapes o w s) := congrArg List.ofFn (shrink_tapes B f hf i X s w)

/-- Read off the row-major choice tapes from the actual accepted native
shrinking term reports. -/
theorem shrink_branches (origin : PhaseRecipe.Expr) (T : IncidenceDirectory w) (start cap : ℕ)
    {m : Memory w} {rs : List (Report w)} (h : ShrinkTermPackets.PacketRun B i origin X T start s cap .select m rs) :
    branchPaths rs = List.ofFn (workerTapes o w s) :=
  h.branches.trans (shrink_choices B f hf i X s w)

/-- The occurrence of the shrinking selector in the global script carries
the entire canonical term tape as its scheduled choices. -/
theorem shrink_online_choices (T : IncidenceDirectory w) (start cap : ℕ) :
    (ShrinkTermOnline.globalVisit B i X T start s cap .select).choices = List.ofFn (workerTapes o w s) :=
  shrink_choices B f hf i X s w

end Shrink

section Refresh

variable {g : ℕ} (X : State S.portExponent (S.portExponent+g))
local notation "hd" => Nat.two_pow_pos S.expanderExponent
private abbrev connected := (S.port_bound.connected_and_pos S.port_order).1
local notation "hc" => connected (S := S)
local notation "o" => PassOrigin.refresh (B := B) (f := f) (hf := hf) X
variable (c : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (w : ℕ)

/-- The inverse physical block ordinal is the same base/lane order as
the refresh pass's term rows. -/
theorem refresh_blocks :
    (DemandScan.blocks X).symm =
      (Order.prod ⟨_,X.baseIndex.symm⟩ ⟨_,(bitWordFinEquiv g).symm⟩).entries := rfl

/-- The full native refresh tape, including every supply coordinate, is
the canonical worker tape of the same choice. -/
theorem refresh_tapes : blockTapes S.graph hd hc B.refresh X c w = workerTapes o w c := by
  funext j
  rfl

theorem refresh_choices (start : ℕ) :
    Scheduled.tapes (w := w) (t := (RefreshBlockPlan.shape B).ties) X S.graph hd hc B.refresh c start
      (RefreshBlockPlan.shape B).stride .term = List.ofFn (workerTapes o w c) :=
  congrArg List.ofFn (refresh_tapes B f hf X c w)

/-- In an executed refresh term stage the genuine branch bits are exactly
the selected canonical stream, in the same order. -/
theorem refresh_branches (old : IncidenceDirectory w) (start cap : ℕ) {m : Memory w} {rs : List (Report w)}
    (h : Scheduled.Source X S.graph hd hc B.refresh S.degree_bounds.2 c (RefreshBlockPlan.order B) old
      start (RefreshBlockPlan.shape B).stride cap .term m rs) :
    branchPaths rs = List.ofFn (workerTapes o w c) :=
  ((runSegment_iff ..).mp h).2.2.trans (refresh_choices B f hf X c w start)

open private refreshStages from OAI.Computability.VPVNP.CompressorBlockIndex

/-- The refresh selector follows the gather, bundle and offset scans and
all the tie-demand scans. -/
def refreshTermIndex : Fin (RefreshCore.stages B).length := (refreshStages B).index

theorem refreshTermIndex_val : (refreshTermIndex B).val = 3+(RefreshBlockPlan.shape B).ties := by
  simp only [refreshTermIndex,BlockIndex.Focus.index,refreshStages,List.length_append,List.length_cons,
    List.length_nil,List.length_map,List.length_finRange]

theorem refreshTermIndex_stage : (RefreshCore.stages B)[(refreshTermIndex B).val] = .term :=
  (refreshStages B).lookup

set_option maxHeartbeats 900000 in
/-- The native refresh occurrence is the actual term stage of the live
script; its scheduled choice lists agree with the mathematical worker
tapes at every port-block ordinal. -/
theorem refresh_online_choices (old : IncidenceDirectory w) (start cap : ℕ) :
    (RefreshCore.visit B X c old start cap (refreshTermIndex B)).choices = List.ofFn (workerTapes o w c) := by
  simp only [RefreshCore.visit,SourceOnline.Visit.ofWorker,refreshTermIndex_stage]
  exact refresh_choices B f hf X c w start

end Refresh

end CompressorRecords.CanonicalWorker

end

end VPVNP
end Computability
end OAI
