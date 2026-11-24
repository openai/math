import OAI.Computability.VPVNP.CompressorRecordsShrinkBranch
import OAI.Computability.VPVNP.CompressorShrinkSelectedOutput

/-!
# A shrinking pass on the represented RAM wire graph

The deterministic prefix ends at the actual term-chooser entry. Every admissible
term stream induces one chosen layout, its role and child lists, and a subsequent
width and slot construction. The last memory represents the precise next
compression state on the same branch. The computation retains the immediate
old-site preimages used by the backward history evaluator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkBranch

open Compression BurstRAM ShrinkMotif
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {a b g w : ℕ} {δ : ℝ} (X : State a (packingLaneBits a g))
variable (ready : ShrinkMotif.Ready (2^a) (Shrink.colors a) (2^b) δ)
variable (T : IncidenceDirectory w) (start : ℕ) (stride selectors : Word w) (cap : ℕ)

local notation "Z" => ShrinkInput.plan X start
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "dense" => ShrinkInput.demandHead (w := w) X start
local notation "bank" => ShrinkInput.placementBank X T start
local notation "ids" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X start) w
local notation "keepEnd" => SelectedFinish.stop X (ShrinkInput.termHead (w := w) X start) stride
local notation "role" => SelectedArena.roleBase X (ShrinkInput.termHead (w := w) X start) stride

private theorem absolute_room (room : ShrinkInput.termEnd X start stride.val < 2^w) :
    (ids).val + ShrinkOutput.motifCount X ≤ keepEnd := by
  have h₀ : (ids).val ≤ (Z).gathered+(Z).B*(Z).Q := Nat.mod_le ..
  have hr : (Z).gathered + (Z).B*(Z).Q + (Z).B*(Z).Q = (Z).ranks := by
    change _ = (Z).gathered+(2*(Z).B)*(Z).Q
    ring
  have hc : ShrinkOutput.motifCount X = (Z).B*(Z).Q := rfl
  have h₁ : (Z).ranks ≤ ShrinkInput.stop X start := by
    change (Z).ranks ≤ (Z).ranks+(Z).A + _ + _
    omega
  have h₂ : ShrinkInput.stop X start ≤ (term).val := by
    unfold ShrinkInput.termEnd at room
    change _ ≤ (_+_ : ℕ) % 2^w
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have h₃ : (term).val ≤ keepEnd := by
    unfold SelectedFinish.stop SelectedFinish.rowStart SelectedFinish.countStart SelectedArena.endAddr
      SelectedArena.roleBase SelectedArena.placementBase SelectedArena.origin
    omega
  rw [hc]
  omega

/-- The stored outcomes of every native part of a full shrinking pass. -/
structure Complete (m : Memory w) (p : Prefix X T start cap m) (s : SelectedScore.Selection B X) where
  /-- The chosen term and geometry runs extending this deterministic shrinking prefix. -/
  selected : Selected B X T start stride selectors cap m p s
  /-- The native passes building the next state's widths and slot directory from the selected
  records. -/
  output : ShrinkOutput.Passes w
  outputRun : ShrinkOutput.Complete B X ready s term stride ids cap selected.beforeOutput output

namespace Complete

variable {B X ready T start stride selectors cap} {m : Memory w}
variable {p : Prefix X T start cap m} {s : SelectedScore.Selection B X}
variable (r : Complete B X ready T start stride selectors cap m p s)

/-- The complete branch trace in prefix, selected-term and geometry, then output order. -/
def reports := (p.reports ++ r.selected.reports) ++ r.output.reports

/-- The physical RAM memory after the entire branch is the post-memory of the slot construction. -/
theorem replay : after m (eventLog r.reports) = r.output.final := by
  rw [reports,eventLog,List.flatMap_append,List.flatMap_append,after,List.foldl_append,List.foldl_append]
  change after (after (after m (eventLog p.reports)) (eventLog r.selected.reports))
    (eventLog r.output.reports) = _
  rw [p.replay,r.selected.replay]
  exact r.outputRun.replay

end Complete

set_option maxHeartbeats 1200000 in
/-- Compile the actual wire-state transition for all admitted choices, in the same order
in which the fused term worker reads their canonical tapes. -/
theorem build_complete (m : Memory w) (old : T.Represents X m)
    (hp : PrefixFits B X T start stride cap) (selectorsFit : selectors.val = B.shrink.selectorBits)
    (weightsFit : ∀ t, MotifAdmission.weight relativeMass t < 2^w)
    (geometryFit : keepEnd ≤ 2^w)
    (outputFit : ShrinkOutput.FitsWords (b := b) X B.shrink term stride.val role keepEnd)
    (outputClock : ShrinkSliceSweep.SurvivingNative.ops.length < cap) :
    ∃ p : Prefix X T start cap m,
      (∀ bs : Fin (ShrinkTermInputs.motifCount X) → List Bool,
        (runSegment (ShrinkTermSelection.termProgram B.shrink dense term stride.val) cap (some 0)
          p.beforeTerm (List.ofFn bs)).isSome ↔
          ∃! s : X.ShrinkSelection B.shrink, bs = ShrinkTermSelection.tapes B.shrink X s w) ∧
      ∀ s : SelectedScore.Selection B X,
        (∀ l, layoutScore relativeMass (X.packingData.termWidths B.shrink X.shrinkNumber X.packingWidth s) l < 2^w) →
        Nonempty (Complete B X ready T start stride selectors cap m p s) := by
  obtain ⟨p,legal,make⟩ := build B X T start stride selectors cap m old hp selectorsFit weightsFit geometryFit
  refine ⟨p,legal,?_⟩
  intro s hs
  obtain ⟨r⟩ := make s hs
  let before := after p.beforeTerm (eventLog r.terms)
  obtain ⟨out,hout⟩ := ShrinkOutput.build_selected B X ready s term stride ids selectors bank before
    r.geometry.placed r.geometry.children r.postTerm.geometry hp.wide outputFit
    (absolute_room X start stride hp.termRoom) r.absoluteDirectory cap outputClock
  exact ⟨⟨r,out,hout⟩⟩

end CompressorRecords.ShrinkBranch

end VPVNP
end Computability
end OAI
