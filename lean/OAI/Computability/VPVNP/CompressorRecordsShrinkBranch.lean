import OAI.Computability.VPVNP.CompressorRecordsChosenGeometry
import OAI.Computability.VPVNP.CompressorShrinkBundleAbsolute
import OAI.Computability.VPVNP.CompressorShrinkBundleFrame
import OAI.Computability.VPVNP.CompressorRecordsShrinkSelectedInputs

/-!
# The ordered shrinking branch through the selected geometry

Starting from an old represented wire graph and unused workspace, generate the
greedy geometry, sort and split the demand bundles, and transpose their old arc IDs.
The deterministic prefix is independent of the forthcoming term stream. At the
following worker the legal tapes are in bijection with the original shrinking
choices. On each such choice, use its output words to build the selected role and
preimage directories while retaining the dense absolute-ID table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkBranch

open Compression BurstRAM ShrinkMotif
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {a g w : ℕ} (X : State a (packingLaneBits a g)) (T : IncidenceDirectory w)
variable (start : ℕ) (stride selectors : Word w) (cap : ℕ)

local notation "Z" => ShrinkInput.plan X start
local notation "dense" => ShrinkInput.demandHead (w := w) X start
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "oldPub" => ShrinkInput.placementBank X T start
local notation "absHead" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X start) w

/-- Numerical bounds of the deterministic input scans and the admitted-term worker. -/
structure PrefixFits : Prop where
  before : ∀ c : Fin 6, (T.column c).val+DemandRAM.oldCount X ≤ start
  wide : 10 ≤ stride.val
  termRoom : ShrinkInput.termEnd X start stride.val < 2^w
  widthRoom : (Z).Q*X.maxWireWidth < 2^w
  termWords : ShrinkTermSelection.fitConstant B.shrink+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w
  gatherClock : ShrinkDemandGather.cost < cap
  termClock : TermWorker.budget B.shrink 2 8 w X.maxWireWidth ≤ cap

/-- Actual chronological reports before the first nondeterministic shrinking call. -/
structure Prefix (m : Memory w) where
  /-- The deterministic shrinking-input run that produces the sorted AB and CD width data. -/
  input : ShrinkInput.Run X T start m
  /-- Reports of writing the absolute old arc identifiers into the bundle directory before term
  selection. -/
  absolute : List (Report w)
  /-- Reports of gathering the demand data into dense motif rows for the term chooser. -/
  gather : List (Report w)
  absoluteRun : ShrinkBundlePlan.AbsoluteRun input absolute
  gatherRun : ShrinkDemandGather.Gathered (ShrinkTermSelection.bundles X) (ShrinkTermSelection.ranks a)
    (ShrinkInput.pairBank X T start) cap (after input.post (eventLog absolute)) gather

namespace Prefix

variable {X T start cap} {m : Memory w}

/-- The memory at entry to the term chooser, after input construction, absolute arc indexing,
and demand gathering. -/
def beforeTerm (p : Prefix X T start cap m) := after (after p.input.post (eventLog p.absolute)) (eventLog p.gather)
/-- All reports before the first term choice, in the order of input preparation, absolute arc
indexing, and demand gathering. -/
def reports (p : Prefix X T start cap m) := (p.input.reports++p.absolute)++p.gather

theorem replay (p : Prefix X T start cap m) : after m (eventLog p.reports) = p.beforeTerm := by
  rw [reports,eventLog,List.flatMap_append,List.flatMap_append,after,List.foldl_append,List.foldl_append]
  change after (after (after m (eventLog p.input.reports)) (eventLog p.absolute)) (eventLog p.gather) = _
  rw [p.input.post_reports]; rfl

end Prefix

/-- Fixed chronological term and chosen-geometry runs for a specified shrinking choice. -/
structure Selected (m : Memory w) (p : Prefix X T start cap m) (s : SelectedScore.Selection B X) where
  /-- Reports of the term-selection calls for the specified motif choices. -/
  terms : List (Report w)
  /-- The native construction of the layout, role records, and child directory determined by
  those choices. -/
  geometry : ChosenGeometry.Construction w
  termRun : ShrinkTermSelection.Written B.shrink X dense term stride.val cap s p.beforeTerm terms
  postTerm : ChosenGeometry.Run B X term stride selectors oldPub T s p.beforeTerm terms geometry
  absoluteDirectory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber absHead
    (geometry.final (after p.beforeTerm (eventLog terms)))
  lowerFrame : ∀ j, j<ShrinkInput.stop X start →
    geometry.final (after p.beforeTerm (eventLog terms)) j = after p.input.post (eventLog p.absolute) j

namespace Selected

variable {B X T start stride selectors cap} {m : Memory w} {p : Prefix X T start cap m}
variable {s : SelectedScore.Selection B X} (v : Selected B X T start stride selectors cap m p s)

/-- The memory supplied to the output sweep after the term rows and their chosen geometry have
been written. -/
def beforeOutput := v.geometry.final (after p.beforeTerm (eventLog v.terms))
/-- The selected branch's term reports followed by the reports of its geometry construction. -/
def reports := v.terms ++ v.geometry.reports

theorem replay : after p.beforeTerm (eventLog v.reports) = v.beforeOutput := by
  rw [reports,eventLog,List.flatMap_append,after,List.foldl_append]
  exact v.geometry.replay _

end Selected

set_option maxHeartbeats 1200000 in
/-- The same deterministic prefix serves every later shrinking choice. Legal tapes
at its exit are exactly the admitted choices in compact motif order. -/
theorem build (m : Memory w) (old : T.Represents X m)
    (hp : PrefixFits B X T start stride cap) (selectorsFit : selectors.val = B.shrink.selectorBits)
    (weightsFit : ∀ t, MotifAdmission.weight relativeMass t < 2^w)
    (geometryFit : SelectedFinish.stop X term stride ≤ 2^w) :
    ∃ p : Prefix X T start cap m,
      (∀ bs : Fin (ShrinkTermInputs.motifCount X) → List Bool,
        (runSegment (ShrinkTermSelection.termProgram B.shrink dense term stride.val) cap (some 0)
          p.beforeTerm (List.ofFn bs)).isSome ↔
          ∃! s : X.ShrinkSelection B.shrink, bs = ShrinkTermSelection.tapes B.shrink X s w) ∧
      ∀ s : SelectedScore.Selection B X,
        (∀ l, layoutScore relativeMass (X.packingData.termWidths B.shrink X.shrinkNumber X.packingWidth s) l < 2^w) →
        Nonempty (Selected B X T start stride selectors cap m p s) := by
  have hstop : ShrinkInput.stop X start < 2^w := by
    have h := hp.termRoom
    unfold ShrinkInput.termEnd at h
    omega
  have hrank : (Z).stop < 2^w := by
    change ShrinkInput.widthBase X start < 2^w
    unfold ShrinkInput.stop at hstop
    omega
  obtain ⟨r⟩ := ShrinkInput.build X T start m old hp.before hstop hp.widthRoom
  obtain ⟨ars,ha⟩ := ShrinkBundlePlan.run_absolute r hrank
  let absMem := after r.post (eventLog ars)
  have retained := r.keepAbsoluteFrame hstop ha.frame
  obtain ⟨gs,hg,legal,full⟩ := ShrinkInput.gather_select_from X T start B.shrink absMem retained.stored
    stride.val hp.wide hp.termRoom hp.termWords cap hp.gatherClock hp.termClock
  let p : Prefix X T start cap m := ⟨r,ars,gs,ha,hg⟩
  refine ⟨p,legal,?_⟩
  intro s score
  obtain ⟨ts,hw,_,frame⟩ := full s
  have ht := r.keepAbsoluteThenTerms ha.frame stride.val hp.termRoom frame
  obtain ⟨inputs,hI,hW⟩ := r.termInputs stride hp.termRoom
  obtain ⟨geom,hgeom⟩ := ChosenGeometry.build B X dense term stride selectors oldPub T cap s
    p.beforeTerm ts (r.bankParams hstop) hw ht.directory ht.incidence.actual inputs hI hW hp.wide geometryFit
    weightsFit selectorsFit score
  have hterm : ShrinkInput.stop X start ≤ (term).val := by
    have h := hp.termRoom
    unfold ShrinkInput.termEnd at h
    change _ ≤ (_ + _ : ℕ) % 2^w
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hlower (j : ℕ) (hj : j<ShrinkInput.stop X start) :
      geom.final (after p.beforeTerm (eventLog ts)) j = absMem j := by
    have hframe := hgeom.geometry.frame j (.inl (hj.trans_le (hterm.trans (Nat.le_add_right ..))))
    exact hframe.trans (frame j hj)
  exact ⟨⟨ts,geom,hw,hgeom,ShrinkBundlePlan.AbsoluteRun.directory_after r ha hlower,hlower⟩⟩

end CompressorRecords.ShrinkBranch

end VPVNP
end Computability
end OAI
