import OAI.Computability.VPVNP.CompressorDetailedResident
import OAI.Computability.VPVNP.CompressorSelectedChildDirectory
import OAI.Computability.VPVNP.CompressorSelectedPayloadReadback
import OAI.Computability.VPVNP.CompressorRefreshPayloadHistory
import OAI.Computability.VPVNP.PairShrinkResidentHeaderWords
import OAI.Computability.VPVNP.PairShrinkResidentSources
import OAI.Computability.VPVNP.PairShrinkPhysicalSourceBounds

/-!
# Resident data from the two compiled compressor passes

The selected origin fixes the input state and the type of its choice.
A shrink stores its term, ranking and slot tables together with the
published party header words. A refresh stores its demand and term records,
input and output incidence, and traversal geometry. The chronological
level gives the addresses at which later site workers read these records.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.CompiledResident

open BurstRAM Compression DescriptorSpace PairSimulation PairSimulation.LocalHistory
open SelectedPayloadHistory
open scoped Fin.CommRing

variable {w : ℕ} {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)
variable (workspace : Word w) (positions blocks n : ℕ)
local notation "L" => BlockProgram.layout B workspace.val positions blocks

/-- The selected shrinking sources, address bounds and published headers. -/
structure ShrinkPayload (cur : ℕ) (i : Fin S.steps) {g : ℕ}
    (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
    (sel : SelectedScore.Selection B X) (m : Memory w) : Prop where
  bounds : ShrinkResidentSources.Bounds B i X workspace positions blocks cur
  sources : ShrinkResidentSources.Data B i X (S.shrink i) sel workspace positions blocks cur m
  words : ShrinkResidentHeaders.Words B i X sel workspace positions blocks cur n m
  child : SelectedChildDirectory.Stored B L cur n X m
  termRun : ∃ (dense : Word w) (fuel : ℕ) (before : Memory w) (reports : List (Report w)),
    ShrinkTermSelection.Written B.shrink X dense
    (ShrinkInput.termHead X (tableBase L cur (0 : Fin 6))) 10 fuel sel before reports

/-- The selected refresh sources and their readback bounds. The placement
publisher also records the DFS row stride for this chronological level. -/
structure RefreshPayload (cur : ℕ) {g : ℕ} (X : State S.portExponent (S.portExponent+g))
    (choice : Refresh.DyadicRefreshChoice (a₀ := S.degreeExponent 0) (g := g) X S.graph (Nat.two_pow_pos _)
      (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (m : Memory w) : Prop where
  live : cur+1 < (L).levels
  size : X.positions ≤ positions
  fit : endAddress L < 2^w
  sources : RefreshPayloadHistory.Data B L cur n X choice m
  child : SelectedChildDirectory.Stored B L cur n X m

private def shrinking : Shrinking (w := w) B f hf := by
  intro cur i g lanes h X sel _ m
  subst lanes
  exact ShrinkPayload B workspace positions blocks n cur i X sel m

private def refreshing : Refreshing (w := w) B :=
  fun cur {_} X choice _ m => RefreshPayload B workspace positions blocks n cur X choice m

/-- Select the native payload corresponding to the pass that was actually
executed and the term that its branch selected. -/
def payload : Data (w := w) B f hf :=
  byOrigin (shrinking B f hf workspace positions blocks n) (refreshing B workspace positions blocks n)

theorem shrink_payload (cur : ℕ) (i : Fin S.steps) {g : ℕ}
    (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
    (sel : SelectedScore.Selection B X) (bits : List Bool) (m : Memory w) :
    payload B f hf workspace positions blocks n cur ⟨_,_,_,_,X,_,.shrink i rfl X,sel,bits⟩ m ↔
      ShrinkPayload B workspace positions blocks n cur i X sel m := Iff.rfl

theorem refresh_payload (cur : ℕ) {g : ℕ} (X : State S.portExponent (S.portExponent+g))
    (choice : Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
      (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (bits : List Bool) (m : Memory w) :
    payload B f hf workspace positions blocks n cur ⟨_,_,_,_,X,_,.refresh X,choice,bits⟩ m ↔
      RefreshPayload B workspace positions blocks n cur X choice m := Iff.rfl

/-- The concrete boundary predicate for the compiled calendar. -/
abbrev resident (initial : TraversalRoles.TaggedLayer) (initialFrame : Fin 8 → Word w) :
    ScheduledTrace.Resident B f hf w :=
  DetailedResident.resident B f hf initial L (endAddress L) n initialFrame
    (payload B f hf workspace positions blocks n)

variable {B f hf workspace positions blocks n}

/-- All fields read by either kind of site parser transfer from its
producing memory on the region retained for this particular occurrence. -/
theorem payload_transfer {cur : ℕ} {v : SelectedLevel B f hf} {m out : Memory w}
    (h : payload B f hf workspace positions blocks n cur v m) (same : SourceTransport.Agree (Cells L cur) m out) :
    payload B f hf workspace positions blocks n cur v out := by
  obtain ⟨a,g,b,l,X,p,o,c,bits⟩ := v
  cases o with
  | shrink i eq X =>
    subst eq
    have d := (shrink_payload ..).mp h
    exact (shrink_payload ..).mpr ⟨d.bounds,d.sources.transfer d.bounds same,d.words.transfer same,
      d.child.transfer same,d.termRun⟩
  | refresh X =>
    have d := (refresh_payload ..).mp h
    exact (refresh_payload ..).mpr ⟨d.live,d.size,d.fit,d.sources.transfer rfl d.live d.size d.fit same,
      d.child.transfer same⟩

/-- Recover the concrete native sources directly in the current memory. -/
theorem read {past : List (SelectedLevel B f hf)} {m : Memory w}
    (h : Past B f hf L (payload B f hf workspace positions blocks n) past m) (i : Fin past.length) :
    payload B f hf workspace positions blocks n i.val past[i] m :=
  h.atLevel i (fun _ d same => payload_transfer d same)

/-- The child scan's operands are available for every selected pass. -/
theorem child_directory {cur : ℕ} {v : SelectedLevel B f hf} {m : Memory w}
    (h : payload B f hf workspace positions blocks n cur v m) :
    SelectedChildDirectory.Stored B L cur n v.input m := by
  obtain ⟨a,g,b,l,X,p,o,c,bits⟩ := v
  cases o with
  | shrink i eq X =>
    subst eq
    exact ((shrink_payload ..).mp h).child
  | refresh X => exact ((refresh_payload ..).mp h).child

/-- Every selected pass publishes the same DFS row stride. -/
theorem stride_word {cur : ℕ} {v : SelectedLevel B f hf} {m : Memory w}
    (h : payload B f hf workspace positions blocks n cur v m) :
    m (levelStart L cur+15) = ((B.recordLimit+2 : ℕ) : Word w) :=
  (child_directory h).stride

/-- The parser for a shrinking occurrence can read its successor's stride
from the actual selected history, including the shrink just before refresh. -/
theorem shrink_successor_stride {lanes : ℕ} {hT : blocks*S.laneBits ≤ lanes}
    {X : State (S.degreeExponent 0) lanes} {z : (B.execute f hf blocks hT X).Choices} {m : Memory w}
    (h : Past B f hf L (payload B f hf workspace positions blocks n) (executeLevels B f hf blocks hT X z) m)
    (i : Fin (executeLevels B f hf blocks hT X z).length)
    (shrink : (executeLevels B f hf blocks hT X z)[i].origin.ordinal < S.steps) :
    m (levelStart L (i.val+1)+15) = ((B.recordLimit+2 : ℕ) : Word w) :=
  SelectedPayloadHistory.shrink_successor_stride h i shrink
    (by change 15 < 66 + _ + _; omega) (fun _ _ published => stride_word published)

end CompressorRecords.CompiledResident

end

end VPVNP
end Computability
end OAI
