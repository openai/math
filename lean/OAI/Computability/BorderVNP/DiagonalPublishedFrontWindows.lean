import OAI.Computability.BorderVNP.DiagonalPublishedSourceWindows
import OAI.Computability.BorderVNP.RoutingISAScheduleClockFinitePrefix

/-! # The actual publication and route charges before the signed private calls -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing Cover Packing PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open TeamScales RoutingISA RoutingISA.Evaluator RoutingISA.LocalRow ScheduleClock _root_.OAI.Computability.BorderVNP.Cube CubeArena
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {extra E d Q A B j : ℕ} (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra}

set_option maxRecDepth 5000 in
/-- Reading the four actual published header words calibrates the entire native
schedule. Both windows are chosen before all pins, placements, routes and teams
at this length. They can be charged before any private call is made. -/
theorem JointSchedule.eventually_published_front_windows (b : JointSchedule s (E+1) d Q A B j)
    (degree fixed emitted H : ℕ) (exponent : E+2≤degree) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let teams := b.physical.teamsPred n
      let R := teams+1
      let w := b.physical.word n
      let X := exterior ((s.τ:ℝ)/5) r n
      let a := cube.pred+1
      let bitWidth := Tally.selectorWidth cube.pred cube.copies cube.h
      let start := CoverScale.initialDepth (Epoch.Cube D) r n
      let V := CoverScale.sites (Epoch.Cube D) start
      let T := epochs s.τ n
      let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start T)
      let cables := (boundary S start T).edges+4*(R*V)
      let J := (epochCopies S)^T*V
      let P := RoutingISA.Evaluator.publicWork a s.α r n R
      let windows := s.signedWindows degree (512*(a+bitWidth+1)) fixed emitted H n r
      ∀ (desc base reserve k outputs field : ℕ),
        let dir := ExternalSew.freeDirectory teams r (literal s.α n) (b.physical.link n) V (blockWidth (r*n) V) J desc
        let sizes := selectedSizes base (Cube.alphabet s.α n) (R*X) cells cables dir.candidates R r n reserve
        let ar := sizes.selected cube.pred cube.b cube.h cube.copies cube.width
        ∀ pp lp, ∀ (frame saved axis : ℕ) (after : ℕ → ℕ),
          let rows := dir.directory pp lp
          let tab := ar.table frame (rows.length+ar.header.d.choose 2)
          let l := LabelIndex.layout frame after
          let geo := GeometryAdviceRate.ticks k reserve outputs field w
          ar.stop < 2^w → l.cells=ar.cells → l.cableCount=ar.cables → l.deliveryCount=rows.length → l.labels=ar.alphabet →
          outputs≤⌈P⌉₊ → (geo:ℝ)≤P → cells≤outputs → J≤outputs →
          2048*(X+(R+1)^3+tab.count+r+1)≤windows.core ∧
            geo+beforeDirectory R V dir.entries+rawScheduleTicks ar frame saved axis teams rows.length after≤windows.before := by
  filter_upwards [b.eventually_published_source_windows cube degree fixed emitted H exponent] with n paid
  intro r teams R w X a bitWidth start V T cells cables J P windows desc base reserve k outputs field dir sizes ar
    pp lp frame saved axis after rows tab l geo room nativeCells nativeCables nativeDeliveries nativeLabels out geometry
    capCells capJ
  let core := 2048*(X+(R+1)^3+tab.count+r+1)
  obtain ⟨coreBound,beforeBound,_⟩ := paid desc base reserve k outputs field pp lp frame saved axis 0 core 0 0 0 after
    room nativeCells nativeCables nativeDeliveries nativeLabels (by simp) out geometry capCells capJ
    (Nat.zero_le _) (Nat.zero_le _) (Nat.le_refl _)
  have scheduled := rawScheduleTicks_eq ar frame saved axis teams rows.length after nativeCells nativeLabels nativeDeliveries rfl
  rw [scheduled]
  refine ⟨coreBound,?_⟩
  change geo+beforeDirectory R V dir.entries+
    (descriptorTicks l after (l.labels-1) a (weightLayout ar frame axis) (teamLayout ar teams)+
      declarationTicks (ar.header.decoder saved) cube.pred bitWidth)≤windows.before
  rw [nativeLabels,←Nat.add_assoc]
  exact beforeBound

end Diagonal

end BorderVNP
end Computability
end OAI
