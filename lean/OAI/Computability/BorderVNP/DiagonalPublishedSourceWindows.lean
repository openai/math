import OAI.Computability.BorderVNP.DiagonalSignedSourceWindows
import OAI.Computability.BorderVNP.DiagonalSelectedScheduleCounts
import OAI.Computability.BorderVNP.DiagonalSignedScheduleWords

/-! # The uniform phase windows on the actual signed publication and arena -/

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
/-- The real four published size words, selected cube address space, and the
physical packet and reader charges put all five signed phases within their
uniform budgets. The history, cell descriptions and actual route image are
chosen only after the length threshold. -/
theorem JointSchedule.eventually_published_source_windows (b : JointSchedule s (E+1) d Q A B j)
    (degree fixed emitted H : ℕ) (exponent : E+2≤degree) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let w := b.physical.word n
      let ξ := (s.τ:ℝ)/5
      let X := exterior ξ r n
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
        let dir := ExternalSew.freeDirectory (b.physical.teamsPred n) r (literal s.α n) (b.physical.link n)
          V (blockWidth (r*n) V) J desc
        let sizes := selectedSizes base (Cube.alphabet s.α n) (R*X) cells cables dir.candidates R r n reserve
        let ar := sizes.selected cube.pred cube.b cube.h cube.copies cube.width
        ∀ pp lp, ∀ (frame saved axis words core powers rectangle reader : ℕ) (after : ℕ → ℕ),
          let rows := dir.directory pp lp
          let l := LabelIndex.layout frame after
          let g := weightLayout ar frame axis
          let t := teamLayout ar (b.physical.teamsPred n)
          let h := ar.header.decoder saved
          let geo := GeometryAdviceRate.ticks k reserve outputs field w
          let costs := phaseCharges core geo fixed R V J cells J (descriptorTicks l after (ar.alphabet-1) a g t)
            (declarationTicks h cube.pred bitWidth) cables (ar.alphabet^2+X+1) emitted H w words powers X rectangle reader
          ar.stop < 2^w → l.cells=ar.cells → l.cableCount=ar.cables → l.deliveryCount=rows.length → l.labels=ar.alphabet →
          (w+1)*words≤⌈P⌉₊ → outputs≤⌈P⌉₊ → (geo:ℝ)≤P → cells≤outputs → J≤outputs →
          powers≤r*logWidth r n → rectangle+reader≤r →
          core≤2048*(X+(R+1)^3+(rows.length+ar.header.d.choose 2)+r+1) →
          costs.core≤windows.core ∧ costs.before≤windows.before ∧ costs.argumentsCalls≤windows.argumentsCalls ∧
            costs.finish≤windows.finish ∧ costs.reader≤windows.reader := by
  let bits := Tally.selectorWidth cube.pred cube.copies cube.h
  have paid := b.eventually_signed_source_windows degree bits (signedRowConstant D) fixed emitted H exponent
  filter_upwards [b.eventually_signed_schedule_counts,b.eventually_cube_primitives cube,b.eventually_lengths 0,paid]
    with n counts primitive sizes₀ run
  intro r R w ξ X a bitWidth start V T cells cables J P windows desc base reserve k outputs field dir sizes ar
    pp lp frame saved axis words core powers rectangle reader after rows l g t h geo costs room
    nativeCells nativeCables nativeDeliveries nativeLabels wordCost outputCost geometry capCells capJ
    paidPowers paidReader paidRoute
  let Z := Routing.labelCount a s.α n
  obtain ⟨_,_,_,_,_,jCap,nTeams,all⟩ := counts
  have labels : l.labels=Z := nativeLabels
  have symbols : 2 ≤ ar.header.d := (show 2 ≤ R from (Nat.le_succ 2).trans sizes₀.teams.1).trans nTeams
  have sys : 1 ≤ Z := Nat.one_le_pow _ _ (show 1 ≤ ar.header.d from by omega)
  have included : g.groups≤l.labels := by
    rw [nativeLabels]
    change ar.header.d ≤ ar.header.d^a
    exact Nat.le_self_pow (by change cube.pred+1≠0; omega) _
  have decoder := PackedHistoryCircuit.signed_decoder_widths ar saved symbols primitive.2.2.2.2.2.1 rfl room
  have total := (all desc).2 pp lp
  have actual := run words k reserve outputs field J cells J core powers rectangle reader l after g t h
    (by rw [nativeCells,nativeCables,nativeDeliveries]; exact total) labels sys nativeCells.symm rfl nTeams included
    rfl rfl decoder.1 decoder.2 wordCost outputCost geometry jCap capCells capJ paidPowers paidReader
    (by rw [nativeDeliveries]; exact paidRoute)
  rw [nativeCables] at actual
  exact actual

end Diagonal

end BorderVNP
end Computability
end OAI
