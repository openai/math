import OAI.Computability.BorderVNP.DiagonalPublishedSourceWindows
import OAI.Computability.BorderVNP.PackedTerminalSignedGridEmitterCost

/-! # Paying for the argument phase of the selected signed evaluator -/

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

open private logWidth_pos from OAI.Computability.BorderVNP.CellPrivateBudget

/-- The threshold precedes all substituted input bytes, public geometry
outputs and received rows. The actual emitter pays the two packet sections
and both control directories; the counted power positions can be any part
of one stretched batch. -/
theorem JointSchedule.eventually_published_argument_window (b : JointSchedule s (E+1) d Q A B j)
    (degree fixed emitted H : ℕ) (exponent : E+2≤degree) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
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
      ∀ desc base reserve gates field p q live controls,
        let dir := ExternalSew.freeDirectory (b.physical.teamsPred n) r (literal s.α n) (b.physical.link n)
          V (blockWidth (r*n) V) J desc
        let sizes := selectedSizes base (Cube.alphabet s.α n) (R*X) cells cables dir.candidates R r n reserve
        let ar := sizes.selected cube.pred cube.b cube.h cube.copies cube.width
        let outputs := PackedHistoryCircuit.TerminalCells.signedGridOutputCount cables cells J live controls (CellPacketGeometry.Total p q)
        ∀ pp lp frame axis powers (after : ℕ → ℕ),
          let rows := dir.directory pp lp
          let l := LabelIndex.layout frame after
          let g := weightLayout ar frame axis
          let t := teamLayout ar (b.physical.teamsPred n)
          ar.stop < 2^w → l.cells=ar.cells → l.cableCount=ar.cables → l.deliveryCount=rows.length → l.labels=ar.alphabet →
          1≤field → (GeometryAdviceRate.ticks gates reserve outputs field w : ℝ)≤P → powers≤r →
          fixed+argumentDirectory ar.cells J+32*descriptorTicks l after (ar.alphabet-1) a g t+
            (82*l.cableCount+emitted*(ar.alphabet^2+X+1))+cellWork w (2^p+2^q) powers X ≤ windows.argumentsCalls := by
  filter_upwards [b.eventually_published_source_windows cube degree fixed emitted H exponent,
    b.eventually_word_capacity 1 1,eventually_ge_atTop 1] with n windowsAt word npos
  intro r R w X a bitWidth start V T cells cables J P windows desc base reserve gates field p q live controls
    dir sizes ar outputs pp lp frame axis powers after rows l g t room cellCount cableCount deliveryCount labels
    fieldPos geometry powerCap
  have logPos := logWidth_pos npos (stretch_one b.ρ n)
  have wPos : 1≤w := logPos.trans word.1
  have measured := signed_emitted_and_report_words (reportWords:=0) wPos fieldPos (by simp) geometry
  have words : (w+1)*(2^p+2^q)≤⌈P⌉₊ := by simpa using measured.1
  have cellsOut : cells≤outputs := by unfold outputs PackedHistoryCircuit.TerminalCells.signedGridOutputCount; omega
  have originalsOut : J≤outputs := by unfold outputs PackedHistoryCircuit.TerminalCells.signedGridOutputCount; omega
  have powersFit := powerCap.trans (Nat.le_mul_of_pos_right r logPos)
  have bound := windowsAt desc base reserve gates outputs field pp lp frame 0 axis (2^p+2^q) 0 powers 0 0 after
    room cellCount cableCount deliveryCount labels words measured.2 geometry cellsOut originalsOut powersFit (by omega) (Nat.zero_le _)
  have result := bound.2.2.1
  change fixed+argumentDirectory cells J+32*descriptorTicks l after (ar.alphabet-1) a g t+
    (82*cables+emitted*(ar.alphabet^2+X+1))+cellWork w (2^p+2^q) powers X ≤ windows.argumentsCalls at result
  rw [cableCount]
  exact result

end Diagonal

end BorderVNP
end Computability
end OAI
