import OAI.ThreeFlat.RAM.HistoryStageChartAddresses
import OAI.ThreeFlat.Diagonal.ShrinkChildAssemblyOrder

namespace OAI
/-! # Numerical pin relocation for the literal shrink word step -/

namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.Compression CompressorPacking PhysicalShrink HistoryContraction RAM.HistoryStageShapeWires
open scoped Classical
noncomputable section
variable {F Pins : Type} [Field F]

/-- Tests the generated wires at the actual target site on every input word layout. -/
def Move.AssemblerWires {d l D m : ℕ} {A : State d l} {R : Move F A D m} (J : R.Assembler Pins) : Prop :=
  ∀ L i v,At L.ports (J L i).stage (Move.WordStep.targetSite (R:=R) (i:=i) v) ((J L i).words.ext v)

theorem wires_degree {d l D D' m : ℕ} {A : State d l} (e : D=D') (R : Move F A D m)
    (J : R.Assembler Pins) (h : Move.AssemblerWires J) : Move.AssemblerWires (Move.castAssembler e R J) := by
  cases e; exact h

theorem wires_lanes {d l l' D m : ℕ} (e : l=l') (A : State d l)
    (R : Move F (e ▸ A : State d l') D m) (J : R.Assembler Pins) (h : Move.AssemblerWires J) :
    Move.AssemblerWires (Move.inputAssembler e A R J) := by cases e; exact h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
theorem shrinkMove_wordWires {d lanes rem h t D : ℕ} (T : ShrinkMotif.Table F)
    (A : State d lanes) (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord h × BitWord t × BitWord rem)
    (P : PackingData A.Base (BitWord h) (BitWord t) (BitWord rem) d (2*d+1))
    (agree : StageAddress.packedGraph P=changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset) (hd : 0<d) (hD : 0<D)
    (small : ((2^(2*d+1)*d*d:ℕ):ℝ)/D≤1/1024) (tagSize : 1<2^t)
    (code : Arc A.Base (BitWord h) (BitWord t) (BitWord rem) d (2*d+1) ↪ ℕ)
    (order : ShrinkEdge P (parallel (2*d+1) d D) ↪ ℕ) :
    Move.AssemblerWires (Pins:=Pins) (shrinkMove_assembler T A u P agree good hd hD small tagSize code order) := by
  unfold shrinkMove_assembler
  apply wires_degree
  intro layout i v
  dsimp only [Move.WordStep.targetSite, id]
  apply At.onStage (I := StageAddress.shrinkInputIso A.graph A.chart u P agree A.width)
    (L := layout) (t := i) (v := v)
  unfold shrinkAssembly
  apply wordsStage_at

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
theorem shrinkBinary_wordWires (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*2^s+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem)) :
    Move.AssemblerWires (Pins:=Pins) (shrinkBinary_assembler T s D rem hD small A) := by
  unfold shrinkBinary_assembler
  apply wires_lanes
  unfold shrinkRaw_assembler
  apply shrinkMove_wordWires


end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.NavigationPass
open PhysicalStage HistoryContraction Computability.VPVNP.BurstRAM PrivateRAM RAM.HistoryStageShapeWires

theorem ShrinkWordVisit.wires {F Pins : Type} [Field F] {allow : StaticMotif F→Prop} {W K headerEnd heapEnd : ℕ} {cur ctr : Word W}
    {final : Memory W} {d l D m : ℕ} {A : State d l} {R : Move F A D m}
    {b : Fin R.rules.count} {L : A.Words Pins} {step : R.WordStep Pins L b}
    {old : A.ArchiveSites} {charge : (R.next b).Site→ℕ} {row : R.ArchiveStep b old charge}
    (issued : ShrinkWordVisit K cur ctr headerEnd heapEnd final allow R b L step old charge row) (v : (R.next b).Site) :
    At L.ports step.stage (Move.WordStep.targetSite (R:=R) (i:=b) v) (step.words.ext v) := by
  cases issued
  apply shrinkBinary_wordWires


end ThreeFlat.Diagonal.NavigationPass

end OAI
