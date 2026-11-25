import OAI.Computability.MultitapeWeakETH.HistoryChildBank

/-! # A retained branch of the sparse formula's native descriptor computation -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP BurstRAM Compression CompressorRecords DescriptorSpace
open PairSimulation LocalHistory TraversalRows TraversalRoles NetworkKernel DyadicBudget
open scoped Classical Fin.CommRing
noncomputable section

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)

abbrev gridIndex (volume : Tally) := index (4*stepSize B) volume.length
abbrev gridWidth (volume : Tally) := CursorBounds.wordBits 1 (scale B (gridIndex B volume))
abbrev gridExecution (volume : Tally) := B.execute f hf (gridIndex B volume) (lanes_fit B _) (source B (gridIndex B volume))

set_option allowUnsafeReducibility true in
attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale entryMemory executeLevels
  BlockSchedule.Templates.execute CompiledResident.resident
set_option maxHeartbeats 1000000

def Recorded (volume : Tally) (path : (gridExecution B f hf volume).Choices) (log : CallProgram.Stores (gridWidth B volume)) : Prop :=
    let s := gridIndex B volume
    let X := source B s
    let w := gridWidth B volume
    let u := stepSize B*s
    let initial : TaggedLayer := ⟨leafLayer (siteOrder X),.cursor⟩
    let base := entryMemory B (3*u) u (scale B s) s w
    let past := executeLevels B f hf s (lanes_fit B s) X path
    CompiledResident.resident B f hf 0 X.positions s (scale B s) initial
      (Frame.data (k:=8) (BlockHeaderRun.header w (gridLayout B volume) 0+6) base) past
      ((gridExecution B f hf volume).finalState path) (memory base log)

/-- The branch and its chronological writes use the same initial grid memory. -/
def ResidentHistory := (v : Tally) × (p : (gridExecution B f hf v).Choices) ×
  {log : CallProgram.Stores (gridWidth B v) // Recorded B f hf v p log}

variable {B f hf} (H : ResidentHistory B f hf)

abbrev ResidentHistory.volume : Tally := H.1
abbrev ResidentHistory.path : (gridExecution B f hf H.volume).Choices := H.2.1
abbrev ResidentHistory.log : CallProgram.Stores (gridWidth B H.volume) := H.2.2.val
theorem ResidentHistory.stored : Recorded B f hf H.volume H.path H.log := H.2.2.property

def ResidentHistory.passes := executeLevels B f hf (gridIndex B H.volume) (lanes_fit B _)
  (source B (gridIndex B H.volume)) H.path

def ResidentHistory.point (i j : ℕ) : HistorySite := (((H.volume,writes H.log),tally i),tally j)

def ResidentHistory.Children (children : HistorySite × Bits.Word → Option ChildResult) : Prop :=
  ∀ i : Fin H.passes.length, let V := H.passes[i.val]
    ∀ (j : Fin (levelLayer B f hf V).count) bits ids bank tail,
      children (H.point i.val j.val,bits) = some ((ids,bank),tail) ↔
        ∃ h : Placed (V.pass.step.term V.term).place V.input.network.Half (outputSite V j),
          ids = ((levelLayer B f hf V).ids j).map tally ∧
          bank = NamedPackets.placedBank V.input _ _ (childOrder V j) h (gridWidth B H.volume) ∧ bits = bank.2.flatten ++ tail

theorem resident_children (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) :
    ∃ children : HistorySite × Bits.Word → Option ChildResult, Poly children ∧ ∀ H : ResidentHistory B f hf,
      max 1 (slotDegree S) ≤ gridIndex B H.volume → H.Children children := by
  obtain ⟨read,cost,correct⟩ := history_child_bank B f hf
  exact ⟨read,cost,fun H room => correct H.volume ((le_max_left ..).trans room) ((le_max_right ..).trans room)
    H.path H.log H.stored⟩

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
