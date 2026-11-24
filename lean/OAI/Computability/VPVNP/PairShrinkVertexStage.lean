import OAI.Computability.VPVNP.PairShrinkHiddenSegment
import OAI.Computability.VPVNP.PairShrinkMapReload
import OAI.Computability.VPVNP.CompressorShrinkResidentLayout
import OAI.Computability.VPVNP.CompressionTemplates

/-!
# Child, absorbed-field, and map code in one shrinking stage

The old level determines the child degree and the fixed capacity of its absorbed-field
rows. After loading the hidden operands, the stage saves the actual hidden base in
locator register eight, for the subsequent map's supply-half reads.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkVertexStage

open BurstRAM BurstRAM.PrivateRAM VertexImage VertexStagePrefix CompressorRecords Compression
open scoped Fin.CommRing

variable {p r w : ℕ}

/-- Load the four hidden-field operands and cache the private field base for the map. -/
def prepare (s t : ℕ) (B : LocatedBody) :
    Preparation (ShrinkHiddenGuess.Table.segment s t) B.code where
  count := VertexLevel.hiddenCount + 1
  entry := 0
  row pc dfs _ phaseRegs bodyRegs next :=
    let locator := B.locator.trans bodyRegs
    let inputs := (ShrinkHiddenGuess.Table.segmentInputs s t).trans phaseRegs
    Fin.lastCases (.copy (locator 8) (inputs 1) next)
      (VertexLevel.hiddenHandoff (pc ∘ Fin.castSucc) locator inputs (dfs 6)
        (pc (Fin.last VertexLevel.hiddenCount)))

/-- Place the hidden-field preparation in front of the supplied located body and lift its
locator into the enlarged private register bank. -/
def withHidden (s t : ℕ) (B : LocatedBody) : LocatedBody where
  code := (prepare s t B).assemble
  locator := B.locator.trans (Fin.castAddEmb (ShrinkHiddenGuess.Table.segment s t).privateRegs)

/-- The selected stage reaches its map after scanning the child list and the hidden rows. -/
def stage (degreeExponent selectors : ℕ) (maps : LocatedBody) : LocatedBody :=
  (withHidden selectors (ShrinkResidentLayout.rowCapacity degreeExponent false)
    (ShrinkMapReload.body maps)).withChildren degreeExponent

/-- All stage constants are chosen before the live traversal. The modulo selector chooses
the appropriate body for each occurrence of a shrinking level in the repeated schedule. -/
def image {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
    (maps : Fin S.steps → LocatedBody) : Segment :=
  LocatedBody.family fun i =>
    stage (S.degreeExponent i.castSucc) B.shrink.selectorBits (maps i)

theorem prepare_rows (s t : ℕ) (B : LocatedBody) (M : Machine w p r 11)
    (pc : Fin (withHidden s t B).code.count → Fin p) (dfs : Fin 9 ↪ Fin r)
    (saved : Saved ↪ Fin r) (reg : Fin (withHidden s t B).code.privateRegs ↪ Fin r)
    (done : Fin p) (rows : ∀ i, M.code (pc i) =
      ((withHidden s t B).code.row pc dfs saved reg done i).resize w) :
    let X := prepare s t B
    let H := ShrinkHiddenGuess.Table.segment s t
    let ps := Preparation.phaseRegs H B.code reg
    let bs := Preparation.bodyRegs H B.code reg
    let inputs := (ShrinkHiddenGuess.Table.segmentInputs s t).trans ps
    let locator := B.locator.trans bs
    let pre := X.setupPC pc
    (∀ i, M.code (pre i.castSucc) =
      VertexLevel.hiddenHandoff (pre ∘ Fin.castSucc) locator inputs (dfs 6)
        (pre (Fin.last VertexLevel.hiddenCount)) i) ∧
    M.code (pre (Fin.last VertexLevel.hiddenCount)) =
      .copy (locator 8) (inputs 1) (X.phasePC pc H.entry) ∧
    (∀ i, M.code (X.phasePC pc i) =
      (H.row (X.phasePC pc) dfs saved ps (X.bodyPC pc B.code.entry) i).resize w) ∧
    (∀ i, M.code (X.bodyPC pc i) = (B.code.row (X.bodyPC pc) dfs saved bs done i).resize w) := by
  let X := prepare s t B
  obtain ⟨pre, phase, body⟩ := X.links M pc dfs saved reg done rows
  refine ⟨fun i => ?_, ?_, phase, body⟩
  · apply (pre i.castSucc).trans
    simp only [X, prepare, Fin.lastCases_castSucc, VertexLevel.resize_hiddenHandoff]
  · apply (pre (Fin.last VertexLevel.hiddenCount)).trans
    simp only [X, prepare, Fin.lastCases_last, Instr.resize]

end PairSimulation.ShrinkVertexStage

end

end VPVNP
end Computability
end OAI
