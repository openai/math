import OAI.Computability.VPVNP.PairShrinkVertexEntry

/-!
# Installed component rows of the actual shrinking image

The address and register maps below are computed from the single hosted segment.
They recover the hidden-field code and gathered map code after the child scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkVertexImage

open BurstRAM BurstRAM.PrivateRAM VertexImage Compression CompressorRecords
open ShrinkMapImage VertexStagePrefix NodeArguments

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
    {t : ℕ} (ord : B.Entry → Fin t) (i : Fin S.steps)

/-- Input degree exponent at this elementary step of the block schedule. -/
abbrev oldExponent := S.degreeExponent i.castSucc
/-- Maximum number of hidden-field IDs reserved for a site's directory row at this old degree. -/
abbrev hiddenStride := ShrinkResidentLayout.rowCapacity (oldExponent i) false
/-- The resident map handler prefixed with the private histogram-base reload. -/
abbrev mapReload := ShrinkMapReload.body (maps B ord i)
/-- Instruction segment that guesses the hidden fields using the shrink block's selector width
and the old degree's directory stride. -/
abbrev hiddenCode := ShrinkHiddenGuess.Table.segment B.shrink.selectorBits (hiddenStride i)
/-- The preparation that installs hidden-field guessing immediately ahead of the histogram
reload and resident maps. -/
abbrev hiddenPrep :=
  ShrinkVertexStage.prepare B.shrink.selectorBits (hiddenStride i) (mapReload B ord i)
/-- The located continuation entered after the old-child argument scan, consisting of
hidden-field guessing, histogram reload, and resident maps. -/
abbrev afterChildren :=
  ShrinkVertexStage.withHidden B.shrink.selectorBits (hiddenStride i) (mapReload B ord i)
/-- The child-scan preparation that links the input degree's child argument bank to the located
hidden-field and map continuation. -/
abbrev childPrep := childPreparation (oldExponent i) (afterChildren B ord i).code
  (afterChildren B ord i).locator

variable {p r w : ℕ} (M : Machine w p r 11) (pc : Fin (shrinkSegment B ord).count → Fin p)
    (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
    (reg : Fin (shrinkSegment B ord).privateRegs ↪ Fin r)
    (done : Fin p) (rows : ∀ a, M.code (pc a) =
      ((shrinkSegment B ord).row pc dfs saved reg done a).resize w)

/-- Translate instruction ordinals of this elementary shrink into program counters in the whole
shrinking segment. -/
abbrev activePC := LocatedBody.stagePC (active B ord) pc i
/-- Embed this elementary shrink's private registers into the bank reserved for the whole
shrinking segment. -/
abbrev activeBank := LocatedBody.stageBank (active B ord) reg i

/-- Program counters of the continuation after child preparation, including the hidden-field
reader and the resident maps. -/
abbrev afterChildPC := (childPrep B ord i).bodyPC (activePC B ord i pc)
/-- Private registers of the continuation after the child scan, as embedded in the selected
stage's bank. -/
abbrev afterChildRegs := Preparation.bodyRegs (ChildCode.RegisterBank.segment (oldExponent i))
  (afterChildren B ord i).code (activeBank B ord i reg)

/-- Program-counter map of the hidden-field guessing phase inside the continuation reached
after the child scan. -/
abbrev hiddenPC := (hiddenPrep B ord i).phasePC (afterChildPC B ord i pc)
/-- Register embedding used by the hidden-field guessing phase in the post-child continuation. -/
abbrev hiddenRegs := Preparation.phaseRegs (hiddenCode B i) (mapReload B ord i).code
  (afterChildRegs B ord i reg)

/-- Program-counter map of the histogram reload and resident map body reached after
hidden-field preparation. -/
abbrev reloadPC := (hiddenPrep B ord i).bodyPC (afterChildPC B ord i pc)
/-- Register embedding for the histogram reload and resident map continuation after the
hidden-field scan. -/
abbrev reloadRegs := Preparation.bodyRegs (hiddenCode B i) (mapReload B ord i).code
  (afterChildRegs B ord i reg)

/-- Program counters for the resident map body on the far side of its four-instruction
histogram reload. -/
abbrev matrixPC := Segment.rightPC (ShrinkMapReload.setup (maps B ord i)) (maps B ord i).code
  (reloadPC B ord i pc)

include rows in
theorem after_child_rows (j : Fin (afterChildren B ord i).code.count) :
    M.code (afterChildPC B ord i pc j) = ((afterChildren B ord i).code.row (afterChildPC B ord i pc)
      dfs saved (afterChildRegs B ord i reg) done j).resize w :=
  (child_rows (oldExponent i) (afterChildren B ord i).code (afterChildren B ord i).locator M
    (activePC B ord i pc) dfs saved (activeBank B ord i reg) done
    (active_rows B ord M pc dfs saved reg done rows i)).2.2.2 j

include rows in
theorem hidden_rows (j : Fin (hiddenCode B i).count) :
    M.code (hiddenPC B ord i pc j) = ((hiddenCode B i).row (hiddenPC B ord i pc)
      dfs saved (hiddenRegs B ord i reg)
      ((reloadPC B ord i pc) (mapReload B ord i).code.entry) j).resize w :=
  (ShrinkVertexStage.prepare_rows B.shrink.selectorBits (hiddenStride i) (mapReload B ord i)
    M (afterChildPC B ord i pc) dfs saved (afterChildRegs B ord i reg) done
    (after_child_rows B ord i M pc dfs saved reg done rows)).2.2.1 j

include rows in
theorem reload_rows (j : Fin (mapReload B ord i).code.count) :
    M.code (reloadPC B ord i pc j) = ((mapReload B ord i).code.row (reloadPC B ord i pc)
      dfs saved (reloadRegs B ord i reg) done j).resize w :=
  (ShrinkVertexStage.prepare_rows B.shrink.selectorBits (hiddenStride i) (mapReload B ord i)
    M (afterChildPC B ord i pc) dfs saved (afterChildRegs B ord i reg) done
    (after_child_rows B ord i M pc dfs saved reg done rows)).2.2.2 j

include rows in
/-- The real role's map and party gather share these exact rows. -/
theorem selected_map_rows (j : Fin (maps B ord i).code.count) :
    M.code (matrixPC B ord i pc j) = ((maps B ord i).code.row (matrixPC B ord i pc)
      dfs saved (reloadRegs B ord i reg) done j).resize w :=
  (ShrinkMapReload.links (maps B ord i) M (reloadPC B ord i pc) dfs saved (reloadRegs B ord i reg)
    done (reload_rows B ord i M pc dfs saved reg done rows)).2 j

/-- The matrix and gather operands see the very same fourteen physical words that the
locator populated before the selected child and hidden routines. -/
theorem map_locator_shared (j : Fin 14) :
    reloadRegs B ord i reg ((maps B ord i).locator j) =
      LocatedBody.commonLocator (active B ord) reg j :=
  active_locator B ord reg i j

end PairSimulation.ShrinkVertexImage

end

end VPVNP
end Computability
end OAI
