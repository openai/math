import OAI.Computability.VPVNP.MacaulayOrdinary
import OAI.Computability.VPVNP.RankCoordinateSelectedAdvice

/-! # Fixed ports of the advised compressor-coordinate reader

The index and scalar values vary with the model, while the set of advice and
workspace ports below is the same for every prime, length and operation.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

set_option maxRecDepth 10000

namespace CompressorReader

open RankQuery.Stack RankQuery.Stack.Coordinate

/-- Raw advice-port type used for Macaulay matrix entries by the compressor coordinate reader. -/
abbrev K := MacaulayRead.BaseAdvice.RawPort
/-- Denominator, raw, and side preparation components for the selected coordinate advice. -/
abbrev Parts := SelectedAdvice.Parts K
/-- Advice ports for the compressor's selected coordinate preparation over the raw Macaulay
port bank. -/
abbrev Advice := SelectedAdvice.Advice K
/-- Working ports used by the selected coordinate preparation routines. -/
abbrev Work := SelectedAdvice.Work K
/-- Combined reader port type separating advised inputs from working storage. -/
abbrev Ports := Advice ⊕ Work

set_option synthInstance.maxSize 8000 in
instance rawDecidable : DecidableEq K := inferInstanceAs (DecidableEq
  (MacaulayRowDispatch.Small ⊕ MacaulayRead.Arms.Leaf MacaulayRead.Arms.CoefficientPort))

set_option synthInstance.maxSize 12000 in
instance partsFinite : Fintype Parts := inferInstanceAs (Fintype
  (Prepare.Root (SelectedAdvice.Den K) (SelectedAdvice.Raw K) ⊕
    (Dynamic.Host (SelectedAdvice.Side K) ⊕ RAMTape.UnaryWord.Port)))

set_option synthInstance.maxSize 12000 in
instance partsDecidable : DecidableEq Parts := Prepare.partsDecidable

instance adviceDecidable : DecidableEq Advice := inferInstanceAs (DecidableEq (Parts ⊕ Bool))
instance workDecidable : DecidableEq Work := inferInstanceAs (DecidableEq (Parts ⊕ Unit))
instance adviceFinite : Fintype Advice := inferInstanceAs (Fintype (Parts ⊕ Bool))
instance workFinite : Fintype Work := inferInstanceAs (Fintype (Parts ⊕ Unit))

end CompressorReader

end

end VPVNP
end Computability
end OAI
