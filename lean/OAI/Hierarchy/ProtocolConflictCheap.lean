import OAI.Hierarchy.ProtocolConflictRAM
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Boolean-checkable instructions of the native greedy conflict scan -/

namespace Hierarchy.ProtocolConflictPack.Native
open ThreeFlat.RAM DescriptorExpr
open ProtocolRAM (admissible admissible_let admissible_rename opAllowed allowed)

private theorem both_ok {W : ℕ} (x y : T W) (hx : admissible x) (hy : admissible y) :
    admissible (both x y) := by
  simp [both,Term.select,Term.literal,admissible_let,admissible_rename,admissible,opAllowed,hx,hy]

theorem scan_cheap (W base n d : ℕ) : ProtocolRAM.CheapCode (scan W base n d) := by
  apply ProtocolRAM.writing_cheap
  let out := dst base n d
  have maskOk : admissible (mask W base out) := by
    simp [mask,row,Term.load,Term.binary,Term.literal,admissible_let,admissible_rename,admissible,opAllowed,allowed]
  have clearOk (j : Fin d) : admissible (clear W base n out j.val) := by
    simp [clear,neighbour,row,Term.select,Term.load,Term.binary,Term.literal,
      admissible_let,admissible_rename,admissible,opAllowed,allowed]
  have rest (js : List (Fin d)) : admissible (checks W base n d out js) := by
    induction js with
    | nil => trivial
    | cons j js ih => exact both_ok _ _ (clearOk j) ih
  exact both_ok _ _ maskOk (rest (List.finRange d))

end Hierarchy.ProtocolConflictPack.Native

end OAI
