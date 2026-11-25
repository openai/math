import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRoundForward
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoicePartition
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoiceTag
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementNewWeight

/-! # Weight of the concrete replacement selected on an old map -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators

namespace PortGraph.ShapeCatalogue

open ReplacementChoices ReplacementTemplate UniformDecorations

variable {N K w c : ℕ} {ε : ℝ} {F : Type} [Field F] (C : ShapeCatalogue F K w c)

/-- Restricting the uniform catalogue coefficient to one template recovers
its local tables, for the direct term and for every pruned trivalent tree. -/
theorem roleTable_coefficient (j : C.Tag N ε) :
    roleTable C.coefficient j = (C.selected j).localTable :=
  roleTable_roleCoefficient (T := C.templates) (fun j => (C.selected j).localTable) j

/-- The old-width value of one position in the checked record's list. -/
abbrev termValue (r : Checked N K ε) (i : C.Index r) := (C.selected ⟨r,i⟩).value

variable (S : System N K ε) (M : MapRep N) (v : (S.family C.Index).Label M)

local notation "tg" => S.choiceTag C.Index v
local notation "templatesForMap" => C.templates (N:=N) (ε:=ε)
local notation "pieces" => Forward.pieces (T := templatesForMap) tg

/-- On the smaller assembly of the chosen records and indices, its accepted
class weight is exactly the chosen summand of the old-map expansion. No
boundary terms from the larger common alphabet remain. -/
theorem mapWeight_eq_choiceValue
    [DecidableEq (StubPairing.Vertex pieces)]
    (H : RootedMap (StubPairing.Vertex pieces) ((S.pairing M).Edge pieces))
    (src : H.graph = Forward.graph (T := templatesForMap) tg (S.pairing M))
    (ports : ∀ e b, H.portNumber e b =
      (endNumber (C.rules N ε).slot (Forward.namedEnd (T := templatesForMap) tg (S.pairing M) (e,b))).val)
    (pass : (C.rules N ε).Accepts H (Forward.label (T := templatesForMap) tg)) :
    (C.rules N ε).roleContraction H C.coefficient ⟨Forward.label tg,pass⟩ =
      S.choiceValue M C.Index C.termValue v := by
  apply Forward.mapWeight_of_paddedTerms (T := templatesForMap) tg (S.pairing M) (C.rules N ε) C.coefficient
    H src ports pass (Nat.pow_le_pow_right (by decide) (by omega : w ≤ 8*w))
    (fun i => C.termValue (S.checked M i) (v i))
  intro i x
  exact (congrArg (fun U => (C.templates (tg i)).graph.openValue (C.templates (tg i)).attach U x)
    (C.roleTable_coefficient (tg i))).trans ((C.selected (tg i)).openValue_all x)


set_option maxHeartbeats 1000000 in
/-- The accepted, numbered, rooted forward representative has the selected
old weight for every choice of an actual term in every canonical record. -/
theorem forwardWeight_eq_choiceValue :
    (C.rules N ε).roleContraction (C.forwardMap S M v) C.coefficient
      ⟨C.forwardLabel S M v,C.forward_accepts S M v⟩ = S.choiceValue M C.Index C.termValue v :=
  C.mapWeight_eq_choiceValue S M v (C.forwardMap S M v) rfl
    (C.forward_portNumber S M v) (C.forward_accepts S M v)

end PortGraph.ShapeCatalogue

end

end SpectralBooks
end LinearAlgebra
end OAI
