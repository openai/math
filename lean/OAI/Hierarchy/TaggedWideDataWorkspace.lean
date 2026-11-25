import OAI.Hierarchy.TaggedWideOutputPlane

namespace OAI
/-! # The common data workspace of the physical board -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open scoped Classical

/-- Numbered positive-bank bits, private (unshortened) endpoint data, the
whole calendar site trajectory, and the fixed decoded switched-word plane.
Intermediate packet and radius bonds are internal to their local programs. -/
abbrev DataWorkspace (T G E H : Type) [Fintype H] (ports lanes dates view : ℕ)
    (width : T→ℕ) (privateCap : E→ℕ) (historyCap : H→ℕ) :=
  OutputData T G ports lanes width ⊕ ((Bool × ((e:E) × Fin (privateCap e))) ⊕
    (Fin (dates*Fintype.card ((p:H) × Fin (historyCap p))) ⊕ ((G×Fin ports)×Fin view)))

end Hierarchy.Tagged.WideStack
end

end OAI
