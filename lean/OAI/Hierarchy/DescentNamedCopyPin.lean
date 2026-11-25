import OAI.Hierarchy.DescentNamedOriginalExterior

namespace OAI
/-! # Transporting an individual physical address pin across the true copy-count equality -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open Catalyst CatalystSubstitution CorrectionFrame

def copyPin {F:Type} [Field F] {cp P:ℕ} (X:Approximation F cp P) (t:ℕ) {m n:ℕ} (equal:m=n)
    (a:Port ((n*t)*P) (copiesWidth (n*t) X.width)) : Port ((m*t)*P) (copiesWidth (m*t) X.width) :=
  equal.symm ▸ a

theorem copyPin_eval {F:Type} [Field F] {cp P:ℕ} (X:Approximation F cp P) (t:ℕ) {m n:ℕ} (equal:m=n)
    {A:Type} (x:Port ((m*t)*P) (copiesWidth (m*t) X.width)→Bool) (z:A→Bool)
    (pin:(Port ((n*t)*P) (copiesWidth (n*t) X.width)⊕A)⊕Bool) :
    Sum.elim (Sum.elim x z) id (pin.map (Sum.map (copyPin X t equal) id) id)=
      Sum.elim (Sum.elim (copyInput X t equal x) z) id pin := by
  subst n
  rcases pin with ((v|v)|v) <;> rfl

end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
