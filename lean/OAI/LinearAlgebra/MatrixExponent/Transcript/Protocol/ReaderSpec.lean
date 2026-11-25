import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.HistorySpec
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.IndexSpec


/-! # The ordered RAM image and the original bit sources -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
open Coloring

namespace Strings

variable {I : Type} {A : Format} {n : I → ℕ}

def memory (k M : ℕ) (row : Rows A n) (i : I) : B (width A k M) → Bool :=
  Function.extend (address A k M) (fun v =>
    if h : v.1.val < n i then packet A k (row i ⟨v.1.val, h⟩) v.2 else false) (fun _ => false)

def inputMemory {Z : Type} (A : Format) (k M : ℕ) (place : Z ↪ B (width A k M - 1))
    (z : Z → Bool) (m : B (width A k M) → Bool) : B (width A k M) → Bool :=
  Function.extend (place.trans (workspace A k M)) z m

end Strings

namespace Spec
variable {X : Type} {k H : ℕ} (S : Spec X k H)

/-- Every bit used in the upload is read directly from the record. -/
def source (g j : Level k) : Strings.Bank S.key k S.messages (2 ^ j.val) → S.withOrder.Fields g j
  | .inl ⟨s, b⟩ => .inr ⟨s.1, s.2, b⟩
  | .inr v => .inl (S.orderPins g j (.inr v))

end Spec
end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
