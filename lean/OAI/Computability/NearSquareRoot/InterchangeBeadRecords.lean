import OAI.Computability.NearSquareRoot.InterchangeAlphabet
import OAI.Computability.NearSquareRoot.InterchangePackedRequest
import OAI.Computability.IntegerMultiplication.Short

/-!
# Binary data inside the larger interchange field

Choose the two field codes occurring on a binary input to be precisely the
existing P192 bead codes. Other field elements are tagged fork trees. The
packed request therefore accepts an ordinary P192 bead stripe directly.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePayload
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
open NearSquareRoot.InterchangeAddress.Request

noncomputable section

variable {F : Type} [Field F] [Finite F] [DecidableEq F]

/-- The zero and one field elements have the two one-cell input codes. -/
def beadDigit (x : F) : Tree :=
  if x = 0 then .atom false else if x = 1 then .atom true
  else .fork (.atom false) (InterchangeAlphabet.symbol x)

theorem beadDigit_injective : Function.Injective (beadDigit (F:=F)) := by
  intro x y he
  by_cases x0 : x = 0 <;> by_cases x1 : x = 1 <;> by_cases y0 : y = 0 <;> by_cases y1 : y = 1 <;>
    simp_all [beadDigit, InterchangeAlphabet.symbol_injective.eq_iff]

/-- The bead's installed binary encoder fixes which symbol is the zero code. -/
def beadValue (v : Bead) : F := if notify v then 1 else 0

@[simp] theorem beadDigit_value (v : Bead) : beadDigit (beadValue (F:=F) v) = send v := by
  change _ = Tree.atom (notify v)
  cases eq : notify v <;> simp [beadDigit,beadValue,eq]

/-- The series `t` may occur in any order. A normal binary cloth row is an
exact record over the finite repair alphabet in its natural tabulation. -/
theorem bead_record {T : Type} (t : Series T) (v : T → Bead) :
    record (beadDigit (F:=F)) t.count (stripe t (send ∘ v)) := by
  let rep := t.native
  refine ⟨fun j => beadValue (v (rep.cast.symm j)), ?_⟩
  rw [rep.packet]
  apply congrArg (stripe t)
  funext j
  simp [Function.comp_def,rep]

end
end InterchangePayload

end NearSquareRoot
end Computability
end OAI
