import OAI.Computability.IntegerMultiplication.Adic.Drive
import OAI.Computability.IntegerMultiplication.Loom.Skein

/-! # Canonical payload coordinates and physical row size -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Code
open IntegerMultiplication.Strip IntegerMultiplication.Loom

/-- Tabulating a payload on its natural indices preserves its serialized order. -/
theorem stripe_natural_follow {A : Type} (u : Series A) (f : A → Tree) :
    stripe (Series.natural u.count) (fun i => f (u.follow i)) = stripe u f := by
  rw [stripe_eq,stripe_eq]
  apply congrArg send
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [Series.tab,List.getElem_map,Series.natural,Series.fixed,List.getElem_finRange,
      Series.follow, Fin.val_cast]

/-- A complete binary array of bead payloads has at most three physical tree nodes
per address and payload position counted with its row delimiter. -/
theorem position_row_count {A : Type} (k : ℕ) (u : Series A) (f : Block 2 k → A → Bead) :
    (stripe (line 2 k) (fun a => stripe u (fun i => send (f a i)))).count ≤
      3 * 2^k * (u.count+1) := by
  have h := stripe_size (line 2 k) (fun a => stripe u (fun i => send (f a i)))
    (2*u.count+1) (fun a => bulk u (f a))
  rw [lineSize] at h
  have pos : 0 < 2^k * (u.count+1) := by positivity
  nlinarith

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
