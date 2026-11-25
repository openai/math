import OAI.Computability.NearSquareRoot.CRTPositionPreparation
import OAI.Computability.NearSquareRoot.CRTPositionReadRows
import OAI.Computability.NearSquareRoot.CRTPositionRoundAction

/-! # Running a serialized round of position switches

The interpreter uses only the supplied tables of unary indices and the word.
It reads the six table groups in fixed chunk-pair order. Each pair of
cross-chunk tables drives three XORs, and each diagonal triple drives nine.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionPreparation

open IntegerMultiplication.Code

/-- Execute the six supplied read tables in pair order 00, 01, 02, 11, 12, 22. -/
def runTables {k : ℕ} (t : RoundTables) (w : Fin k → Bool) : Fin k → Bool :=
  let a := borrowFromRows t.2.1 0 (NativeRound.auxiliary 0) w
  let b := crossFromRows t.1.1 0 1 a
  let c := crossFromRows t.1.2.1 0 2 b
  let d := borrowFromRows t.2.2.1 1 (NativeRound.auxiliary 1) c
  let e := crossFromRows t.1.2.2 1 2 d
  borrowFromRows t.2.2.2 2 (NativeRound.auxiliary 2) e

private def nativeBoth {k : ℕ} (v : Equiv.Perm (Fin k)) (s d : Fin 3) : Both :=
  let m := k/3
  both (tally m,tally (m*s.val),tally (m*d.val),positionImages v)

private def nativeBorrow {k : ℕ} (v : Equiv.Perm (Fin k)) (c : Fin 3) : Borrow :=
  let m := k/3
  borrowedDescriptor (tally m,tally (m*c.val),positionImages v)

private theorem nativeTables {k : ℕ} (v : Equiv.Perm (Fin k)) :
    roundTables (tally (k/3),Reflections.table v) =
      ((nativeBoth v 0 1,nativeBoth v 0 2,nativeBoth v 1 2),
        nativeBorrow v 0,nativeBorrow v 1,nativeBorrow v 2) := by
  have dbl (n : ℕ) : twice (tally n) = tally (n+n) := by
    rw [← recover_tally (twice (tally n))]
    simp [twice]
  simp [roundTables,nativeBoth,nativeBorrow,dbl,Nat.mul_two,Reflections.table,positionImages,show tally 0 = [] from rfl]

private theorem nativeBoth_action {k : ℕ} (v : Equiv.Perm (Fin k)) (s d : Fin 3) (w : Fin k → Bool) :
    crossFromRows (nativeBoth v s d) s d w = crossWord v s d w :=
  crossFromRows_tables v s d w

private theorem nativeBorrow_action {k : ℕ} (v : Equiv.Perm (Fin k)) (hv : Function.Involutive v)
    (c d : Fin 3) (w : Fin k → Bool) :
    borrowFromRows (nativeBorrow v c) c d w = borrowWord v hv c d w :=
  borrowFromRows_tables v hv c d w

/-- The read maps emitted by the compiler drive exactly the six native operators
even when the outer word includes a remainder after the three complete chunks. -/
theorem runTables_native {k : ℕ} (v : Equiv.Perm (Fin k)) (hv : Function.Involutive v)
    (w : Fin k → Bool) :
    runTables (roundTables (tally (k/3),Reflections.table v)) w = NativeRound.bulkAction v hv w := by
  rw [nativeTables]
  simp only [runTables,nativeBoth_action,nativeBorrow_action v hv]
  rfl

/-- On three complete chunks the decoded tables implement the source permutation
on the entire word, including all positions used as temporary storage. -/
theorem runTables_value {m : ℕ} (v : Equiv.Perm (Fin (3*m))) (hv : Function.Involutive v)
    (w : Fin (3*m) → Bool) : runTables (roundTables (tally m,Reflections.table v)) w = w ∘ v := by
  have h := runTables_native v hv w
  rw [show 3*m/3 = m by omega] at h
  exact h.trans (NativeRound.bulkAction_value v hv w)

end Controlled.PositionPreparation

end NearSquareRoot
end Computability
end OAI
