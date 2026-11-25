import OAI.Computability.NearSquareRoot.CommonAlphabetSweep

/-! # Writing all serialized blocks in one physical sweep -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet
open IntegerMultiplication
variable {A Q I : Type}

theorem writeSweep (c : Code A) (m : TM.Rule A Q I) (q : Q) (op : I → A × TM.Move)
    (T : I → TM.Tape A) (S : I → TM.Tape (Option Bool))
    (repr : ∀ i, Represents c (S i) (T i)) :
    ∃ S', Trace (TM.advance (rule c m)) ⟨.work q op .write (first c),S⟩ c.width
        ⟨.work q op .align₁ (first c),S'⟩ ∧
      (∀ i, SameCells c (S' i) ((T i).apply (op i))) ∧
      (∀ i, (S' i).pos = (T i).pos * c.width + c.width) := by
  let inv (r : ℕ) (Z : I → TM.Tape (Option Bool)) :=
    (∀ i, Written c (Z i) (T i) (op i).1 r) ∧
    (∀ i, (Z i).pos = (T i).pos * c.width + r)
  have h₀ : inv 0 S := ⟨fun i => written_zero _ (repr i).2 _, fun i => by simpa using (repr i).1⟩
  obtain ⟨S', run, hw, hp⟩ := sweepAt c.pos (rule c m) (.work q op .write)
    (.work q op .align₁ (first c)) inv S h₀ fun j Z ⟨hw, hp⟩ => by
      let Z' (i : I) := (Z i).apply (c.enc (op i).1 j, .right)
      refine ⟨Z', rfl, fun i => written_succ c j (hw i) (hp i), fun i => ?_⟩
      change (Z i).pos + 1 = _
      rw [hp]
      push_cast
      ring
  exact ⟨S', run, fun i => written_full c (hw i) (op i).2, hp⟩

end CommonAlphabet

end NearSquareRoot
end Computability
end OAI
