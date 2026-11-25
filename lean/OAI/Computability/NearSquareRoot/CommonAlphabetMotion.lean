import OAI.Computability.NearSquareRoot.CommonAlphabetSweep

/-! # Alignment and rewind of the simulated heads -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet
open IntegerMultiplication
variable {A Q I : Type} (c : Code A) (m : TM.Rule A Q I)

/-- Rewriting the scanned symbols and moving for a whole block preserves each tape's contents. -/
private theorem hold_sweep (stage : Fin c.width → PC A Q I c.width)
    (done : PC A Q I c.width) (moves : I → TM.Move) (S : I → TM.Tape (Option Bool))
    (transition : ∀ j a, rule c m (stage j) a =
      some (atIndex c.width stage done (j.val+1), hold a moves)) :
    ∃ T, Trace (TM.advance (rule c m)) ⟨stage (first c), S⟩ c.width ⟨done, T⟩ ∧
      ∀ i, (T i).absolute = (S i).absolute ∧ (T i).pos = (S i).pos + c.width * (moves i).shift := by
  apply sweepAt c.pos (rule c m) stage done
    (fun n T => ∀ i, (T i).absolute = (S i).absolute ∧
      (T i).pos = (S i).pos + n * (moves i).shift) S
  · simp
  · intro j T hT
    refine ⟨fun i => (T i).apply ((T i).view 0, moves i), ?_, ?_⟩
    · simp [TM.advance, transition, hold]
    · intro i
      refine ⟨(funext fun p => idleWrite (T i) (moves i) p).trans (hT i).1, ?_⟩
      change (T i).pos + (moves i).shift = _
      rw [(hT i).2, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc]

/-- After writing a block, the two alignment sweeps move each tape to the first bit of
the block selected by its virtual head movement. -/
theorem align_run (q : Q) (op : I → A × TM.Move) (T : I → TM.Tape A)
    (S : I → TM.Tape (Option Bool)) (h : ∀ i, (S i).pos = (T i).pos * c.width + c.width) :
    ∃ S', Trace (TM.advance (rule c m)) ⟨.work q op .align₁ (first c), S⟩ (2*c.width)
        ⟨readStart c q, S'⟩ ∧
      ∀ i, (S' i).absolute = (S i).absolute ∧
        (S' i).pos = (T i).pos * c.width + (op i).2.shift * c.width := by
  obtain ⟨U,run₁,hU⟩ := hold_sweep c m (.work q op .align₁) (.work q op .align₂ (first c))
    (fun i => turn₁ (op i).2) S (fun _ _ => rfl)
  obtain ⟨V,run₂,hV⟩ := hold_sweep c m (.work q op .align₂) (readStart c q)
    (fun i => turn₂ (op i).2) U (fun _ _ => rfl)
  refine ⟨V, by simpa [two_mul] using run₁.trans run₂, fun i => ⟨(hV i).1.trans (hU i).1, ?_⟩⟩
  rw [(hV i).2, (hU i).2, h i, ← aligned (op i).2]
  ring

/-- After reading a block, the rewind restores the heads to its first bit. -/
theorem rewind_run (q : Q) (cached : I → A) (S : I → TM.Tape (Option Bool)) :
    ∃ S', Trace (TM.advance (rule c m)) ⟨.rewind q cached (first c), S⟩ c.width
        ⟨.ready q cached, S'⟩ ∧
      ∀ i, (S' i).absolute = (S i).absolute ∧ (S' i).pos = (S i).pos - c.width := by
  obtain ⟨T,run,hT⟩ := hold_sweep c m (.rewind q cached) (.ready q cached) (fun _ => .left)
    S (fun _ _ => rfl)
  refine ⟨T,run,fun i => ⟨(hT i).1, ?_⟩⟩
  simpa [TM.Move.shift, sub_eq_add_neg] using (hT i).2

end CommonAlphabet

end NearSquareRoot
end Computability
end OAI
