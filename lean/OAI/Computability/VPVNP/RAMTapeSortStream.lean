import OAI.Computability.VPVNP.RAMTapeSortReplayFields

/-! # The sorting suffix as a sequence of raw record blocks -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortStream

open RAMSort RAMLayout Boundary SortReplay

variable {h d H w : ℕ}

/-- Every nonlocal layer consumes its two blocks, in send/receive order.
The addressed words are reconstructed directly from arbitrary incident bits. -/
def bytes (w : ℕ) (raw : ℕ → Bool) (s : Stage (h+d)) : List Bool :=
  if s.stride < h then [] else
    blockBytes (List.ofFn (fieldWords w raw s 0)) ++ blockBytes (List.ofFn (fieldWords w raw s 1))

private theorem chronological (hslots : 2^h = 4*H) (incident : Fin (width d H w) → Bool)
    (raw : ℕ → Bool) (hraw : ∀ k : Fin (width d H w), raw k.val = incident k)
    (ss : List (Stage (h+d))) :
    (ss.filterMap (SortSchedule.exchangeNumber h)).flatMap (SortSchedule.fieldPair incident) =
      ss.flatMap (bytes w raw) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    rw [List.filterMap_cons, List.flatMap_cons]
    by_cases hj : s.stride < h
    · rw [show SortSchedule.exchangeNumber h s = none by simp [SortSchedule.exchangeNumber, Nat.not_le_of_lt hj]]
      simp only [bytes, hj, ite_true, List.nil_append, ih]
    · have hc := Nat.le_of_not_gt hj
      rw [SortSchedule.exchangeNumber_eq s hc]
      simp only [List.flatMap_cons, ih, bytes, hj, ite_false]
      rw [fieldPair_eq_blocks hslots incident raw hraw s hc]

/-- Removing the two successor fields leaves precisely the stream on which
the stage routine operates. This covers malformed tags and padding. -/
theorem suffix (hslots : 2^h = 4*H) (incident : Fin (width d H w) → Bool)
    (raw : ℕ → Bool) (hraw : ∀ k : Fin (width d H w), raw k.val = incident k) :
    (List.ofFn incident).drop (16*w) = (phases (h+d) (h+d) le_rfl).flatMap (bytes w raw) := by
  have h₁ := SuccessorFields.incident_prefix incident
  have h₂ := SortSchedule.incident_stream h incident
  rw [chronological hslots incident raw hraw] at h₂
  exact List.append_cancel_left (h₁.symm.trans h₂)

end RAMTape.SortStream

end VPVNP
end Computability
end OAI
