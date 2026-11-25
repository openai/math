import OAI.Computability.BorderVNP.CubeISADeclaredRowTally

/-! # Keeping the outer unordered-pair cursor across a row tally

Registers 22 and 23 carry the current unordered-pair trial and its bound.
Neither the packet candidate filter nor the scalar row updates overwrite
these registers on either conditional branch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.DeclaredRow

private theorem candidates_keep (n : ℕ) :
    (Owned.packetCandidate n).keeps 22 = true ∧ (Owned.packetCandidate n).keeps 23 = true ∧
    (Owned.singleCandidate n).keeps 22 = true ∧ (Owned.singleCandidate n).keeps 23 = true := by
  induction n with
  | zero => decide
  | succ n ih =>
    change ((Owned.packetCandidate n).keeps 22 && true) = true ∧
      ((Owned.packetCandidate n).keeps 23 && true) = true ∧
      (Owned.singleCandidate n).keeps 22 = true ∧ (Owned.singleCandidate n).keeps 23 = true
    simpa only [Bool.and_true] using ih

/-- The sole diagonal row scan preserves each reserved outer cursor word. -/
theorem diagonal_keeps (n : ℕ) (k : Reg) (hk : k = 22 ∨ k = 23) :
    (SingleTally.oriented n).keeps k = true := by
  obtain ⟨_,_,h22,h23⟩ := candidates_keep n
  rcases hk with rfl | rfl
  · change ((Owned.singleCandidate n).keeps 22 && true) = true
    simp [h22]
  · change ((Owned.singleCandidate n).keeps 23 && true) = true
    simp [h23]

/-- The packet and two singleton orientations of a strict row preserve the
outer unordered-pair cursor and its bound on all executed paths. -/
theorem strict_keeps (n : ℕ) (k : Reg) (hk : k = 22 ∨ k = 23) :
    (strict n).keeps k = true := by
  obtain ⟨h22,h23,_,_⟩ := candidates_keep n
  have hs := diagonal_keeps n k hk
  rcases hk with rfl | rfl
  · change (((Owned.packetCandidate n).keeps 22 && true) &&
      ((SingleTally.oriented n).keeps 22 && (SingleTally.oriented n).keeps 22)) = true
    simp [h22,hs]
  · change (((Owned.packetCandidate n).keeps 23 && true) &&
      ((SingleTally.oriented n).keeps 23 && (SingleTally.oriented n).keeps 23)) = true
    simp [h23,hs]

end RoutingISA.DeclaredRow

end BorderVNP
end Computability
end OAI
