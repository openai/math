import OAI.Computability.BorderVNP.CoverDeckTranslationKeys
import OAI.Computability.BorderVNP.PackedDeckChoiceCircuit
import OAI.Computability.BorderVNP.PackedChoiceMux

/-! # Reading the selected child of a product-cover residue -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open VPVNP.VerifierNetwork (Frame)

/-- Read the ordinary child address whose flag is set. -/
noncomputable def readFlagged (m k : ℕ) : Frame ((Fin m × Fin k) ⊕ Fin m) (Fin k) :=
  (Frame.initial id).step fun b => PackedChoiceMux.read Sum.inr (fun j => .inl (j,b))

theorem readFlagged_size (m k : ℕ) : (readFlagged m k).size ≤ k*(4*m+1) := by
  unfold readFlagged
  exact (Frame.step_size_le _ _ (4*m+1) (fun _ => PackedChoiceMux.read_size _ _)).trans (by simp)

/-- A one-hot first-minimum flag selects precisely that row's wire value. -/
theorem readFlagged_eval (m k : ℕ) (x : (Fin m × Fin k) ⊕ Fin m → Bool) (j : Fin m)
    (h : ∀ i, x (.inr i) = true ↔ i = j) (b : Fin k) :
    (readFlagged m k).eval x b = x (.inl (j,b)) := by
  have hid : (Frame.initial id).eval x = x := funext (Frame.initial_eval id x)
  simpa [readFlagged,hid] using PackedChoiceMux.read_eval Sum.inr (fun i => Sum.inl (i,b)) x j h

/-- Gate bound for one complete digit, including the translated lookup keys,
two batched histograms per bin, the score comparisons, and the child read. -/
noncomputable def digitCost (B : Type*) [Fintype B] (q d l w U t C e : ℕ) : ℕ :=
  (childrenFrame q d).size + 1 + (childCount q d * (Fintype.card (Fin q → Deck (d+1)) * q)) *
      (3 * width (d+1) + U * (d+1+1)^t) +
    (1 + childCount q d * PackedDeckScore.childCost B (Fin q → Deck l) (Fin q → Deck (d+1))
        (keyWidth q (d+1)) w C e +
      childCount q d * ((15*PackedDeckScore.scoreBits B (Fin q → Deck (d+1)) w+3)*childCount q d+1)) +
    keyWidth q (d+1)*(4*childCount q d+1)

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
