import OAI.Computability.BorderVNP.PackedDeckChoice
import OAI.Computability.BorderVNP.PackedDeckScore

/-! # First exact conditional minimum in a bounded list of translated candidates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckChoice

open PackedDeckScore ParseBatchSort VPVNP.VerifierNetwork CoverDeck

variable {B G H : Type*} [Fintype B] [Fintype G] [Fintype H] [DecidableEq H] [Group G] [Group H]

/-- A real Boolean circuit produces the one-hot first minimizing child for the manuscript's
conditional score. The centered-array means can be arbitrary rational numbers per relative bin. -/
theorem exists_choices :
    ∃ C e : ℕ, ∀ (B : Type*) (G : Type*) (H : Type*)
      [Fintype B] [Fintype G] [Fintype H] [DecidableEq H] [Group G] [Group H]
      (m k w : ℕ) (π : G →* H) (_ : Function.Surjective π) (index : H ↪ Fin (2^k)),
      ∃ f : Frame (Input B G H m k w) (Fin m),
        f.size ≤ 1 + m*childCost B G H k w C e + m*((15*scoreBits B H w+3)*m+1) ∧
        ∀ (x : Input B G H m k w → Bool) (child : Fin m → H) (base mean : B → ℚ),
          (∀ i v, translated x i v = (index (child i * v)).val) →
          (∀ side t v, histogram π (counts x side t) v < 2^w) →
          ∀ i, f.eval x i = true ↔ (List.finRange m).argmin
            (fun j => conditionalScore π (fun t g => (counts x false t g : ℚ) - base t)
              (fun t g => (counts x true t g : ℚ)) mean (child j)) = some i := by
  obtain ⟨C,e,h⟩ := exists_scores_uniform
  refine ⟨C,e,?_⟩
  intro B G H instB instG instH decH groupG groupH m k w π hπ index
  obtain ⟨score,hs,he⟩ := h B G H m k w π index
  refine ⟨(firstMin m (scoreBits B H w)).subst score, ?_, ?_⟩
  · rw [Frame.subst_size]
    exact Nat.add_le_add hs (firstMin_size ..)
  · intro x child base mean haddr fits i
    rw [Frame.subst_eval, firstMin_eval]
    let a (j : Fin m) := numerator π (counts x false) (counts x true) (child j)
    let b (j : Fin m) := conditionalScore π (fun t g => (counts x false t g : ℚ) - base t)
        (fun t g => (counts x true t g : ℚ)) mean (child j)
    have ha : (fun l => value (fun d => score.eval x (l,d))) = a := funext (he x child haddr fits)
    rw [ha]
    change (List.finRange m).argmin a = some i ↔ (List.finRange m).argmin b = some i
    rw [argmin_congr a b (fun j l => (score_le_iff π hπ _ _ base mean (child j) (child l)).symm)]

omit [Fintype H] [DecidableEq H] [Group H] in
/-- Reading a flagged ordinal recovers exactly the selected child in the manuscript's list. -/
theorem chosen_child {m : ℕ} (child : Fin m → H) (s : H → ℚ) {i : Fin m}
    (h : (List.finRange m).argmin (s ∘ child) = some i) :
    chooseResidue s (List.ofFn child) = some (child i) := by
  simp only [chooseResidue, argmin_map, h, Option.map_some]

end PackedDeckChoice

end BorderVNP
end Computability
end OAI
