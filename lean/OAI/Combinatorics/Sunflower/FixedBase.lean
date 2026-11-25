import OAI.Combinatorics.Sunflower.RuleDevices
import OAI.Combinatorics.Sunflower.Transfer

/-! # The fixed-base Erdős–Rado sunflower theorem -/

open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- For each number of petals, the planar configuration gives one base for all
word lengths and all finite alphabets. -/
theorem fixedBase_words (r : ℕ) (hr : 3 ≤ r) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (k m : ℕ) (W : Finset (Fin k → Fin m)),
      WordFree r W → W.card ≤ D ^ k := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  obtain ⟨φ, hgap, htests⟩ := RuleDevices.exists_devices n
  let rules := anchorRules (0 : Fin (n + 2)) 1
  let cost (q : Rule (Fin (n + 2))) : ℝ :=
    if h : q ∈ rules then (htests q h).choose else 0
  let ρ := 1 - ∑ j, maskDiagonalPrice φ 1 (Placement.fiber j)
  obtain ⟨D, hD, hbound⟩ := exists_natBase_of_logb_bound (ρ := ρ) hgap (∑ q ∈ rules, cost q)
  refine ⟨D, hD, fun k m W hfree => hbound k W.card (fun hpos => ?_)⟩
  have hfiber (j : Fin (n + 2)) :
      Comparison.fiber Placement.group j = Placement.fiber j := by
    ext s
    simp only [Comparison.mem_fiber, Placement.mem_fiber]
  have hc := Comparison.wordComparison φ Placement.group Placement.group_surjective 0 1
    Fin.zero_ne_one W (Finset.card_pos.mp hpos) hfree cost (by
      intro q hq
      simpa only [cost, dite_eq_left (show q ∈ rules from hq)] using (htests q hq).choose_spec m)
  simpa only [ρ, rules, hfiber] using hc

universe u

/-- A family of more than `C ^ k` distinct `k`-sets contains an `r`-sunflower.
The natural base is chosen before the uniformity and ground type. -/
theorem erdosRadoSunflower (r : ℕ) (hr : 3 ≤ r) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (k : ℕ) (α : Type u) (F : Finset (Finset α)),
      (∀ A ∈ F, A.card = k) → C ^ k < F.card →
      ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset α,
        ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K := by
  obtain ⟨D, _, hword⟩ := fixedBase_words r hr
  obtain ⟨C, hC, hsets⟩ := fixedBase_of_wordBound.{u} (D := D) hword
  exact ⟨C, hC, fun k α F => hsets k α F⟩

end Sunflower
end Combinatorics
end OAI
