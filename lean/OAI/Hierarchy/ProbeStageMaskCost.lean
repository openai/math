import OAI.Hierarchy.ProbeStageScanCost

namespace OAI
/-! # Fallbacks and linear charges for the actual masked coloring trajectory -/

namespace Hierarchy.ProbeStage

open Finset

/-- One candidate-string table is shared across all tiles and blocks of this stage. -/
structure MaskAdvice (B ℓ : ℕ) where
  row : MaskIndex B → Fin ℓ → Fin B
  sparse : ∀ S : Finset (Fin B), 4*S.card ≤ B → (overloaded row S).card < B

namespace MaskAdvice

variable {n m B ℓ : ℕ} {G : Type*} [DecidableEq G]

def pick (A : MaskAdvice B ℓ) (p : Tiles (Fin n) G m) (pos : 0<B) (i : Fin n) :=
  maskedChoice pos (A.row (maskIndex p pos i))

private def final (A : MaskAdvice B ℓ) (p : Tiles (Fin n) G m) (pos : 0<B) :=
  Greedy.colors pos (A.pick p pos) (leftBlock p pos) (rightBlock p pos) n

def sourceCharges (A : MaskAdvice B ℓ) (p : Tiles (Fin n) G m) (pos : 0<B) (g : G × Fin (blocks m B)) :=
  univ.filter fun i => leftBlock p pos i=g ∧ maskIndex p pos i ∈ overloaded A.row
    (Greedy.fullColors (leftBlock p pos) (A.final p pos) g)

def targetCharges (A : MaskAdvice B ℓ) (p : Tiles (Fin n) G m) (pos : 0<B) (g : G × Fin (blocks m B)) :=
  univ.filter fun i => rightBlock p pos i=g ∧ maskIndex p pos i ∈ overloaded A.row
    (Greedy.fullColors (rightBlock p pos) (A.final p pos) g)

/-- Every fallback on the actual row belongs to at least one of its two block charge sets. -/
theorem charged (A : MaskAdvice B ℓ) (p : Tiles (Fin n) G m) (pos : 0<B) (i : Fin n)
    (miss : freeBits (A.row (maskIndex p pos i))
      (Greedy.available (leftBlock p pos) (rightBlock p pos) (Greedy.before n i)
        (Greedy.colors pos (A.pick p pos) (leftBlock p pos) (rightBlock p pos) i) i) = ∅) :
    i ∈ A.sourceCharges p pos (leftBlock p pos i) ∨ i ∈ A.targetCharges p pos (rightBlock p pos i) := by
  have h := fallback_charge pos (leftBlock p pos) (rightBlock p pos) (A.pick p pos)
    (fun j => A.row (maskIndex p pos j)) i miss
  rcases h with h|h
  · exact Or.inl (mem_filter.mpr ⟨mem_univ _,rfl,mem_filter.mpr ⟨mem_univ _,h⟩⟩)
  · exact Or.inr (mem_filter.mpr ⟨mem_univ _,rfl,mem_filter.mpr ⟨mem_univ _,h⟩⟩)

/-- Charging every scan at its full `B` steps, each individual source and target block pays at
most `B⁹` steps. The same advice works for every matching in the stage. -/
theorem scan_bounds (A : MaskAdvice B ℓ) (p : Tiles (Fin n) G m) (pos : 0<B) (g : G × Fin (blocks m B)) :
    B * (A.sourceCharges p pos g).card ≤ blockSize B ∧ B * (A.targetCharges p pos g).card ≤ blockSize B := by
  have lc := Fintype.card_le_of_injective _ (leftBlockFiber p pos g).injective
  have rc := Fintype.card_le_of_injective _ (rightBlockFiber p pos g).injective
  simp only [Fintype.card_subtype,Fintype.card_fin] at lc rc
  exact ⟨scan_cost _ _ _ (source_residue_bound p pos g) _ _ (A.sparse _ (Greedy.fullColors_card pos _ _ _ lc)),
    scan_cost _ _ _ (target_residue_bound p pos g) _ _ (A.sparse _ (Greedy.fullColors_card pos _ _ _ rc))⟩

end MaskAdvice
end Hierarchy.ProbeStage

end OAI
