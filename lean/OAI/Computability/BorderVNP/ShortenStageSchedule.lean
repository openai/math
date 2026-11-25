import OAI.Computability.BorderVNP.CoverDeckTower
import OAI.Computability.BorderVNP.ShortenPhysicalEpoch

/-!
# Preparing a finite chain of catalogs and choosing all quotient levels

The data of the next stage may depend on the current finite relative
catalog. The entire chain is fixed before the fan-in and initial packs.
Each chosen Hecke word length causes a drop of twice that length, including
the final motion back to sites. A single lower threshold on the initial
level guarantees every individual stage threshold and bounds all intermediate
product tile counts by the original count.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Adaptive

open Cover Finset
open scoped Classical

universe u v

/-- Successive relative catalogs and the fixed preparation selected at
each of the finitely many rounds. -/
structure PreparedPath (b : ℕ) {S : Type u} (Step : S → Type v) (advance : ∀ s, Step s → S) where
  /-- The catalog at the input of each stage and at the final output. -/
  catalog : ℕ → S
  /-- The single fixed preparation for every attained branch at this stage. -/
  pattern : ∀ i : Fin b, Step (catalog i.val)
  /-- The successor catalog is exactly the one prepared by this step. -/
  next : ∀ i : Fin b, catalog (i.val+1) = advance (catalog i.val) (pattern i)

/-- Independent per-catalog existence selects a whole finite path before
any of the actual packs, levels, or profile choices are supplied. -/
theorem exists_prepared_path {S : Type u} (Step : S → Type v) (advance : ∀ s, Step s → S)
    (prepare : ∀ s, Nonempty (Step s)) (b : ℕ) (initial : S) :
    ∃ path : PreparedPath b Step advance, path.catalog 0 = initial := by
  let select := fun s => (prepare s).some
  let catalog (n : ℕ) : S := Nat.rec initial (fun _ s => advance s (select s)) n
  exact ⟨⟨catalog,fun i => select (catalog i.val),fun _ => rfl⟩,rfl⟩

namespace Levels

variable {b : ℕ} (word : Fin b → ℕ)

/-- Remaining intermediate cover drop at the input of stage j. -/
def remaining (j : ℕ) : ℕ := ∑ i : Fin b, if j ≤ i.val then 2*word i else 0

/-- Passing one prepared stage removes exactly its chosen twice-word-length drop. -/
theorem remaining_step (i : Fin b) : remaining word i.val = remaining word (i.val+1) + 2*word i := by
  unfold remaining
  calc
    _ = ∑ j : Fin b, ((if i.val+1 ≤ j.val then 2*word j else 0) + (if i = j then 2*word i else 0)) := by
      apply sum_congr rfl
      intro j _
      by_cases hij : i = j
      · subst j; simp
      · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
        by_cases h : i.val ≤ j.val
        · simp [h,hij,show i.val+1 ≤ j.val by omega]
        · simp [h,hij,show ¬ i.val+1 ≤ j.val by omega]
    _ = _ := by rw [sum_add_distrib]; simp

/-- Intermediate depth indexed by the final rounded depth and the last
motion's word length. Surface packs use the quotient at one plus this depth. -/
def level (terminal last j : ℕ) : ℕ := terminal + 2*last + remaining word j

/-- Exact depth difference in the index used by PlacedPack. -/
theorem step_depth (terminal last : ℕ) (i : Fin b) :
    level word terminal last i.val = level word terminal last (i.val+1) + 2*word i := by
  unfold level
  rw [remaining_step]
  omega

/-- The exact input-output quotient equation for each finite stage. -/
theorem step (terminal last : ℕ) (i : Fin b) :
    level word terminal last i.val + 1 = (level word terminal last (i.val+1) + 1) + 2*word i := by
  unfold level
  rw [remaining_step]
  omega

/-- After all intermediate stages, precisely the final rounding drop remains. -/
theorem finish (terminal last : ℕ) : level word terminal last b = terminal + 2*last := by
  simp [level,remaining,show ∀ i : Fin b, ¬ b ≤ i.val from fun i => Nat.not_le.mpr i.isLt]

/-- Total drop, fixed by the preparation and including the final site motion. -/
def totalDrop (last : ℕ) : ℕ := 2*last + ∑ i, 2*word i

/-- At the initial pack the scheduled depth is the final depth plus the entire drop. -/
theorem start (terminal last : ℕ) : level word terminal last 0 = terminal + totalDrop word last := by
  simp [level,totalDrop,remaining,Nat.add_assoc]

/-- Every output level is at least the final rounded level. -/
theorem terminal_le (terminal last j : ℕ) : terminal ≤ level word terminal last j := by
  unfold level; omega

/-- Every intermediate level is at most the starting level. -/
theorem le_start (terminal last j : ℕ) : level word terminal last j ≤ level word terminal last 0 := by
  apply Nat.add_le_add_left
  apply sum_le_sum
  intro i _
  simp only [Nat.zero_le,ite_true]
  split_ifs <;> omega

/-- The product quotient at each output level is a surjective image of the
starting one, so the same V controls the additive tile loss everywhere. -/
theorem tiles_le_start (I : Type*) [Fintype I] (terminal last j : ℕ) :
    Fintype.card (I → Deck (level word terminal last j + 1)) ≤
      Fintype.card (I → Deck (level word terminal last 0 + 1)) := by
  let hl := Nat.succ_le_succ (le_start word terminal last j)
  let f := fun (x : I → Deck (level word terminal last 0 + 1)) i => deckReduction hl (x i)
  exact Fintype.card_le_of_surjective f (Function.Surjective.piMap (fun _ => deckReduction_surjective hl))

/-- Given the starting level, one explicit threshold enforces all the chosen
output-depth floors and the final rounding floor at once. -/
theorem of_start (last lastFloor : ℕ) (floor : Fin b → ℕ) {high : ℕ}
    (hhigh : totalDrop word last + (lastFloor + ∑ i, floor i) ≤ high) :
    let terminal := high - totalDrop word last
    level word terminal last 0 = high ∧ lastFloor ≤ terminal ∧
    ∀ i : Fin b, floor i ≤ level word terminal last (i.val+1) := by
  intro terminal
  have hl : lastFloor + ∑ i, floor i ≤ terminal := by dsimp [terminal]; omega
  refine ⟨by rw [start]; dsimp [terminal]; omega,by omega,?_⟩
  intro i
  have hi : floor i ≤ ∑ i, floor i := single_le_sum (f := floor) (fun i _ => Nat.zero_le _) (mem_univ _)
  exact (show floor i ≤ terminal by omega).trans (terminal_le word _ _ _)

end Levels
end Shortening.Adaptive

end BorderVNP
end Computability
end OAI
