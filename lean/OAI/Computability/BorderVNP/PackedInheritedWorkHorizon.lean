import OAI.Computability.BorderVNP.PackedSelectedEpochNodeFrames
import OAI.Computability.BorderVNP.PackedHistoryNormalizedProcessor
import OAI.Computability.BorderVNP.PackedBankOuterInnerCaps

/-! # Uniform site rectangles and expanded-record word budgets for the width compiler -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.StaticRows
open Packing PublicCapacity EnrichedOuter InheritedBank TeamScales
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
variable {start T w : ℕ}

/-- The site identifiers needed by the inherited-width compiler. They depend solely on
the public schedule and its allocated rectangles. -/
structure WidthRanges (S : SiteSchedule e) (start T w : ℕ) : Prop where
  initial : ∀ t, t<T → (before S start t 0).sites ≤ 2^w
  successor : ∀ t, t<T → ∀ i : Fin S.rounds, (before S start t (i.val+1)).sites ≤ 2^w

/-- The actual selected range certificate supplies the site word fits. -/
theorem WidthRanges.of_ranges {r n : ℕ} {den cut : Fin S.rounds → ℕ}
    (ranges : ∀ t, t<T → ∀ i : Fin S.rounds, Ranges S r n start t i (den i) (cut i)) :
    WidthRanges S start T (60*logWidth r n) :=
  ⟨fun t ht => (boundary_fits S (ranges t ht)).1,
   fun t ht i => (ranges t ht i).words.2.2.2.2.2.2.1⟩

/-- The selected site directory has one slot for each template birth at each actual seed.
The seed cardinality here is the cardinality of the source node's literal index type. -/
theorem width_rectangle (deep : S.floor+1+S.drop*T ≤ start) {t : ℕ} (ht : t<T) (i : Fin S.rounds) :
    (before S start t (i.val+1)).sites = siteCapacity e (S.fanIn*(before S start t i.val).sites)
      (Fintype.card (PublicDenseReceipt.Seed (S.source.pattern i).bins
        (S.source.asPath.depth S.last (S.high (offset S start t)) (i.val+1)))) := by
  change _ = siteCapacity e _ (S.source.stageSeeds S.last (S.high (offset S start t)) i)
  rw [stageSeeds_offset S deep ht i,before_next]
  rfl

/-- Expanded budget at a partial internal depth, including the initial true subdivision. -/
noncomputable def widthBudget (B j : ℕ) : ℕ :=
  (1+∑ i, loadMultiplier e*(S.source.pattern i).record*S.fanIn)^j*
    (1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) × Fin (hopCount S.budget S.radius)))*B)

/-- One positive true budget per internal depth. -/
theorem widthBudget_pos {B : ℕ} (hB : 0<B) (j : ℕ) : 0 < widthBudget S B j := by
  unfold widthBudget
  positivity

/-- The fixed budget grows by at least the measured multiplier of this one active stage. -/
theorem widthBudget_step (B : ℕ) (i : Fin S.rounds) :
    loadMultiplier e*(S.source.pattern i).record*S.fanIn*widthBudget S B i.val ≤ widthBudget S B (i.val+1) := by
  let f := fun a : Fin S.rounds => loadMultiplier e*(S.source.pattern a).record*S.fanIn
  have one : f i ≤ 1+∑ a, f a :=
    (Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (Nat.le_add_left _ _)
  apply (Nat.mul_le_mul_right (widthBudget S B i.val) one).trans_eq
  unfold widthBudget
  rw [pow_succ']
  dsimp only [f]
  ac_rfl

/-- All partial internal depths fit the same horizon-wide bound. -/
theorem widthBudget_horizon (B : ℕ) {t j : ℕ} (ht : t<T) (hj : j ≤ S.rounds) :
    widthBudget S (S.publicProgramFactor^t*B) j ≤ S.publicProgramFactor^T*B := by
  have step := S.partialProgramFactor_le j hj (S.publicProgramFactor^t*B)
  have pos : 0 < S.publicProgramFactor := by
    unfold SiteSchedule.publicProgramFactor SiteSchedule.bankRecordFactor epochRecordFactor
    positivity
  apply step.trans
  rw [←Nat.mul_assoc,←pow_succ']
  exact Nat.mul_le_mul_right B (Nat.pow_le_pow_right pos ht)

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
