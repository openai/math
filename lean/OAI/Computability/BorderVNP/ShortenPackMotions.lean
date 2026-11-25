import OAI.Computability.BorderVNP.ShortenCombiningConcentration
import OAI.Computability.BorderVNP.PackedProfiles
import OAI.Computability.BorderVNP.ShortenEpochConcentration

/-!
# Choosing whole-pack motions from actual sorted bin populations

The chosen motion for a pack acts jointly on all of its cables. Tags of
different input packs remain independent until their disjoint union is
formed. Its integer bin population is exactly the sum of the individual
moved populations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PackMotions

open Crossing Epoch SeedIntervals Packing
open scoped BigOperators Classical

variable {D copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
variable (input : Fin copies → Pack D P bits K) {A M : Type} [Fintype M]
variable (movedBin : ∀ i, M → (input i).layout.Edge → Option A)

/-- The bin of a cable in the moved disjoint union; its copy tag determines
which of the selected whole-pack motions acts on it. -/
def jointBin (ω : Fin copies → M) : (parallelPacks input).layout.Edge → Option A :=
  fun c => movedBin c.1 (ω c.1) c.2

omit [Fintype M] in
/-- Populations of the moved copies add exactly before matching. -/
theorem joint_count (ω : Fin copies → M) (a : A) :
    count (parallelPacks input).layout (jointBin input movedBin ω) a =
      ∑ i, count (input i).layout (movedBin i (ω i)) a := by
  simp only [count_eq_sum]
  exact Fintype.sum_sigma (fun z : Σ i, (input i).layout.Edge =>
    if movedBin z.1 (ω z.1) z.2 = some a then (input z.1).layout.width z.2 else 0)

/-- The bin mean in (6.2), as the average of the expected actual cable counts. -/
noncomputable def binMean (prob : Fin copies → M → ℝ) (a : A) : ℝ :=
  (∑ i, motionMean prob (fun l m b => (count (input l).layout (movedBin l m) b : ℝ)) i a) / copies

/-- Actual independent whole-pack motions can achieve (6.2) on the disjoint
union's sorted-bin populations. No independence within a pack is required. -/
theorem choose_motions [NeZero copies] [Fintype A] (prob : Fin copies → M → ℝ)
    (hpos : ∀ i m, 0 ≤ prob i m) (hprob : ∀ i, ∑ m, prob i m = 1)
    {tiles radius : ℝ} (ht : 0 ≤ tiles) (hr : 0 ≤ radius)
    (hbound : ∀ i m, tiles * binEnergy (fun a => (count (input i).layout (movedBin i m) a : ℝ)) ≤ radius^2) :
    ∃ ω : Fin copies → M, Real.sqrt tiles *
      Real.sqrt (binEnergy (fun a => count (parallelPacks input).layout (jointBin input movedBin ω) a / copies -
        binMean input movedBin prob a)) ≤ radius / Real.sqrt copies := by
  obtain ⟨ω,hω⟩ := exists_concentrated_motions prob hpos hprob
    (fun i m a => (count (input i).layout (movedBin i m) a : ℝ)) ht hr hbound
  refine ⟨ω, ?_⟩
  simp only [binMean, joint_count, Nat.cast_sum, Fintype.card_fin] at *
  exact hω

variable {Q : Type*} [PseudoMetricSpace Q]

omit [Fintype M] in
/-- Length in the moved disjoint union is the sum of the individual moved
charged lengths. -/
theorem joint_length (ω : Fin copies → M) (place : ∀ i, M → (input i).layout.Site → Q) :
    chargedLength (parallelPacks input).layout (fun v => place v.1 (ω v.1) v.2)
      (fun c => (jointBin input movedBin ω c).isSome) =
      ∑ i, chargedLength (input i).layout (place i (ω i)) (fun c => (movedBin i (ω i) c).isSome) := by
  unfold chargedLength
  exact Fintype.sum_sigma (fun c : Σ i, (input i).layout.Edge =>
    if (movedBin c.1 (ω c.1) c.2).isSome then ((input c.1).layout.width c.2 : ℝ) *
      dist (place c.1 (ω c.1) ((input c.1).layout.src c.2)) (place c.1 (ω c.1) ((input c.1).layout.dst c.2))
    else 0)

end Shortening.PackMotions

end BorderVNP
end Computability
end OAI
