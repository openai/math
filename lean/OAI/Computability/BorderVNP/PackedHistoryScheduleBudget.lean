import OAI.Computability.BorderVNP.PackedHistoryBoundaryBudget
import OAI.Computability.BorderVNP.PackedSelectedScheduleRanges

/-! # Sparse arrays throughout the calibrated history of the actual bottom grid -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Epoch Packing Shortening PublicCapacity Diagonal TeamScales Filter VPVNP.VerifierNetwork
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- The actual reserved rectangle at the boundary below outer level t. -/
noncomputable def boundary (start t : ℕ) : Shape :=
  epochRows e S.fanIn S.rounds (interiors S) (seedCount S start) (bottom (D := D) start) t

/-- Both boundaries and every input subdivision fit the processor address range. -/
theorem eventually_boundaries {a x : ℕ} (s : EpochScales S a x) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      let start := CoverScale.initialDepth (Cube D) r n
      let V := CoverScale.sites (Cube D) start
      let T := epochs s.τ n
      (∀ t ≤ T, (boundary S start t).volume V ≤ r*n) ∧
      ∀ t < T, ((boundary S start t).subdivide (interiors S)).volume V ≤ r*n := by
  let dirs := Fintype.card (DeckGrid.Direction (Fintype.card (Cube D)))
  let g := PublicCapacity.epochFactor e S.fanIn S.rounds (interiors S) (bins S)
  have hg : 1 ≤ g := epochFactor_pos e S.positiveFanIn _ _ _
  have hτ : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have gr : (s.τ:ℝ)*Real.logb 2 g ≤ (s.α:ℝ)/10 := s.rate hg (epochGrowth_bounds S x).2.2.2.2.1
  have all := eventually_rectangle_range s.alpha_small hτ.le hg gr (dirs+3)
  filter_upwards [all, eventually_grid_volume (Cube D) dirs, eventually_ranges S s (fun _ => 0) (fun _ => 0)]
    with n hmax hbottom hrange
  intro r hr start V T
  have hs := (hrange r hr).1
  have cap : g^T*(bottom (D := D) start).volume V ≤ r*n := hmax r _ (hbottom r hr)
  constructor
  · intro t ht
    exact (epochRows_le e S.positiveFanIn _ _ V _ _ hs (bottom (D := D) start) t).trans
      ((Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hg ht)).trans cap)
  · intro t ht
    let sub := (boundary S start t).subdivide (interiors S)
    have bound : (sub.parallel S.fanIn).volume V ≤ g^T*(bottom (D:=D) start).volume V :=
      joinedRows_le e S.positiveFanIn _ _ V _ _ hs _ ht S.rounds_pos
    have hsite := Nat.le_mul_of_pos_left sub.sites S.positiveFanIn
    have hedge := Nat.le_mul_of_pos_left sub.edges S.positiveFanIn
    have mono : sub.volume V ≤ (sub.parallel S.fanIn).volume V := by
      dsimp only [Shape.volume,Shape.parallel]
      omega
    exact mono.trans (bound.trans cap)

/-- On the fixed site schedule the actual calibrated copy and rectangular
growth rates pay for the entire accepted-word circuit and all of its count
pins, including every boundary pass and every repeated bottom input. -/
theorem eventually_schedule_history {a x : ℕ} (s : EpochScales S a x) (C exponent Q : ℕ) :
    ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ) ≤ 2^((n:ℝ)^ω) →
      let T := epochs s.τ n
      let start := CoverScale.initialDepth (Cube D) r n
      let V := CoverScale.sites (Cube D) start
      ∀ (σ : Type) [Fintype σ] (O : ℕ → Type) (W G : ℕ → ℕ → Type)
        [∀ t, Fintype (O t)] [∀ t j, Fintype (W t j)] [∀ t j, Fintype (G t j)]
        (f : Frame σ (O 0)) (inner : ∀ t, t<T → Steps S.fanIn S.rounds (W t) (G t))
        (pre : ∀ t, t<T → Frame (Fin (S.fanIn^S.rounds) × O t) (Fin (S.fanIn^S.rounds) × W t 0))
        (post : ∀ t, t<T → Frame ((Fin (S.fanIn^S.rounds) × O t) ⊕ W t S.rounds) (O (t+1))),
        RectangleWork e (interiors S) V (logWidth r n) C exponent (seedCount S start) (bottom (D:=D) start) f inner pre post →
        ((Q*(compile (nestedSteps inner pre post) T le_rfl (repeatLeaf (S.fanIn^S.rounds) f T)).size +
          Fintype.card (Slot (S.fanIn^S.rounds) (fun t => Slot S.fanIn (G t) S.rounds) T) : ℕ) : ℝ) <
          r*(n:ℝ)^(92/100:ℝ) := by
  have hτ : 0<(s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have copies := s.rate (epochCopies_pos S) (epochGrowth_bounds S x).2.1
  have growth := s.rate (epochFactor_pos e S.positiveFanIn S.rounds (interiors S) (bins S))
    (epochGrowth_bounds S x).2.2.2.2.1
  have ht : (s.τ:ℝ)*Real.logb 2 (S.fanIn^S.rounds : ℕ) ≤ (s.α:ℝ) :=
    copies.trans (by linarith [show 0 < (s.α:ℝ) by exact_mod_cast s.alpha_pos])
  obtain ⟨ω,hω,work⟩ := eventually_rectangular_history_92 e (interiors S) (bins S) C exponent Q
    s.alpha_small hτ s.tau_small S.positiveFanIn ht growth
  let dirs := Fintype.card (DeckGrid.Direction (Fintype.card (Cube D)))
  refine ⟨ω,hω,?_⟩
  filter_upwards [work (dirs+3) (by positivity),eventually_grid_volume (Cube D) dirs,
    eventually_ranges S s (fun _ => 0) (fun _ => 0)] with n bound bottomBound ranges
  intro r hr hr' T start V
  exact bound r hr hr' V (seedCount S start) (bottom (D:=D) start) (ranges r hr).1 (bottomBound r hr)

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
