import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetInput
import OAI.Computability.NearSquareRoot.FixedCandidateTuples

/-! # A common accounting function for the emitted fixed-candidate stages -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedPermutationBudget
open IntegerMultiplication FixedCandidate FixedLayer SynchronizedLayers Filter
open DigitPacking IntegerMultiplication.Code EffectiveBoundedTask

/-- A finite list can include both directions of every permutation, the Walsh
commands and both CRT commands. Repetitions in the list preserve the bounds. -/
def sumAt {L P : Type*} (stages : List L) (f : L → P → ℕ → ℕ) (p : P) (n : ℕ) :=
  (stages.map fun l => f l p n).sum

def commonArena {L P : Type*} (stages : List L) (s : L → P → ℕ → ℕ) (p : P) (n : ℕ) :=
  n+sumAt stages s p n

def commonClock {L P : Type*} (stages : List L) (s t : L → P → ℕ → ℕ) (p : P) (n : ℕ) :=
  commonArena stages s p n+phaseClock n+sumAt stages t p n

private theorem le_sumAt {L P : Type*} (stages : List L) {l : L} (hl : l ∈ stages)
    (f : L → P → ℕ → ℕ) (p : P) (n : ℕ) : f l p n ≤ sumAt stages f p n := by
  induction stages with
  | nil => simp at hl
  | cons a t ih =>
    rcases List.mem_cons.mp hl with eq | mem
    · subst a; simp [sumAt]
    · exact (ih mem).trans (Nat.le_add_left ..)

theorem common_bounds {L P : Type*} (stages : List L) (s t : L → P → ℕ → ℕ) (p : P) (n : ℕ) :
    n ≤ commonArena stages s p n ∧ commonArena stages s p n ≤ commonClock stages s t p n ∧
      phaseClock n ≤ commonClock stages s t p n := by
  unfold commonArena commonClock
  exact ⟨Nat.le_add_right .., (Nat.le_add_right ..).trans (Nat.le_add_right ..),
    (Nat.le_add_left ..).trans (Nat.le_add_right ..)⟩

theorem individual_bounds {L P : Type*} (stages : List L) {l : L} (hl : l ∈ stages)
    (s t : L → P → ℕ → ℕ) (p : P) (n : ℕ) :
    s l p n ≤ commonArena stages s p n ∧ t l p n ≤ commonClock stages s t p n :=
  ⟨(le_sumAt stages hl s p n).trans (Nat.le_add_left ..),
   (le_sumAt stages hl t p n).trans (Nat.le_add_left ..)⟩

def LinearArena (s : ℕ → ℕ) : Prop := ∃ C : ℕ, ∀ᶠ n in atTop, s n ≤ C*(n+1)

private theorem linear_add {f g : ℕ → ℕ} (hf : LinearArena f) (hg : LinearArena g) :
    LinearArena (fun n => f n+g n) := by
  obtain ⟨C,c⟩ := hf
  obtain ⟨D,d⟩ := hg
  refine ⟨C+D,?_⟩
  filter_upwards [c,d] with n h k
  exact (Nat.add_le_add h k).trans_eq (Nat.add_mul ..).symm

private theorem sum_linear {L P : Type*} (stages : List L) (s : L → P → ℕ → ℕ) (p : P)
    (hs : ∀ l ∈ stages, LinearArena (s l p)) : LinearArena (sumAt stages s p) := by
  induction stages with
  | nil => exact ⟨0,Eventually.of_forall fun n => by simp [sumAt]⟩
  | cons a tail ih =>
    exact linear_add (hs a (List.mem_cons_self ..)) (ih (fun l h => hs l (List.mem_cons_of_mem _ h)))

theorem common_linear {L P : Type*} (stages : List L) (s : L → P → ℕ → ℕ) (p : P)
    (hs : ∀ l ∈ stages, LinearArena (s l p)) : LinearArena (commonArena stages s p) :=
  linear_add (f := id) ⟨1,Eventually.of_forall fun n => by simp⟩ (sum_linear stages s p hs)

private theorem row_mono {ρ : ℝ} {f g : ℕ → ℕ} (hf : RowClock ρ f) (hg : ∀ᶠ n in atTop, g n ≤ f n) :
    RowClock ρ g := by
  obtain ⟨B,pos,l,h⟩ := hf
  refine ⟨B,pos,l,?_⟩
  filter_upwards [h,hg] with n h hn
  exact (Nat.cast_le.mpr hn).trans h

private theorem linear_clock {ρ : ℝ} (hr : 0 ≤ ρ) {s : ℕ → ℕ} (linear : LinearArena s) :
    RowClock ρ s := by
  obtain ⟨C,hC⟩ := linear
  obtain ⟨B,pos,l,cost⟩ := RowClock.linear hr
  refine ⟨(2*C)*B,by positivity,l,?_⟩
  filter_upwards [hC,cost,eventually_ge_atTop (1:ℕ)] with n hn hc positive
  have bound := hn.trans (Nat.mul_le_mul_left C (show n+1 ≤ 2*n by omega))
  have natBound : s n ≤ (2*C)*n := bound.trans_eq (by ring)
  have scaled : (s n:ℝ) ≤ (2*C:ℕ)*(n:ℝ) := by exact_mod_cast natBound
  calc
    _ ≤ (2*C:ℕ)*(n:ℝ) := scaled
    _ ≤ (2*C:ℕ)*integerBudget B 0 ρ l 0 n := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by unfold integerBudget; push_cast; ring

private theorem sum_clock {L P : Type*} (stages : List L) (t : L → P → ℕ → ℕ) (p : P) {ρ : ℝ}
    (hr : 0 ≤ ρ) (ht : ∀ l ∈ stages, RowClock ρ (t l p)) : RowClock ρ (sumAt stages t p) := by
  induction stages with
  | nil => exact row_mono (RowClock.linear hr) (Eventually.of_forall fun n => by simp [sumAt])
  | cons a tail ih =>
    exact (ht a (List.mem_cons_self ..)).add (ih (fun l h => ht l (List.mem_cons_of_mem _ h)))

/-- The eventual resource estimates concern just the selected good tuple. All of
the same functions still bound their exact executable on every other tuple. -/
theorem common_good {L P : Type*} (stages : List L) (s t : L → P → ℕ → ℕ) (p : P) {ρ : ℝ}
    (hr : 0 ≤ ρ) (hs : ∀ l ∈ stages, LinearArena (s l p)) (ht : ∀ l ∈ stages, RowClock ρ (t l p)) :
    LinearArena (commonArena stages s p) ∧ RowClock ρ (commonClock stages s t p) := by
  have area := common_linear stages s p hs
  exact ⟨area,((linear_clock hr area).add (phaseClock_bound hr)).add (sum_clock stages t p hr ht)⟩

/-- Widen a row's two certified resource functions simultaneously, leaving its
file and resulting array fixed. -/
theorem promote_row {P : Type} [Primcodable P] {I : P → Type} (n : ∀ p, I p → ℕ)
    (hv : ∀ p i, Directory (n p i)) (dir : ∀ p, I p → Bool)
    (hd : ∀ p i, 4 ≤ (box (n p i)).length) (kind : Kind) {L : Type*}
    (stages : List L) {l : L} (hl : l ∈ stages) (s t : L → P → ℕ → ℕ)
    (run : EffectiveImplementsAt n hv dir hd (s l) (t l) kind) :
    EffectiveImplementsAt n hv dir hd (commonArena stages s) (commonClock stages s t) kind := by
  obtain ⟨y,cmd,err⟩ := run
  exact ⟨y,cmd.mono (fun p e => (individual_bounds stages hl s t p (n p e.val.instanceIndex)).2)
    (fun p e => (individual_bounds stages hl s t p (n p e.val.instanceIndex)).1),err⟩

end SynchronizedPermutationBudget

end NearSquareRoot
end Computability
end OAI
