import OAI.Computability.VPVNP.RAMBuckets
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Scheduling the instructions of a team in Lemma 7.1

A processor consumes the longest initial segment fitting its own block. An instruction costs
one tick plus the length of its burst, with zero additional cost for an ordinary instruction.
The payload can include the instruction's private choices and its signed output.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Team

open VPVNP.RAMBuckets (cost cost_append cost_eq_zero_iff)

variable {α : Type*}

/-- Take the longest prefix whose total charge fits the available ticks. -/
def splitBlock (burst : α → ℕ) : ℕ → List α → List α × List α
  | _, [] => ([], [])
  | h, a :: xs => if 1 + burst a ≤ h then
      let rest := splitBlock burst (h - (1 + burst a)) xs
      (a :: rest.1, rest.2)
    else ([], a :: xs)

/-- A processor executes its prefix in full, handing off only when the next call would overflow. -/
def MaximalBlock (burst : α → ℕ) (h : ℕ) (front tail : List α) : Prop :=
  cost burst front ≤ h ∧ ∀ a xs, tail = a :: xs → h < cost burst front + (1 + burst a)

/-- Splitting a block preserves the path and meets both local handoff tests. -/
theorem splitBlock_spec (burst : α → ℕ) (h : ℕ) (xs : List α) :
    let p := splitBlock burst h xs
    p.1 ++ p.2 = xs ∧ MaximalBlock burst h p.1 p.2 := by
  induction xs generalizing h with
  | nil => exact ⟨rfl, Nat.zero_le _, by simp [splitBlock]⟩
  | cons a xs ih =>
    by_cases fits : 1 + burst a ≤ h
    · simp only [splitBlock, fits, ↓reduceIte, List.cons_append]
      obtain ⟨hf, hc, ht⟩ := ih (h - (1 + burst a))
      refine ⟨congrArg (List.cons a) hf, ?_, ?_⟩
      · simp only [cost]; omega
      · intro b ys hy
        have := ht b ys hy
        simp only [cost]; omega
    · simp only [splitBlock, fits, ↓reduceIte, List.nil_append]
      refine ⟨trivial, Nat.zero_le _, ?_⟩
      intro b ys e
      cases e
      simpa only [cost, Nat.zero_add] using Nat.lt_of_not_ge fits

/-- The local handoff tests force the split, including at a halt or an exact boundary. -/
theorem MaximalBlock.eq_splitBlock {burst : α → ℕ} {h : ℕ} {front tail : List α}
    (valid : MaximalBlock burst h front tail) :
    splitBlock burst h (front ++ tail) = (front, tail) := by
  induction front generalizing h with
  | nil =>
    cases tail with
    | nil => rfl
    | cons a xs =>
      have stop := valid.2 a xs rfl
      simp only [cost, Nat.zero_add] at stop
      simp [splitBlock, Nat.not_le.mpr stop]
  | cons a front ih =>
    obtain ⟨bound, stop⟩ := valid
    simp only [cost] at bound stop
    have fits : 1 + burst a ≤ h := by omega
    have tailValid : MaximalBlock burst (h - (1 + burst a)) front tail := by
      refine ⟨by omega, ?_⟩
      intro b ys eq
      have := stop b ys eq
      omega
    simp [splitBlock, fits, ih tailValid]

/-- A nonhalting handoff leaves at most the maximum burst length unused. -/
theorem MaximalBlock.idle_le {burst : α → ℕ} {h maxBurst : ℕ} {front tail : List α}
    (valid : MaximalBlock burst h front tail) (hne : tail ≠ [])
    (bounded : ∀ a ∈ tail, burst a ≤ maxBurst) : h - cost burst front ≤ maxBurst := by
  cases tail with
  | nil => contradiction
  | cons a xs =>
    have hs := valid.2 a xs rfl
    have hb := bounded a (List.mem_cons_self ..)
    omega

/-- Partition a path among consecutive processors, filling empty blocks after a halt. -/
def teamBlocks (burst : α → ℕ) (h : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | r + 1, xs => let p := splitBlock burst h xs
                 p.1 :: teamBlocks burst h r p.2

/-- The local stop rule holds at every processor boundary. -/
def ValidBlocks (burst : α → ℕ) (h : ℕ) : List (List α) → Prop
  | [] => True
  | front :: rest => MaximalBlock burst h front rest.flatten ∧ ValidBlocks burst h rest

@[simp] theorem teamBlocks_length (burst : α → ℕ) (h r : ℕ) (xs : List α) :
    (teamBlocks burst h r xs).length = r := by
  induction r generalizing xs with
  | zero => rfl
  | succ r ih => simp [teamBlocks, ih]

/-- Every path below the effective tick capacity fits, with all private choices preserved. -/
theorem teamBlocks_spec (burst : α → ℕ) (h maxBurst r : ℕ) (xs : List α)
    (bounded : ∀ a ∈ xs, burst a ≤ maxBurst) (cap : cost burst xs ≤ r * (h - maxBurst)) :
    (teamBlocks burst h r xs).flatten = xs ∧ ValidBlocks burst h (teamBlocks burst h r xs) := by
  induction r generalizing xs with
  | zero =>
    have he := (cost_eq_zero_iff burst xs).mp (by simpa using cap)
    subst xs; exact ⟨rfl, trivial⟩
  | succ r ih =>
    let p := splitBlock burst h xs
    obtain ⟨hflat, hblock⟩ : p.1 ++ p.2 = xs ∧ MaximalBlock burst h p.1 p.2 := splitBlock_spec ..
    have htail (a) (ha : a ∈ p.2) : burst a ≤ maxBurst :=
      bounded a (hflat ▸ List.mem_append_right _ ha)
    have restCap : cost burst p.2 ≤ r * (h - maxBurst) := by
      by_cases empty : p.2 = []
      · simp [empty, cost]
      · have idle := hblock.idle_le empty htail
        have total : cost burst p.1 + cost burst p.2 = cost burst xs := by rw [← cost_append, hflat]
        rw [Nat.succ_mul] at cap
        omega
    obtain ⟨flat, valid⟩ := ih p.2 htail restCap
    change p.1 ++ (teamBlocks burst h r p.2).flatten = xs ∧
      MaximalBlock burst h p.1 (teamBlocks burst h r p.2).flatten ∧ _
    rw [flat]; exact ⟨hflat, hblock, valid⟩

/-- The boundary tests uniquely recover the partition from its full path. -/
theorem ValidBlocks.eq_teamBlocks {burst : α → ℕ} {h : ℕ} {blocks : List (List α)}
    (valid : ValidBlocks burst h blocks) : teamBlocks burst h blocks.length blocks.flatten = blocks := by
  induction blocks with
  | nil => rfl
  | cons front rest ih =>
    obtain ⟨hb, hr⟩ := valid
    simp [teamBlocks, hb.eq_splitBlock, ih hr]

/-- Existence and uniqueness of the team schedule at the tick bound of Lemma 7.1. -/
theorem existsUnique_teamBlocks (burst : α → ℕ) (h maxBurst r : ℕ) (xs : List α)
    (bounded : ∀ a ∈ xs, burst a ≤ maxBurst) (cap : cost burst xs ≤ r * (h - maxBurst)) :
    ∃! blocks : List (List α), blocks.length = r ∧ blocks.flatten = xs ∧ ValidBlocks burst h blocks := by
  refine ⟨teamBlocks burst h r xs, ⟨teamBlocks_length .., teamBlocks_spec burst h maxBurst r xs bounded cap⟩, ?_⟩
  rintro bs ⟨hlen, hflat, valid⟩
  simpa [hlen, hflat] using valid.eq_teamBlocks.symm

/-- Multiplying local path weights in execution order preserves the global path weight. -/
theorem prod_block_weights {M : Type*} [Monoid M] (weight : α → M)
    {blocks : List (List α)} {xs : List α} (flat : blocks.flatten = xs) :
    (blocks.map (fun block => (block.map weight).prod)).prod = (xs.map weight).prod := by
  subst xs
  induction blocks with
  | nil => rfl
  | cons front rest ih => simp [ih]

end Team

end BorderVNP
end Computability
end OAI
