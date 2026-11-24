import OAI.Computability.VPVNP.RAMTapeNamed
import OAI.Computability.VPVNP.RAMTapeSpace
import OAI.Computability.VPVNP.RAMTapeSpaceLiteral
import Mathlib.Algebra.BigOperators.Fin

/-!
# Reachable space of a named stack bank

Installing a fixed bank of labeled stacks in the physical machine adds one
spare empty port. The size of its packed tape is the number of separators
plus the total bit count in the named stacks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.StackCompiler

open UniversalMachine

variable {K Q : Type*} [DecidableEq K] [Fintype K]

private theorem unique_step {L : Type*} [DecidableEq L] {code : StackCode L Q} {q s a b u v}
    (first : StackStep code q s a u) (second : StackStep code q s b v) : a = b ∧ u = v := by
  cases first <;> cases second <;> simp_all

private theorem reflect_step (input : K) (code : StackCode K Q) (base : Stacks (Fin (Fintype.card K+1)))
    (q : Q) (s : Stacks K) {u t}
    (h : StackStep (labeledCode input code) q (installStacks (labeledPort input) base s) u t) :
    ∃ s', StackStep code q s u s' ∧ t = installStacks (labeledPort input) base s' := by
  have lift {r s'} (small : StackStep code q s r s') :
      ∃ s', StackStep code q s u s' ∧ t = installStacks (labeledPort input) base s' := by
    have big := small.lift (target := labeledCode input code) (labeledPort input)
      (labeledPort_injective input) id base (fun _ _ => rfl)
    obtain ⟨he, ht⟩ := unique_step h big
    exact ⟨s', he.symm ▸ small, ht⟩
  cases hc : code q with
  | push => exact lift (.push hc)
  | pop => exact lift (.pop hc)
  | goto => exact lift (.goto hc)
  | choose | halt => cases h <;> simp_all [labeledCode]

private theorem choice_of_labeled {input : K} {code : StackCode K Q} {q l h}
    (hc : labeledCode input code q = .choose l h) : code q = .choose l h := by
  cases hs : code q <;> simp_all [labeledCode]

/-- All reachable numbered banks have a corresponding reachable named bank. -/
theorem reflect_reach (input : K) (code : StackCode K Q) (start : Q) (s : Stacks K)
    (base : Stacks (Fin (Fintype.card K+1))) {u t}
    (h : Reach (labeledCode input code) start (installStacks (labeledPort input) base s) u t) :
    ∃ s', Reach code start s u s' ∧ t = installStacks (labeledPort input) base s' := by
  induction h with
  | initial => exact ⟨s, .initial, rfl⟩
  | step _ big ih =>
    obtain ⟨s', small, rfl⟩ := ih
    obtain ⟨t', hs, ht⟩ := reflect_step input code base _ s' big
    exact ⟨t', .step small hs, ht⟩
  | low _ ch ih =>
    obtain ⟨s', small, ht⟩ := ih
    exact ⟨s', .low small (choice_of_labeled ch), ht⟩
  | high _ ch ih =>
    obtain ⟨s', small, ht⟩ := ih
    exact ⟨s', .high small (choice_of_labeled ch), ht⟩

theorem packed_length {k : ℕ} (s : Stacks (Fin k)) :
    (packed s).length = k + ∑ p, (s p).length := by
  simp [packed, fields, List.length_flatMap, List.map_ofFn, List.sum_ofFn, Finset.sum_add_distrib, Nat.add_comm]

/-- The one spare physical label is empty at initialization and stays empty. -/
theorem installed_length (input : K) (raw : Word) (s : Stacks K) :
    (packed (installStacks (labeledPort input) (inputStacks raw) s)).length =
      (Fintype.card K+1) + ∑ p, (s p).length := by
  classical
  rw [packed_length]
  congr 1
  let ks := Finset.univ.image (labeledPort input)
  have zero (i : Fin (Fintype.card K+1)) (hi : i ∉ ks) :
      (installStacks (labeledPort input) (inputStacks raw) s i).length = 0 := by
    have hn : ∀ p, labeledPort input p ≠ i := by simpa [ks] using hi
    rw [installStacks_outside _ _ hn]
    have h0 := hn input
    simp [labeledPort] at h0
    cases i using Fin.cases with
    | zero => exact (h0 rfl).elim
    | succ j => simp [inputStacks]
  rw [← Finset.sum_subset (Finset.subset_univ ks) (fun i _ hi => zero i hi)]
  rw [Finset.sum_image (labeledPort_injective input).injOn]
  simp [installStacks_at (labeledPort_injective input)]

/-- A size invariant on reachable named banks bounds every packed physical
instruction boundary, starting on the raw input tape. -/
theorem named_reach_packed_le (input : K) (code : StackCode K Q) (start : Q) (raw : Word) {M : ℕ}
    (bounded : ∀ ⦃q s⦄, Reach code start (labeledInput input raw) q s →
      Fintype.card K+1 + ∑ p, (s p).length ≤ M) {q t}
    (h : Reach (labeledCode input code) start (inputStacks raw) q t) : (packed t).length ≤ M := by
  have he : installStacks (labeledPort input) (inputStacks raw) (labeledInput input raw) = inputStacks raw := by
    apply installStacks_eq (labeledPort_injective input)
    intro p
    by_cases hp : p = input <;> simp [hp, labeledPort, inputStacks, labeledInput]
  rw [← he] at h
  obtain ⟨s, hs, rfl⟩ := reflect_reach _ _ _ _ _ h
  rw [installed_length]
  exact bounded hs

variable [Fintype Q]

/-- The two literal table heads stay in a fixed interval for every prefix
of witness bits, including padded execution after a halt. -/
theorem input_space {k : ℕ} (code : StackCode (Fin (k+1)) Q) (start : Q) (raw : Word) {M : ℕ}
    (bounded : ∀ ⦃q s⦄, Reach code start (inputStacks raw) q s → (packed s).length ≤ M)
    (bits : List Bool) :
    let d := choiceDisplacement (program code start) (initial (program code start) raw) bits
    HeadBox (7*M+4) d.1 d.2 := by
  rw [physical_initial]
  obtain ⟨_, _, _, _, _, hp⟩ := choiceDisplacement_path (.ready start) (rows code) (.ready start)
    (tapeList (packed (inputStacks raw))) (tapeList []) bits
  exact headPath_space start (inputStacks raw) bounded hp

/-- A bound on the total reachable bit count of the evaluator's named stack
bank gives a time-independent space bound for the compiled universal program. -/
theorem input_space_labeled (input : K) (code : StackCode K Q) (start : Q) (raw : Word) {M : ℕ}
    (bounded : ∀ ⦃q s⦄, Reach code start (labeledInput input raw) q s →
      Fintype.card K+1 + ∑ p, (s p).length ≤ M) (bits : List Bool) :
    let program := labeledProgram input code start
    let d := choiceDisplacement program (initial program raw) bits
    HeadBox (7*M+4) d.1 d.2 :=
  input_space (labeledCode input code) start raw (fun ⦃_ _⦄ h => named_reach_packed_le input code start raw bounded h) bits

end RAMTape.StackCompiler

end VPVNP
end Computability
end OAI
