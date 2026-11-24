import OAI.Computability.VPVNP.StructuredStacks

/-! # Stop bounds through deterministic prefixes of the transcript validator

A deterministic parser consumes a known number of steps before entering the
nondeterministic part of the validator. At that point every accepting or rejecting
branch has its own path length. A common bound on all leaves permits any larger
clock to be used without changing the path count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

variable {K Q : Type*} [DecidableEq K] {code : StackCode K Q}

/-- The normal stop budget of a deterministic prefix is added to the budget at its exit. -/
theorem StackRuns.stopsWithin_iff {n q s u v} (h : StackRuns code n q s u v) (fuel : ℕ) :
    StopsWithin code (fuel+n) q s ↔ StopsWithin code fuel u v := by
  induction h with
  | nil => rfl
  | cons hs _ ih => cases hs <;> simp_all [StopsWithin]

theorem StopsWithin.mono {n m : ℕ} (hnm : n ≤ m) {q : Q} {s : Stacks K}
    (h : StopsWithin code n q s) : StopsWithin code m q s := by
  induction n generalizing m q s with
  | zero => exact h.elim
  | succ n ih =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    cases he : code q <;> simp only [StopsWithin, he] at h ⊢
    · exact ih (by omega) h
    · exact ih (by omega) h
    · exact ih (by omega) h
    · exact ⟨ih (by omega) h.1, ih (by omega) h.2⟩

/-- Once every leaf has halted, enlarging the budget preserves the entire multiplicity. -/
theorem StopsWithin.stackPaths_eq {n m : ℕ} (hnm : n ≤ m) {q : Q} {s : Stacks K}
    (h : StopsWithin code n q s) : stackPaths code m q s = stackPaths code n q s := by
  induction n generalizing m q s with
  | zero => exact h.elim
  | succ n ih =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    cases he : code q <;> simp only [StopsWithin, he] at h <;> simp only [stackPaths, he]
    · exact ih (by omega) h
    · exact ih (by omega) h
    · exact ih (by omega) h
    · exact congrArg₂ (· + ·) (ih (by omega) h.1) (ih (by omega) h.2)

end RAMTape

end VPVNP
end Computability
end OAI
