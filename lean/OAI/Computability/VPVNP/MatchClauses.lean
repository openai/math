import OAI.Computability.VPVNP.HardnessCNF
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators

/-! # Boolean flags for matching finite words

Each match flag is equivalent to a conjunction of prescribed bit values.
There is one binary implication per bit and one clause for the converse.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessCNF

open scoped Classical

variable {k : ℕ} {I : Type*} [Fintype I]

private noncomputable def indices (I : Type*) [Fintype I] : List I :=
  (List.finRange _).map (Fintype.equivFin I).symm

@[simp] private theorem mem_indices (i : I) : i ∈ indices I := by
  simp [indices]
  exact (Fintype.equivFin I).symm.surjective i

@[simp] private theorem length_indices : (indices I).length = Fintype.card I := by
  simp [indices]

/-- Conjunction over a finite index type. -/
noncomputable def meetCNF (c : I → CNF k) : CNF k := (indices I).flatMap c

theorem satisfies_meetCNF (c : I → CNF k) (x : Fin k → Bool) :
    Satisfies (meetCNF c) x ↔ ∀ i, Satisfies (c i) x := by
  simp [Satisfies, meetCNF]
  aesop

theorem literalCount_meetCNF_const (c : I → CNF k) (n : ℕ) (hc : ∀ i, literalCount (c i) = n) :
    literalCount (meetCNF c) = Fintype.card I * n := by
  have h (s : List I) : literalCount (s.flatMap c) = s.length * n := by
    induction s with
    | nil => simp [literalCount]
    | cons i s ih =>
      change literalCount (c i ++ s.flatMap c) = (s.length + 1) * n
      rw [Nat.add_mul, Nat.one_mul, ← ih, ← hc i]
      simp [literalCount, Nat.add_comm]
  simpa [meetCNF] using h (indices I)

/-- A flag is set exactly when the payload bits match the specified word. -/
noncomputable def matchClauses (flag : Fin k) (bit : I → Fin k) (target : I → Bool) : CNF k :=
  ((flag, true) :: (indices I).map (fun i => (bit i, !(target i)))) ::
    (indices I).map (fun i => [(flag, false), (bit i, target i)])

theorem satisfies_matchClauses (flag : Fin k) (bit : I → Fin k) (target : I → Bool)
    (x : Fin k → Bool) :
    Satisfies (matchClauses flag bit target) x ↔ (x flag = true ↔ ∀ i, x (bit i) = target i) := by
  have hneg (i : I) : (x (bit i) = !target i) ↔ x (bit i) ≠ target i := by
    cases x (bit i) <;> cases target i <;> decide
  simp only [Satisfies, matchClauses, List.forall_mem_cons, List.forall_mem_map,
    List.exists_mem_cons_iff, mem_indices, forall_const, List.not_mem_nil, false_and,
    exists_false, or_false]
  have hreverse : (∃ l ∈ (indices I).map (fun i => (bit i, !target i)), x l.1 = l.2) ↔
      ∃ i, x (bit i) ≠ target i := by
    constructor
    · rintro ⟨_, hm, hx⟩
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
      exact ⟨i, (hneg i).mp hx⟩
    · rintro ⟨i, hi⟩
      exact ⟨_, List.mem_map.mpr ⟨i, mem_indices _, rfl⟩, (hneg i).mpr hi⟩
  rw [hreverse]
  cases x flag <;> simp

theorem literalCount_matchClauses (flag : Fin k) (bit : I → Fin k) (target : I → Bool) :
    literalCount (matchClauses flag bit target) = 3 * Fintype.card I + 1 := by
  simp [literalCount, matchClauses, Function.comp_def, Nat.mul_comm]
  omega

end HardnessCNF

end VPVNP
end Computability
end OAI
