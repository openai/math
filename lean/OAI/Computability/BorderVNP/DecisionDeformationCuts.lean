import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.RingTheory.Ideal.Height

/-! # Cutting out an isolated point with one equation per dimension

In the coordinate ring of an affine variety over an extension of an infinite
field, the linear combinations may be chosen over the smaller field. At each
cut we avoid all positive-dimensional components through the given point.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Decision

open scoped BigOperators

variable {K R O : Type*} [Field K] [Infinite K] [CommRing R] [Algebra K R]
  [IsNoetherianRing R] [Fintype O]

/-- Evaluate a ground-field linear combination of the equations in the coordinate ring. -/
def cutCombination (H : O → R) (a : O → K) : R := ∑ j, a j • H j

private theorem combination_avoids (H : O → R) {J m : Ideal R}
    (isolated : m ∈ (Ideal.span (Set.range H)).minimalPrimes) :
    ∃ a : O → K, ∀ P ∈ J.minimalPrimes, P < m → cutCombination H a ∉ P := by
  classical
  let bad := {P : Ideal R | P ∈ J.minimalPrimes ∧ P < m}
  have : Finite bad := ((Ideal.finite_minimalPrimes_of_isNoetherianRing R J).subset
    fun _ h => h.1 : bad.Finite).to_subtype
  let forbidden (P : bad) : Submodule K (O → K) :=
    { carrier := {a | cutCombination H a ∈ P.val}
      zero_mem' := by simp [cutCombination]
      add_mem' := by
        intro a b ha hb
        change cutCombination H (a + b) ∈ P.val
        simpa [cutCombination, add_smul, Finset.sum_add_distrib] using P.val.add_mem ha hb
      smul_mem' := by
        intro c a ha
        change cutCombination H (c • a) ∈ P.val
        rw [show cutCombination H (c • a) = c • cutCombination H a by
          simp [cutCombination, Finset.smul_sum, mul_smul]]
        exact P.val.smul_of_tower_mem c ha }
  have proper (P : bad) : forbidden P ≠ ⊤ := by
    intro e
    have le : Ideal.span (Set.range H) ≤ P.val := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      let δ : O → K := Pi.single (M := fun _ : O => K) j (1 : K)
      have hδ : δ ∈ forbidden P := e ▸ Submodule.mem_top
      change cutCombination H δ ∈ P.val at hδ
      simpa [cutCombination, δ, Pi.single_apply, ite_smul] using hδ
    exact P.property.2.not_ge (isolated.2 ⟨P.property.1.isPrime, le⟩ P.property.2.le)
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top forbidden proper
  exact ⟨a, fun P hP hlt => ha ⟨P, hP, hlt⟩⟩

private theorem cut_height_induction (H : O → R) {m : Ideal R}
    (isolated : m ∈ (Ideal.span (Set.range H)).minimalPrimes) (k : ℕ) :
    ∃ a : Fin k → O → K, let J := Ideal.span (Set.range (fun i => cutCombination H (a i)))
      J ≤ m ∧ ∀ P ∈ J.minimalPrimes, P < m → (k : ℕ∞) ≤ P.height := by
  classical
  induction k with
  | zero =>
    exact ⟨Fin.elim0, Ideal.span_le.mpr (by rintro _ ⟨i, _⟩; exact Fin.elim0 i),
      fun _ _ _ => zero_le⟩
  | succ k ih =>
    obtain ⟨a, hJ, hheight⟩ := ih
    let J := Ideal.span (Set.range (fun i => cutCombination H (a i)))
    obtain ⟨c, hc⟩ := combination_avoids (K := K) (J := J) H isolated
    let a' : Fin (k+1) → O → K := Fin.cons (α := fun _ => O → K) c a
    let J' := Ideal.span (Set.range (fun i => cutCombination H (a' i)))
    have hJJ : J ≤ J' := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span ⟨i.succ, by simp [a']⟩
    have hcJ : cutCombination H c ∈ J' := Ideal.subset_span ⟨0, by simp [a']⟩
    refine ⟨a', ?_, ?_⟩
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact m.sum_mem fun j _ => m.smul_of_tower_mem _ (isolated.le (Ideal.subset_span ⟨j, rfl⟩))
    · intro P hP hPm
      have : P.IsPrime := hP.isPrime
      obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (hJJ.trans hP.le)
      have : Q.IsPrime := hQ.isPrime
      have hQm := hQP.trans_lt hPm
      have hlt : Q < P := lt_of_le_of_ne hQP fun e => hc Q hQ hQm (e ▸ hP.le hcJ)
      simpa only [Nat.cast_succ] using (add_le_add_left (hheight Q hQ hQm) 1).trans
        (Ideal.height_add_one_le_of_lt_of_isPrime hlt)

/-- A point isolated by a system remains isolated by precisely `d` linear
combinations of that system when its maximal ideal has height `d`. The
coefficients are in the ground field even if the equations are over an extension. -/
theorem isolate_by_linear_combinations (H : O → R) (m : Ideal R) {d : ℕ}
    (height : m.height = d) (isolated : m ∈ (Ideal.span (Set.range H)).minimalPrimes) :
    ∃ a : Fin d → O → K,
      m ∈ (Ideal.span (Set.range (fun i => cutCombination H (a i)))).minimalPrimes := by
  obtain ⟨a, hle, hheight⟩ := cut_height_induction (K := K) H isolated d
  have : m.IsPrime := isolated.isPrime
  obtain ⟨P, hP, hPm⟩ := Ideal.exists_minimalPrimes_le hle
  have : P.IsPrime := hP.isPrime
  have he : P = m := by
    by_contra hne
    have hlt := lt_of_le_of_ne hPm hne
    have low := hheight P hP hlt
    have high := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have contra : (d : ℕ∞) + 1 ≤ d := (add_le_add_left low 1).trans (height ▸ high)
    exact (by exact_mod_cast Nat.not_succ_le_self d : ¬ (d : ℕ∞) + 1 ≤ d) contra
  exact ⟨a, he ▸ hP⟩

end Decision

end BorderVNP
end Computability
end OAI
