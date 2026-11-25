import OAI.Computability.BorderVNP.CrossingIntegral

/-!
# Indexing the shared occupation state

Section 4.2 numbers the subsets of odd mode weights below a budget. The numbering puts subsets
which omit the largest available mode first. Both directions use the include-or-exclude counts
computed by dynamic programming. `row` stores its counts in an array-backed `Vector`. A call
at `k` modes and budget `b` constructs `k + 1` rows of `b + 1` cells. Each cell needs at most
`k + 1` bits. Ranking or unranking makes at most one such call at each available mode.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.StateIndex

open Lemmata.FockCircuits
open VPVNP.Crossing (cutoffCount)

/-- The include-or-exclude specification. -/
private def completions : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, b => completions k b + if 2 * k + 1 ≤ b then completions k (b - (2 * k + 1)) else 0

/-- Counts at all residual budgets up to `B`, after processing modes below `k`. -/
def row (B : ℕ) : ℕ → Vector ℕ (B + 1)
  | 0 => Vector.replicate (B + 1) 1
  | k + 1 =>
    let prev := row B k
    Vector.ofFn fun b => prev[b.val] + if 2 * k + 1 ≤ b.val then
      prev[b.val - (2 * k + 1)]'(by omega) else 0

private theorem row_eq (B k : ℕ) (b : Fin (B + 1)) : (row B k)[b.val] = completions k b.val := by
  induction k generalizing b with
  | zero => simp [row, completions]
  | succ k ih =>
    rw [row, Vector.getElem_ofFn, completions, ih b]
    split_ifs with hb
    · exact congrArg (completions k b.val + ·) (ih ⟨_, by omega⟩)
    · rfl

/-- Number of subsets available at one residual budget, computed by tabulating rows. -/
def count (k b : ℕ) : ℕ := (row b k)[b]

private theorem count_eq (k b : ℕ) : count k b = completions k b := row_eq b k ⟨b, by omega⟩

private theorem count_zero (b : ℕ) : count 0 b = 1 := by rw [count_eq]; rfl

private theorem count_succ (k b : ℕ) : count (k + 1) b = count k b +
    if 2 * k + 1 ≤ b then count k (b - (2 * k + 1)) else 0 := by
  simp only [count_eq, completions]

/-- The count in a cell fits in at most `k + 1` binary digits. -/
theorem count_bound (k b : ℕ) : count k b ≤ 2 ^ k := by
  induction k generalizing b with
  | zero => rw [count_zero, pow_zero]
  | succ k ih =>
    rw [count_succ, pow_succ, Nat.mul_two]
    apply Nat.add_le_add (ih _) _
    split_ifs <;> first | exact ih _ | exact Nat.zero_le _

/-- Rank of a subset among the admissible subsets of the first `k` modes. -/
def rank : ℕ → ℕ → Finset ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, b, S =>
    if k ∈ S then count k b + rank k (b - (2 * k + 1)) (S.erase k) else rank k b S

/-- Decode a rank by testing each mode against the size of the branch which omits it. -/
def unrank : ℕ → ℕ → ℕ → Finset ℕ
  | 0, _, _ => ∅
  | k + 1, b, r =>
    let skip := count k b
    if r < skip then unrank k b r else insert k (unrank k (b - (2 * k + 1)) (r - skip))

private def Admissible (k b : ℕ) (S : Finset ℕ) := S ⊆ Finset.range k ∧ doubledEnergy S ≤ b

private theorem pivot_absent {k b : ℕ} {S : Finset ℕ} (h : Admissible k b S) : k ∉ S :=
  fun hmem => Nat.lt_irrefl _ (Finset.mem_range.mp (h.1 hmem))

private theorem admissible_insert {k b : ℕ} {S : Finset ℕ}
    (hb : 2 * k + 1 ≤ b) (h : Admissible k (b - (2 * k + 1)) S) : Admissible (k+1) b (insert k S) := by
  constructor
  · rw [Finset.range_add_one]
    exact Finset.insert_subset_insert _ h.1
  · have he : doubledEnergy (insert k S) = 2*k+1 + doubledEnergy S :=
      Finset.sum_insert (pivot_absent h)
    have := h.2
    omega

private theorem admissible_erase {k b : ℕ} {S : Finset ℕ} (h : Admissible (k+1) b S) (hk : k ∈ S) :
    2 * k + 1 ≤ b ∧ Admissible k (b - (2 * k + 1)) (S.erase k) := by
  have he : doubledEnergy (S.erase k) + (2 * k + 1) = doubledEnergy S := S.sum_erase_add _ hk
  have := h.2
  refine ⟨by omega, ?_, by omega⟩
  intro i hi
  obtain ⟨hi', hiS⟩ := Finset.mem_erase.mp hi
  have := Finset.mem_range.mp (h.1 hiS)
  exact Finset.mem_range.mpr (by omega)

private theorem unrank_spec (k b r : ℕ) (hr : r < count k b) :
    Admissible k b (unrank k b r) ∧ rank k b (unrank k b r) = r := by
  induction k generalizing b r with
  | zero =>
    rw [count_zero] at hr
    simp [Admissible, unrank, rank, doubledEnergy, show r = 0 by omega]
  | succ k ih =>
    rw [unrank]
    by_cases hskip : r < count k b
    · rw [ite_eq_left hskip]
      obtain ⟨h, he⟩ := ih b r hskip
      exact ⟨⟨h.1.trans (Finset.range_mono (by omega)), h.2⟩, by rw [rank, ite_eq_right (pivot_absent h), he]⟩
    · rw [ite_eq_right hskip]
      rw [count_succ] at hr
      have hb : 2 * k + 1 ≤ b := by
        by_contra h
        rw [ite_eq_right h] at hr
        omega
      rw [ite_eq_left hb] at hr
      obtain ⟨h, he⟩ := ih (b - (2 * k + 1)) (r - count k b) (by omega)
      refine ⟨admissible_insert hb h, ?_⟩
      rw [rank, ite_eq_left (Finset.mem_insert_self _ _), Finset.erase_insert (pivot_absent h), he]
      omega

private theorem rank_spec (k b : ℕ) (S : Finset ℕ) (h : Admissible k b S) :
    rank k b S < count k b ∧ unrank k b (rank k b S) = S := by
  induction k generalizing b S with
  | zero =>
    have hS : S = ∅ := Finset.subset_empty.mp h.1
    simp [rank, unrank, count_zero, hS]
  | succ k ih =>
    rw [rank, count_succ]
    by_cases hk : k ∈ S
    · rw [ite_eq_left hk]
      obtain ⟨hb, h'⟩ := admissible_erase h hk
      obtain ⟨hlt, he⟩ := ih _ _ h'
      rw [ite_eq_left hb]
      exact ⟨by omega, by simp [unrank, he, Finset.insert_erase hk]⟩
    · rw [ite_eq_right hk]
      have hs := h.1
      rw [Finset.range_add_one, Finset.subset_insert_iff_of_notMem hk] at hs
      obtain ⟨hlt, he⟩ := ih b S ⟨hs, h.2⟩
      exact ⟨by omega, by simp [unrank, hlt, he]⟩

private theorem state_admissible {E : ℕ} (S : EnergyState E) : Admissible E (2*E) S.val :=
  ⟨Finset.mem_powerset.mp (CrossingCircuit.cutoffEmbedding (E := E) le_rfl S).property,
    mem_fullCutoff.mp S.property⟩

private def stateEquiv (E : ℕ) : EnergyState E ≃ Fin (count E (2*E)) where
  toFun S := ⟨rank E (2*E) S.val, (rank_spec _ _ _ (state_admissible S)).1⟩
  invFun r := ⟨unrank E (2*E) r.val, mem_fullCutoff.mpr (unrank_spec _ _ _ r.isLt).1.2⟩
  left_inv S := Subtype.ext (rank_spec _ _ _ (state_admissible S)).2
  right_inv r := Fin.ext (unrank_spec _ _ _ r.isLt).2

/-- The dynamic-programming count agrees with the number `Q(E)` in the crossing. -/
theorem count_eq_cutoff (E : ℕ) : count E (2*E) = cutoffCount (2*E) := by
  simpa only [Fintype.card_fin, energyState_card] using (Fintype.card_congr (stateEquiv E)).symm

/-- Executable rank/unrank equivalence for the final shared state wire. -/
def energyStateEquiv (E : ℕ) : EnergyState E ≃ Fin (cutoffCount (2*E)) :=
  (stateEquiv E).trans (finCongr (count_eq_cutoff E))

end Crossing.StateIndex

end BorderVNP
end Computability
end OAI
