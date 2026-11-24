import Mathlib.Data.Set.PowersetCard
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.RingTheory.Finiteness.Basic

/-!
# The isolated minimum-weight basis in the rank query

Appendix D.2 of *VP and VNP differ over every field* assigns a row or column
its one-based index as a weight. Keeping exactly the vectors that increase the
span on a left-to-right scan gives the unique minimum-weight basis. The proof
uses prefix ranks and applies over every field, also when the rank is zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery

open scoped BigOperators

private theorem prefix_weight_balance {n : ℕ} (s : Finset (Fin n)) :
    (∑ i ∈ s, (i.val + 1)) + (∑ j : Fin n, (s.filter (· ≤ j)).card) =
      s.card * (n + 1) := by
  classical
  have hcount (i : Fin n) : (∑ j : Fin n, if i ≤ j then 1 else 0) = n - i.val := by
    rw [← Finset.card_filter]
    have h : Finset.univ.filter (fun j : Fin n => i ≤ j) = Finset.Ici i := by ext; simp
    rw [h, Fin.card_Ici]
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm (s := Finset.univ) (t := s)]
  simp_rw [hcount]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _i ∈ s, (n + 1) := Finset.sum_congr rfl fun i _ => by have := i.isLt; omega
    _ = _ := by simp

private theorem eq_of_prefix_counts {n : ℕ} {s t : Finset (Fin n)}
    (h : ∀ j : Fin n, (s.filter (· ≤ j)).card = (t.filter (· ≤ j)).card) :
    s = t := by
  classical
  ext j
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hlt : s.filter (· < j) = t.filter (· < j) := by
      ext i
      by_cases hi : i < j
      · simp [hi, ih i hi]
      · simp [hi]
    have count (u : Finset (Fin n)) :
        (u.filter (· ≤ j)).card = (u.filter (· < j)).card + if j ∈ u then 1 else 0 := by
      by_cases hj : j ∈ u
      · have hu : u.filter (· ≤ j) = insert j (u.filter (· < j)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_insert]
          grind
        simp [hu, hj]
      · have hu : u.filter (· ≤ j) = u.filter (· < j) := by
          ext i
          simp only [Finset.mem_filter]
          grind
        simp [hu, hj]
    have he := h j
    rw [count s, count t, hlt] at he
    by_cases hs : j ∈ s <;> by_cases ht : j ∈ t <;> simp_all

/-- At fixed cardinality, domination of every prefix count strictly lowers the sum of
one-based indices unless the two sets coincide. -/
theorem weight_lt_of_prefix_dominance {n r : ℕ} {S T : Set.powersetCard (Fin n) r}
    (hdom : ∀ j : Fin n, (T.val.filter (· ≤ j)).card ≤ (S.val.filter (· ≤ j)).card)
    (hne : S ≠ T) : (∑ i ∈ S.val, (i.val + 1)) < ∑ i ∈ T.val, (i.val + 1) := by
  classical
  have hstrict : ∃ j : Fin n, (T.val.filter (· ≤ j)).card < (S.val.filter (· ≤ j)).card := by
    by_contra! he
    exact hne (Subtype.ext (eq_of_prefix_counts (fun j => (he j).antisymm (hdom j))))
  obtain ⟨j, hj⟩ := hstrict
  have hsum : (∑ i : Fin n, (T.val.filter (· ≤ i)).card) <
      ∑ i : Fin n, (S.val.filter (· ≤ i)).card :=
    Finset.sum_lt_sum (fun i _ => hdom i) ⟨j, Finset.mem_univ _, hj⟩
  have hs := prefix_weight_balance S.val
  have ht := prefix_weight_balance T.val
  have hcard : S.val.card = T.val.card := S.property.trans T.property.symm
  rw [hcard] at hs
  omega

variable (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {n : ℕ} (v : Fin n → V)

/-- Retain a row exactly when it increases the span of its predecessors. -/
noncomputable def greedyIndices : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => v i ∉ Submodule.span K (v '' Set.Iio i))

@[simp] theorem mem_greedyIndices (i : Fin n) :
    i ∈ greedyIndices K v ↔ v i ∉ Submodule.span K (v '' Set.Iio i) := by
  classical
  simp [greedyIndices]

/-- On each prefix the retained rows form an independent spanning family. -/
theorem greedyIndices_prefix (k : ℕ) :
    LinearIndepOn K v ((greedyIndices K v : Set (Fin n)) ∩ {i | i.val < k}) ∧
      Submodule.span K (v '' ((greedyIndices K v : Set (Fin n)) ∩ {i | i.val < k})) =
        Submodule.span K (v '' {i | i.val < k}) := by
  classical
  induction k with
  | zero => simp [linearIndepOn_empty]
  | succ k ih =>
    by_cases hk : k < n
    · let j : Fin n := ⟨k, hk⟩
      have hnext : {i : Fin n | i.val < k + 1} = insert j {i | i.val < k} := by
        ext i
        change i.val < k + 1 ↔ i = j ∨ i.val < k
        simp only [Fin.ext_iff, j]
        omega
      have hprev : Set.Iio j = {i : Fin n | i.val < k} := rfl
      rw [hnext, Set.image_insert_eq]
      by_cases hj : j ∈ (greedyIndices K v : Set (Fin n))
      · have hnew := (mem_greedyIndices K v j).mp hj
        rw [hprev] at hnew
        rw [Set.inter_insert_of_mem hj, Set.image_insert_eq]
        constructor
        · apply (linearIndepOn_insert ?_).mpr
          · exact ⟨ih.1, ih.2 ▸ hnew⟩
          · exact fun h => lt_irrefl k h.2
        · rw [Submodule.span_insert, Submodule.span_insert, ih.2]
      · have hdep : v j ∈ Submodule.span K (v '' {i : Fin n | i.val < k}) := by
          by_contra hn
          exact hj ((mem_greedyIndices K v j).mpr (hprev ▸ hn))
        rw [Set.inter_insert_of_notMem hj, Submodule.span_insert_eq_span hdep]
        exact ih
    · have hsame : {i : Fin n | i.val < k + 1} = {i | i.val < k} := by
        ext i
        have hi := i.isLt
        change i.val < k + 1 ↔ i.val < k
        omega
      rwa [hsame]

theorem greedyIndices_span_prefix (k : ℕ) :
    Submodule.span K (v '' ((greedyIndices K v : Set (Fin n)) ∩ {i | i.val < k})) =
      Submodule.span K (v '' {i | i.val < k}) :=
  (greedyIndices_prefix K v k).2

theorem greedyIndices_linearIndepOn :
    LinearIndepOn K v (greedyIndices K v : Set (Fin n)) := by
  simpa using (greedyIndices_prefix K v n).1

private theorem card_eq_finrank_image (v : Fin n → V) {S : Finset (Fin n)}
    (hind : LinearIndepOn K v (S : Set (Fin n))) :
    S.card = Module.finrank K (Submodule.span K (v '' (S : Set (Fin n)))) := by
  rw [Set.image_eq_range, finrank_span_eq_card hind]
  simp

private theorem card_prefix_le (v : Fin n → V) {S T : Finset (Fin n)}
    (hS : LinearIndepOn K v (S : Set (Fin n))) (hT : LinearIndepOn K v (T : Set (Fin n)))
    (hspan : ∀ k : ℕ, Submodule.span K (v '' ((S : Set (Fin n)) ∩ {i | i.val < k})) =
      Submodule.span K (v '' {i : Fin n | i.val < k})) (j : Fin n) :
    (T.filter (· ≤ j)).card ≤ (S.filter (· ≤ j)).card := by
  let early := {i : Fin n | i.val < j.val + 1}
  have hp (B : Finset (Fin n)) : ((B.filter (· ≤ j) : Finset (Fin n)) : Set (Fin n)) =
      (B : Set (Fin n)) ∩ early := by
    ext i
    simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff, early, Set.mem_ofPred_eq]
    exact and_congr_right' (Nat.lt_succ_iff.symm : i.val ≤ j.val ↔ i.val < j.val + 1)
  rw [card_eq_finrank_image K v (hT.mono (Finset.filter_subset _ _)),
    card_eq_finrank_image K v (hS.mono (Finset.filter_subset _ _)), hp, hp, hspan]
  let := Module.Finite.span_of_finite K ((Set.toFinite early).image v)
  exact Submodule.finrank_mono (Submodule.span_mono (Set.image_mono Set.inter_subset_right))

/-- Among all independent rank-sized subsets, the first basis selected in index order is
uniquely of smallest total weight. Its indices span the entire family. -/
theorem exists_isolatedBasis {r : ℕ}
    (hr : r = Module.finrank K (Submodule.span K (Set.range v))) :
    ∃ S : Set.powersetCard (Fin n) r,
      LinearIndepOn K v (S : Set (Fin n)) ∧
      Submodule.span K (v '' (S : Set (Fin n))) = Submodule.span K (Set.range v) ∧
      ∀ T : Set.powersetCard (Fin n) r, LinearIndepOn K v (T : Set (Fin n)) → S ≠ T →
        (∑ i ∈ S.val, (i.val + 1)) < ∑ i ∈ T.val, (i.val + 1) := by
  have hspan : Submodule.span K (v '' (greedyIndices K v : Set (Fin n))) =
      Submodule.span K (Set.range v) := by simpa using greedyIndices_span_prefix K v n
  have hind := greedyIndices_linearIndepOn K v
  have hcard : (greedyIndices K v).card = r := by rw [card_eq_finrank_image K v hind, hspan, hr]
  let S : Set.powersetCard (Fin n) r := Set.powersetCard.ofCard hcard
  refine ⟨S, hind, hspan, ?_⟩
  intro T hT hne
  exact weight_lt_of_prefix_dominance (card_prefix_le K v hind hT (greedyIndices_span_prefix K v)) hne

end RankQuery

end VPVNP
end Computability
end OAI
