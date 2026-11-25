import OAI.Hierarchy.ABPFirstCutCoeff
import OAI.Hierarchy.ABPFirstCutPrefix
import OAI.Hierarchy.ABPFirstCutRank
import OAI.Hierarchy.ABPFirstCutSuffix

namespace OAI
/-! # First-cut decomposition of an affine branching program

Expand each edge label into its constant and variable terms. A contribution to
one squarefree coefficient then visits variable slots in a definite order. At
the first prefix whose slot set belongs to the cut family, split the path at the
vertex just reached. The sum before that vertex uses only the prefix slots, and
the sum after it uses only the remaining slots.
-/

namespace Hierarchy.ABPFirstCut

open scoped BigOperators Classical
noncomputable section

variable {F : Type*} {V : Type} [Field F] {τ : V → Type} [DecidableEq V]

private theorem shift_empty_delta (U S : Finset V) :
    shift U (fun T => if T = ∅ then (1 : F) else 0) S = if S = U then 1 else 0 := by
  classical
  by_cases he : S = U
  · subst U
    simp [shift]
  · by_cases h : U ⊆ S
    · have hne : S \ U ≠ ∅ := fun h0 => he (Finset.Subset.antisymm
          (Finset.sdiff_eq_empty_iff_subset.mp h0) h)
      simp [shift, h, hne, he]
    · simp [shift, h, he]

private theorem cut_indicator_sum (family : Finset (Finset V)) (S : Finset V)
    (z : Finset V → F) :
    (∑ U : ↥family, z U.val * (if S = U.val then 1 else 0)) =
      if S ∈ family then z S else 0 := by
  classical
  by_cases h : S ∈ family
  · let selected : ↥family := ⟨S, h⟩
    rw [ite_eq_left h, Finset.sum_eq_single selected]
    · simp [selected]
    · intro U _ hu
      have ne : S ≠ U.val := fun he => hu (Subtype.ext he.symm)
      simp [ne]
    · simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro U _
    have ne : S ≠ U.val := fun he => h (he.symm ▸ U.property)
    simp [ne]

/-- All contributions that have already reached a member of the cut family. -/
private def marked (family : Finset (Finset V)) (a : ∀ i, τ i) {n : ℕ}
    (g : Rows F (Σ i, τ i) n) (t : Fin n) (S : Finset V) : F :=
  ∑ U : ↥family, ∑ c : Fin n,
    hit family a g c U.val * shift U.val (transfer a g t c) S

private theorem marked_castSucc (family : Finset (Finset V)) (a : ∀ i, τ i) {n : ℕ}
    (g : Rows F (Σ i, τ i) n) (edges : List (Fin n × Affine F (Σ i, τ i)))
    (t : Fin n) (S : Finset V) :
    marked family a (g.snoc edges) t.castSucc S = marked family a g t S := by
  classical
  simp [marked, Fin.sum_univ_castSucc, shift]

private theorem marked_last (family : Finset (Finset V)) (a : ∀ i, τ i) {n : ℕ}
    (g : Rows F (Σ i, τ i) n) (edges : List (Fin n × Affine F (Σ i, τ i)))
    (S : Finset V) :
    marked family a (g.snoc edges) (Fin.last n) S =
      step a edges (marked family a g) S +
        if S ∈ family then step a edges (pending family a g) S else 0 := by
  classical
  have old (c : Fin n) : transfer a (g.snoc edges) (Fin.last n) c.castSucc =
      step a edges (fun t => transfer a g t c) :=
    funext (transfer_last_old a g edges c)
  have newCut : transfer a (g.snoc edges) (Fin.last n) (Fin.last n) =
      fun T => if T = ∅ then 1 else 0 := funext (transfer_last_last a g edges)
  unfold marked
  simp only [Fin.sum_univ_castSucc, hit_castSucc, hit_last, old,
    newCut, shift_empty_delta, Finset.sum_add_distrib, cut_indicator_sum]
  congr 1
  rw [step_sum]
  apply Finset.sum_congr rfl
  intro U _
  rw [step_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [step_const_mul, step_shift]

variable [Fintype V] [∀ i, Fintype (τ i)]

private theorem coefficient_split (family : Finset (Finset V)) (a : ∀ i, τ i) {n : ℕ}
    (g : Rows F (Σ i, τ i) n) (t : Fin n) (S : Finset V) :
    slotCoeff a S (g.values t) = pending family a g t S + marked family a g t S := by
  classical
  induction g generalizing S with
  | source => simp [marked, slotCoeff_source]
  | @snoc n prev edges ih =>
    refine Fin.lastCases ?_ (fun i => ?_) t
    · rw [slotCoeff_snoc_last]
      change step a edges (fun j T => slotCoeff a T (prev.values j)) S = _
      have eq : (fun j T => slotCoeff a T (prev.values j)) =
          fun j T => pending family a prev j T + marked family a prev j T :=
        funext fun j => funext fun T => ih j T
      rw [eq, step_add, marked_last, pending_last]
      by_cases h : S ∈ family <;> simp [h, add_comm]
    · simp only [slotCoeff_snoc_castSucc, pending_castSucc, marked_castSucc, ih]

/-- The slot coefficient tensor of an affine ABP is a sum over cuts, with at
most one product per possible cut vertex in each summand. -/
theorem abp_first_cut (g : ABP F (Σ i, τ i)) (family : Finset (Finset V))
    (hempty : ∅ ∉ family) (hcover : HitsEveryOrder family) :
    CutFactorization family g.vertices (fun a => slotCoeff a Finset.univ g.polynomial) := by
  classical
  apply cutFactorization_of_local family g.vertices _
    (fun U c a => hit family a g.rows c U.val)
    (fun U c a => transfer a g.rows g.sink c (Finset.univ \ U.val))
  · intro U c a b h
    exact hit_congr _ _ _ _ h
  · intro U c a b h
    apply transfer_congr
    exact fun i hi => h i (Finset.mem_sdiff.mp hi).2
  · intro a
    rw [ABP.polynomial, coefficient_split family]
    have hz := pending_eq_zero_of_not_avoids family a g.rows g.sink Finset.univ
      hempty (not_avoids_univ hcover)
    simp [hz, marked, shift]

/-- The branching-program assertion of the coefficient partition lemma, with
one summand per allowed cut and a matrix-rank bound given by the size budget. -/
theorem hasABP_first_cut {s : ℕ} {p : MvPolynomial (Σ i, τ i) F} (h : HasABP s p)
    (family : Finset (Finset V)) (hempty : ∅ ∉ family) (hcover : HitsEveryOrder family) :
    ∃ t : ↥family → (∀ i, τ i) → F,
      (∀ a, slotCoeff a Finset.univ p = ∑ U : ↥family, t U a) ∧
      ∀ U, (flatten U.val (t U)).rank ≤ s := by
  obtain ⟨g, rfl, hsize⟩ := h
  obtain ⟨t, sum_eq, ranks⟩ := (abp_first_cut g family hempty hcover).exists_summands
  exact ⟨t, sum_eq, fun U => (ranks U).trans ((Nat.le_add_right _ _).trans hsize)⟩


end
end Hierarchy.ABPFirstCut

end OAI
