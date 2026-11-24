import OAI.Computability.VPVNP.IndependentCompletion
import OAI.Computability.VPVNP.GrassmannTypes
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two

/-!
# Common completions of adjacent column frames

In the equality case of Lemma 5.3 of *VP and VNP differ over every field*,
one original column of a frame is replaced by a vector outside the span.
Putting the difference between the two columns into the completion preserves
the completed span of either block. Over the binary field this difference is
the sum used in Section 5.1.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open Set Submodule

variable {K V ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If the difference of two choices of a column already belongs to the
completion space, every completed block span is independent of the choice. -/
theorem completed_span_update [DecidableEq ι] {v : ι → V} (i : ι) (z : V)
    {S : Submodule K V} (h : z - v i ∈ S) (T : Set ι) :
    S ⊔ span K (v '' T) = S ⊔ span K ((Function.update v i z) '' T) := by
  apply le_antisymm <;> refine sup_le le_sup_left (span_le.mpr ?_)
  · rintro _ ⟨j, hj, rfl⟩
    have hmem : Function.update v i z j ∈ S ⊔ span K ((Function.update v i z) '' T) :=
      Submodule.mem_sup_right (subset_span ⟨j, hj, rfl⟩)
    by_cases hij : j = i
    · subst j
      rw [Function.update_self] at hmem
      simpa using sub_mem hmem (Submodule.mem_sup_left h)
    · simpa [Function.update_of_ne hij] using hmem
  · rintro _ ⟨j, hj, rfl⟩
    have hmem : v j ∈ S ⊔ span K (v '' T) := Submodule.mem_sup_right (subset_span ⟨j, hj, rfl⟩)
    by_cases hij : j = i
    · subst j
      simpa using add_mem (Submodule.mem_sup_left h) hmem
    · simpa [Function.update_of_ne hij] using hmem

/-- Adding a completion column to an original column is an invertible
elementary operation on the completed frame. -/
theorem independent_completed_update [DecidableEq ι] {v : ι → V} {w : κ → V}
    (i : ι) (j : κ) (z : V) (hj : w j = z - v i)
    (h : LinearIndependent K (Sum.elim v w)) :
    LinearIndependent K (Sum.elim (Function.update v i z) w) := by
  classical
  let c : ι ⊕ κ → K := fun a ↦ if a = Sum.inl i then 1 else 0
  have hc : c (Sum.inr j) = 0 := by simp [c]
  have h' := (linearIndependent_add_smul_iff (v := Sum.elim v w) hc).2 h
  convert h' using 1
  funext a
  rcases a with a | b
  · by_cases ha : a = i
    · subst a
      simp [c, hj, add_sub_cancel]
    · simp [c, ha]
  · simp [c]

private def completionIndices (ι : Type*) (k : ℕ) : ι ⊕ Fin (k + 1) ≃ Option ι ⊕ Fin k where
  toFun := Sum.elim (Sum.inl ∘ some) (Fin.cases (Sum.inl none) Sum.inr)
  invFun := Sum.elim (fun o ↦ o.elim (Sum.inr 0) Sum.inl) (Sum.inr ∘ Fin.succ)
  left_inv := by
    rintro (a | j)
    · rfl
    · refine Fin.cases ?_ (fun j ↦ ?_) j <;> rfl
  right_inv := by
    rintro ((_ | a) | j) <;> rfl

private theorem independent_cons_completion {v : ι → V} {k : ℕ} {w : Fin k → V} {x : V}
    (h : LinearIndependent K (Sum.elim (fun o ↦ Option.casesOn' o x v) w)) :
    LinearIndependent K (Sum.elim v (Fin.cons x w)) := by
  have h' := h.comp (completionIndices ι k) (completionIndices ι k).injective
  convert h' using 1
  funext a
  rcases a with a | j
  · rfl
  · refine Fin.cases ?_ (fun j ↦ ?_) j <;> rfl


/-- A common independent completion of the old and new frames containing
their column difference. The final equality holds for every block of columns,
including the whole tuple. -/
theorem adjacent_commonCompletion [DecidableEq ι] [Fintype ι] [FiniteDimensional K V]
    {v : ι → V} (hv : LinearIndependent K v) (i : ι) (z : V)
    (hz : z ∉ span K (range v)) {k : ℕ} (hk : 0 < k)
    (hd : Fintype.card ι + k ≤ Module.finrank K V) :
    ∃ w : Fin k → V, w ⟨0, hk⟩ = z - v i ∧
      LinearIndependent K (Sum.elim v w) ∧
      LinearIndependent K (Sum.elim (Function.update v i z) w) ∧
      ∀ T : Set ι, span K (range w) ⊔ span K (v '' T) =
        span K (range w) ⊔ span K ((Function.update v i z) '' T) := by
  cases k with
  | zero => omega
  | succ k =>
    have hdiff : z - v i ∉ span K (range v) := by
      intro h
      exact hz (by simpa using add_mem h (subset_span (mem_range_self i)))
    obtain ⟨tail, htail⟩ := exists_independent_completion (hv.option hdiff) (k := k)
      (by simpa [Nat.add_assoc, Nat.add_comm 1 k] using hd)
    let w : Fin (k + 1) → V := Fin.cons (z - v i) tail
    have h : LinearIndependent K (Sum.elim v w) := independent_cons_completion htail
    have hw : w 0 = z - v i := rfl
    refine ⟨w, hw, h, independent_completed_update i 0 z hw h, ?_⟩
    exact completed_span_update i z (subset_span ⟨0, hw⟩)

/-- For the two original blocks of Section 5.1 over the binary field, the
common completion has exactly `m - r` columns and contains `v i + z`.
It preserves each of the two completed planes. -/
theorem binary_pair_commonCompletion {m r : ℕ} (hr : r < m)
    {v : Fin r ⊕ Fin r → Space m}
    (hv : LinearIndependent (ZMod 2) v) (i : Fin r ⊕ Fin r) (z : Space m)
    (hz : z ∉ span (ZMod 2) (range v)) :
    ∃ w : Fin (m - r) → Space m, w ⟨0, by omega⟩ = v i + z ∧
      LinearIndependent (ZMod 2) (Sum.elim v w) ∧
      LinearIndependent (ZMod 2) (Sum.elim (Function.update v i z) w) ∧
      (span (ZMod 2) (range w) ⊔ span (ZMod 2) (range (v ∘ Sum.inl)) =
        span (ZMod 2) (range w) ⊔ span (ZMod 2) (range (Function.update v i z ∘ Sum.inl))) ∧
      (span (ZMod 2) (range w) ⊔ span (ZMod 2) (range (v ∘ Sum.inr)) =
        span (ZMod 2) (range w) ⊔ span (ZMod 2) (range (Function.update v i z ∘ Sum.inr))) := by
  obtain ⟨w, hw, h₁, h₂, hspan⟩ := adjacent_commonCompletion (K := ZMod 2) (v := v) hv i z hz
    (k := m - r) (by omega) (by
      simp only [Fintype.card_sum, Fintype.card_fin, Module.finrank_pi]
      omega)
  refine ⟨w, ?_, h₁, h₂, ?_, ?_⟩
  · rw [hw]
    ext j
    exact (CharTwo.sub_eq_add _ _).trans (add_comm _ _)
  · simpa only [← range_comp] using hspan (range Sum.inl)
  · simpa only [← range_comp] using hspan (range Sum.inr)

end Grassmann

end VPVNP
end Computability
end OAI
