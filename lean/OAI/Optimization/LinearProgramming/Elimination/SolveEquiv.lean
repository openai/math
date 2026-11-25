import OAI.Optimization.LinearProgramming.Elimination.MaskSolve

/-! The dynamic and fixed-width routines choose the same descending greedy basis. Their
outputs coincide, including the coefficient choice for nonunique solutions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination
open Matrix Module Submodule
open scoped Matrix BigOperators
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m d : ℕ}

omit [IsStrictOrderedRing K] in
private theorem scan_sublist (A : Matrix (Fin m) (Fin d) K) (l : List (Fin d)) :
    (scan A l).indices.Sublist l := by
  induction l with
  | nil => exact .slnil
  | cons j l ih =>
    simp only [scan]
    split
    · exact .cons j ih
    · exact .cons_cons j ih

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem columns_independent_iff (A : Matrix (Fin m) (Fin d) K) (l : List (Fin d)) (h : l.Nodup) :
    LinearIndependent K (columns A l).col ↔ LinearIndepOn K A.col (l.toFinset : Set (Fin d)) := by
  have hr : Set.range l.get = (l.toFinset : Set (Fin d)) := by
    ext j; exact List.mem_iff_get.symm.trans List.mem_toFinset.symm
  rw [←hr]
  exact (linearIndepOn_range_iff (List.nodup_iff_injective_get.mp h) A.col).symm

/-- In a candidate list without repeated indices, each mask decision reproduces the
variable-order Gram determinant test on the indices selected so far. -/
theorem scanMask_eq_scan_indices (A : Matrix (Fin m) (Fin d) K) (js : List (Fin d)) (hn : js.Nodup) :
    scanMask (Aᵀ*A) js = (scan A js).indices.toFinset := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    let s := (scan A js).indices
    let B := columns A (j::s)
    have hsub : s.Sublist js := scan_sublist A js
    obtain ⟨hj,hjs⟩ := List.nodup_cons.mp hn
    have hnd : (j::s).Nodup := List.nodup_cons.mpr ⟨fun h=>hj (hsub.subset h),hjs.sublist hsub⟩
    have hi : scanMask (Aᵀ*A) js = s.toFinset := ih hjs
    have hnz : determinant (Bᵀ*B) ≠0 ↔ determinant (maskGram (Aᵀ*A) (flag (insert j s.toFinset))) ≠0 := by
      rw [gram_det_ne_zero,maskGram_det_ne_zero_iff]
      simpa only [List.toFinset_cons,B] using columns_independent_iff A (j::s) hnd
    simp only [scanMask,hi,scan]
    change (if determinant (maskGram (Aᵀ*A) (flag (insert j s.toFinset)))=0 then s.toFinset else insert j s.toFinset) =
      (if determinant (Bᵀ*B)=0 then s else j::s).toFinset
    by_cases h: determinant (Bᵀ*B)=0
    · have h' : determinant (maskGram (Aᵀ*A) (flag (insert j s.toFinset)))=0 :=
        by by_contra hc;exact hnz.mpr hc h
      rw [ite_eq_left h',ite_eq_left h]
    · rw [ite_eq_right (hnz.mp h),ite_eq_right h,List.toFinset_cons]

theorem basisMask_eq_columnBasis (A : Matrix (Fin m) (Fin d) K) :
    basisMask (Aᵀ*A) = (columnBasis A).toFinset := scanMask_eq_scan_indices A _ (List.nodup_finRange d)

omit [IsStrictOrderedRing K] in
theorem solve_zero_off_basis (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (x : Fin d→K)
    (hx : solve A b=some x) (j : Fin d) (hj : j∉columnBasis A) : x j=0 := by
  obtain ⟨c,rfl⟩ : ∃c : Fin (columnBasis A).length→K,x=scatter (columnBasis A) c := by
    simp only [solve] at hx
    split at hx
    · contradiction
    · rename_i c hc
      split at hx
      · exact ⟨c,(Option.some.inj hx).symm⟩
      · contradiction
  simp only [scatter,tabulateVec_eq]
  apply Finset.sum_eq_zero;intro k _
  exact ite_eq_right (fun h=>hj (List.mem_iff_get.mpr ⟨k,h⟩))

/-- Exact equality of the two Option-valued implementations, for inconsistent, unique,
underdetermined or zero-dimensional systems over every ordered field. -/
theorem fixedSolve_eq_solve (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) : fixedSolve A b=solve A b := by
  cases hs : solve A b with
  | none =>
    cases hf : fixedSolve A b with
    | none => rfl
    | some x => exact ((solve_none_iff A b).mp hs ⟨x,fixedSolve_sound A b x hf⟩).elim
  | some x =>
    apply fixedSolve_of_supported A b x (solve_sound A b x hs)
    intro j hj; exact solve_zero_off_basis A b x hs j (by simpa [basisMask_eq_columnBasis] using hj)

end Elimination
end LinearProgramming
end Optimization
end OAI
