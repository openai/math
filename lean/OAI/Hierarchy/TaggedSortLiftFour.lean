import OAI.Hierarchy.TaggedSortLiftDeal
import OAI.Hierarchy.TaggedSortCleanupWidths

namespace OAI
/-! # Four concrete short-sort passes sort the larger power-of-two array -/

namespace Hierarchy.Tagged.SortLift

noncomputable section
variable {n : ℕ} {κ : Type*} [LinearOrder κ]

def Sorts (ss : List (Stage n)) (κ : Type*) [LinearOrder κ] : Prop :=
  ∀ x : Fin n → κ, run ss id x = x ∘ Tuple.sort x

def Widths (P : ℕ → Prop) (ss : List (Stage n)) : Prop :=
  ∀ S ∈ ss, ∀ i, P (S.length i)

theorem run_append (ss ts : List (Stage n)) (x : Fin n → κ) :
    run (ss ++ ts) id x = run ts id (run ss id x) :=
  List.foldl_append

theorem first_pair (κ : Type*) [LinearOrder κ] (k p h : ℕ) (hk : 0<k) (eqh : k*p=h) :
    ∃ ss : List (Stage (k*h)), ss.length=2 ∧ Widths (·=h) ss ∧
      ∀ (x : Fin (k*h) → κ) (t : κ), ∃ lo hi, hi=lo+k*k ∧
        (∀ i : Fin (k*h), i.val<lo → run ss id x i<t) ∧
        (∀ i : Fin (k*h), hi ≤ i.val → ¬run ss id x i<t) := by
  subst h
  refine ⟨[columns k (k*p),deal k p],rfl,?_,?_⟩
  · intro S hS i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hS
    rcases hS with rfl | rfl <;> rfl
  · intro x t
    exact deal_window k p hk id x t

theorem four_pass (κ : Type*) [LinearOrder κ] (k p B : ℕ) (hk : 0<k) (pos : 0<B)
    (eqh : k*p=B+B) (window : k*k≤B) :
    ∃ ss : List (Stage (k*(B+B))), ss.length=4 ∧ Widths (fun w=>w=B ∨ w=B+B) ss ∧ Sorts ss κ := by
  obtain ⟨pre,len,width,mix⟩ := first_pair κ k p (B+B) hk eqh
  let post := [aligned k B pos,shifted k B pos]
  refine ⟨pre ++ post,by simp [post,len],?_,?_⟩
  · intro S hS i
    rcases List.mem_append.mp hS with h | h
    · exact Or.inr (width S h i)
    · simp only [post,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl
      · exact Or.inr (aligned_exact k B pos i)
      · exact shifted_exact k B pos hk i
  · intro x
    apply run_eq_sorted
    rw [run_append]
    intro i j hij
    by_contra! bad
    let t := run post id (run pre id x) i
    obtain ⟨lo,hi,size,before,after⟩ := mix x t
    have cleanCut := shifted_cleanup k B pos id (run pre id x) t lo hi (by omega) before after
    exact (lt_irrefl t) (cleanCut i j hij bad)

end
end Hierarchy.Tagged.SortLift

end OAI
