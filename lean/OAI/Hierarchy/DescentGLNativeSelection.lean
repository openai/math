import OAI.Hierarchy.DescentGLFeasibleRows
import OAI.Hierarchy.DescentGLSelection
import OAI.Hierarchy.DescentRowScore
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Indexed feasible-row selection for the binary layout controller -/

namespace Hierarchy.DescentGL
open scoped Classical BigOperators
noncomputable section

/-- The ordinary binary index of the coefficients of a row functional. -/
def rowIndex (k : ℕ) : Row k ≃ Fin (2^k) :=
  (Pi.basisFun (ZMod 2) (Fin k)).dualBasis.equivFun.toEquiv.trans finFunctionFinEquiv

/-- The controller enumerates rows by their binary index and omits the span of
the rows already fixed. -/
def legalMenu {h k : ℕ} (hk : h<k) (base : Layout k) : Finset (Fin (2^k)) :=
  Finset.univ.filter fun i => (rowIndex k).symm i ∉
    Submodule.span (ZMod 2) (Set.range fun l : Fin h => rowFunctional base (l.castLE hk.le))

theorem mem_legalMenu {h k : ℕ} (hk : h<k) (base : Layout k) (i : Fin (2^k)) :
    i ∈ legalMenu hk base ↔ ∃ L : Layout k,
      (∀ l : Fin h, rowFunctional L (l.castLE hk.le)=rowFunctional base (l.castLE hk.le)) ∧
      rowFunctional L ⟨h,hk⟩=(rowIndex k).symm i := by
  simpa only [legalMenu,Finset.mem_filter,Finset.mem_univ,true_and] using
    (feasible_next_row_iff hk base ((rowIndex k).symm i)).symm

theorem legalMenu_nonempty {h k : ℕ} (hk : h<k) (base : Layout k) :
    (legalMenu hk base).Nonempty := by
  refine ⟨rowIndex k (rowFunctional base ⟨h,hk⟩), (mem_legalMenu hk base _).mpr ?_⟩
  exact ⟨base,fun _ => rfl,((rowIndex k).symm_apply_apply _).symm⟩

/-- The uniquely prescribed least-index minimizer in the actual finite row menu. -/
def chosenIndex {h k : ℕ} (hk : h<k) (base : Layout k) (score : Row k → ℝ) : Fin (2^k) :=
  DescentRowScore.nextRow (legalMenu hk base) (legalMenu_nonempty hk base)
    (fun i => score ((rowIndex k).symm i))

private theorem earlier_rows {h k : ℕ} (hk : h<k) (L T : Layout k) :
    (∀ l : Fin h, rowFunctional L (l.castLE hk.le)=rowFunctional T (l.castLE hk.le)) ↔
      ∀ i<h,layoutRow L i=layoutRow T i := by
  constructor
  · intro prev i hi
    funext x
    have him : i<k := hi.trans hk
    have castIdx : (⟨i,hi⟩ : Fin h).castLE hk.le=⟨i,him⟩ := Fin.ext rfl
    simpa only [layoutRow,dite_eq_left him,rowFunctional_apply,castIdx] using
      DFunLike.congr_fun (prev ⟨i,hi⟩) x
  · intro prev l
    apply LinearMap.ext
    intro x
    have castIdx : l.castLE hk.le=⟨l.val,l.isLt.trans hk⟩ := Fin.ext rfl
    simpa only [layoutRow,dite_eq_left (l.isLt.trans hk),rowFunctional_apply,castIdx] using
      congrFun (prev l.val l.isLt) x

/-- When native row scores give the conditional potentials, the controller's
actual tie-broken choice has a GL completion and does not increase the mean. -/
theorem chosenIndex_completion {h k : ℕ} (hk : h<k) (base : Layout k)
    (cost : Layout k → ℝ) (score : Row k → ℝ)
    (represents : ∀ T : Layout k, (∀ i<h,layoutRow T i=layoutRow base i) →
      prefixMean cost T (h+1)=score (rowFunctional T ⟨h,hk⟩)) :
    ∃ L : Layout k, (∀ i<h,layoutRow L i=layoutRow base i) ∧
      rowFunctional L ⟨h,hk⟩=(rowIndex k).symm (chosenIndex hk base score) ∧
      prefixMean cost L (h+1) ≤ prefixMean cost base h := by
  let a := chosenIndex hk base score
  have best := DescentRowScore.nextRow_spec (legalMenu hk base) (legalMenu_nonempty hk base)
    (fun i => score ((rowIndex k).symm i))
  obtain ⟨L,agrees,chosen⟩ := (mem_legalMenu hk base a).mp best.1
  have prefixAgrees := (earlier_rows hk L base).mp agrees
  refine ⟨L,prefixAgrees,chosen,minimizing_next_row cost base L ?_⟩
  intro T same
  have legal := (mem_legalMenu hk base (rowIndex k (rowFunctional T ⟨h,hk⟩))).mpr
    ⟨T,(earlier_rows hk T base).mpr same,((rowIndex k).symm_apply_apply _).symm⟩
  rw [represents L prefixAgrees,represents T same,chosen]
  simpa only [a,chosenIndex,Equiv.symm_apply_apply] using best.2.1 _ legal

/-- Iterating the native least-index choice fixes one further row per iteration.
The resulting full layout satisfies the original uniform bound. -/
theorem chosen_layout_trajectory {k : ℕ} (initial : Layout k) (cost : Layout k → ℝ)
    (score : Fin k → Layout k → Row k → ℝ)
    (represents : ∀ (h : Fin k) (base T : Layout k),
      (∀ i<h.val,layoutRow T i=layoutRow base i) →
      prefixMean cost T (h.val+1)=score h base (rowFunctional T h)) :
    ∃ run : ℕ → Layout k, run 0=initial ∧
      (∀ h : Fin k, (∀ i<h.val,layoutRow (run (h.val+1)) i=layoutRow (run h.val) i) ∧
        rowFunctional (run (h.val+1)) h =
          (rowIndex k).symm (chosenIndex h.isLt (run h.val) (score h (run h.val))) ∧
        prefixMean cost (run (h.val+1)) (h.val+1) ≤ prefixMean cost (run h.val) h.val) ∧
      cost (run k) ≤ (∑ T, cost T) / Fintype.card (Layout k) := by
  let next (h : ℕ) (base : Layout k) : Layout k := if ht : h<k then
    Classical.choose (chosenIndex_completion ht base cost (score ⟨h,ht⟩ base)
      (represents ⟨h,ht⟩ base)) else base
  let run : ℕ → Layout k := Nat.rec initial next
  have step (h : Fin k) :
      (∀ i<h.val,layoutRow (run (h.val+1)) i=layoutRow (run h.val) i) ∧
      rowFunctional (run (h.val+1)) h =
        (rowIndex k).symm (chosenIndex h.isLt (run h.val) (score h (run h.val))) ∧
      prefixMean cost (run (h.val+1)) (h.val+1) ≤ prefixMean cost (run h.val) h.val := by
    have spec := Classical.choose_spec (chosenIndex_completion h.isLt (run h.val) cost
      (score h (run h.val)) (represents h (run h.val)))
    rw [show run (h.val+1)=next h.val (run h.val) from rfl]
    simpa only [next, dite_eq_left h.isLt] using spec
  refine ⟨run,rfl,step,?_⟩
  have chain (h : ℕ) (ht : h≤k) :
      prefixMean cost (run h) h ≤ prefixMean cost (run 0) 0 := by
    induction h with
    | zero => exact le_rfl
    | succ h ih => exact (step ⟨h,ht⟩).2.2.trans (ih (Nat.le_of_lt ht))
  simpa only [prefixMean_full,prefixMean_zero] using chain k le_rfl


end
end Hierarchy.DescentGL

end OAI
