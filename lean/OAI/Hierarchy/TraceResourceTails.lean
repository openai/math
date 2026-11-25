import OAI.Hierarchy.TraceIntervalScanner
import OAI.Hierarchy.TraceIntervalCounts

namespace OAI
/-! # Reading cumulative registration weights from actual ascending interval chains -/
namespace Hierarchy.TraceAdmission.Resources

open Computability.VPVNP.BurstRAM
open TraceIntervalScanner

variable {W lanes roots N : ℕ}

/-- Row 0 represents the sentinel; row `lanes-q` holds the total for the
list beginning at initial lane `q`. Every reachable successor has a smaller
row number because the physical interval lists are strictly increasing. -/
def cumulative (lanes : ℕ) (succPtr : ℕ → ℕ) (weight : ℕ → ℕ) (r : ℕ) : ℕ :=
  if r=0 then 0 else
    let q := lanes-r
    let ptr := succPtr q
    let t := if ptr=0 then 0 else lanes+1-ptr
    weight q + if _h : t<r then cumulative lanes succPtr weight t else 0
termination_by r

theorem cumulative_read {m : Memory W} {xs : List (Fin lanes)} (sorted : xs.Pairwise (·<·))
    (weight : ℕ→ℕ) {ptr : ℕ} (read : Chain N m ptr xs) :
    cumulative lanes (fun q=>(m (N+q)).val) weight (if ptr=0 then 0 else lanes+1-ptr) =
      (xs.map (fun q=>weight q.val)).sum := by
  induction xs generalizing ptr with
  | nil =>
    change ptr=0 at read
    subst ptr
    simp [cumulative]
  | cons q qs ih =>
    obtain ⟨rfl,tail⟩ := read
    have small := q.isLt
    have nonzero : lanes+1-(q.val+1) ≠ 0 := by omega
    have back : lanes-(lanes+1-(q.val+1))=q.val := by omega
    have past : (if (m (N+q.val)).val=0 then 0 else lanes+1-(m (N+q.val)).val) <
        lanes+1-(q.val+1) := by
      cases qs with
      | nil =>
        change (m (N+q.val)).val=0 at tail
        rw [tail]
        simp only [ite_true]
        omega
      | cons z zs =>
        have seq : q.val<z.val := (List.pairwise_cons.mp sorted).1 z (.head _)
        have := z.isLt
        rw [tail.1]
        simp only [Nat.succ_ne_zero,ite_false]
        omega
    simp only [Nat.succ_ne_zero, ite_false,List.map_cons,List.sum_cons]
    rw [cumulative]
    simp only [ite_eq_right nonzero,back,dite_eq_left past]
    exact congrArg (weight q.val+·) (ih (List.pairwise_cons.mp sorted).2 tail)

/-- Column totals found by the descending sweep at each actual head pointer. -/
theorem cumulative_root {dest : Fin lanes→Fin roots} {m o : Memory W} {H : ℕ}
    (h : Output H N dest m o) (v : Fin roots) (weight : ℕ → ℕ) :
    cumulative lanes (fun q=>(o (N+q)).val) weight
      (if (o (H+v.val)).val=0 then 0 else lanes+1-(o (H+v.val)).val)=rootSum dest v weight :=
  (cumulative_read ((List.pairwise_lt_finRange lanes).filter _) weight (h.chain v)).trans
    (rootSum_lists dest v weight)

end Hierarchy.TraceAdmission.Resources

end OAI
