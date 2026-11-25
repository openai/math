import OAI.Hierarchy.TraceIntervalCounts
import Mathlib.Order.Interval.Finset.Nat

namespace OAI
/-! # Which original external pairs a registration direction counts -/

namespace Hierarchy.TraceAdmission

open scoped BigOperators
variable {lanes roots : ℕ}

theorem bandLength_fiber {span lo hi : ℕ} (pos : 0<span) (order : lo≤hi) (q : ℕ) :
    ((Finset.Ico lo hi).filter fun n=>n/span=q).card=bandLength span q lo hi := by
  have set : ((Finset.Ico lo hi).filter fun n=>n/span=q) =
      Finset.Ico (max lo (q*span)) (min hi ((q+1)*span)) := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Ico,max_le_iff,lt_min_iff,Nat.div_eq_iff pos,Nat.succ_mul]
    omega
  rw [set,Nat.card_Ico,bandLength_eq _ _ _ _ order]

/-- The row weight equals the size of the original owner fiber, independently
of the number and sizes of the other factors. The band may be empty. -/
theorem rootSum_band_eq_card (dest : Fin lanes→Fin roots) (v : Fin roots)
    (span lo hi : ℕ) (pos : 0<span) (order : lo≤hi) (room : hi≤lanes*span)
    (owner : ℕ→Fin roots)
    (same : ∀ x∈Finset.Ico lo hi,∀ q : Fin lanes,x/span=q.val → owner x=dest q) :
    rootSum dest v (fun q=>bandLength span q lo hi) =
      ((Finset.Ico lo hi).filter fun x=>owner x=v).card := by
  let set := (Finset.Ico lo hi).filter fun x=>owner x=v
  have partition := Finset.card_eq_sum_card_fiberwise (s:=set) (t:=Finset.range lanes)
    (f:=fun x=>x/span) (by
      intro x hx
      exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul pos).mpr
        (((Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).2).trans_le room)))
  rw [←Fin.sum_univ_eq_sum_range (fun q=> (set.filter fun x=>x/span=q).card) lanes] at partition
  refine Eq.trans ?_ partition.symm
  apply Finset.sum_congr rfl
  intro q _
  by_cases eqn : dest q=v
  · rw [ite_eq_left eqn]
    change bandLength span q.val lo hi = _
    rw [←bandLength_fiber pos order q.val]
    congr 1
    ext x
    simp only [set,Finset.mem_filter]
    constructor
    · rintro ⟨hx,hq⟩
      exact ⟨⟨hx,(same x hx q hq).trans eqn⟩,hq⟩
    · exact fun x=>⟨x.1.1,x.2⟩
  · rw [ite_eq_right eqn]
    symm
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x sh
    obtain ⟨hx,hq⟩:=Finset.mem_filter.mp sh
    obtain ⟨sub,home⟩:=Finset.mem_filter.mp hx
    exact eqn ((same x sub q hq).symm.trans home)

/-- Pairs numbered in the public direction band's original order are charged
once to their genuine physical destination. -/
theorem directionCount_eq_card (dest : Fin lanes→Fin roots) (v : Fin roots)
    (band span i : ℕ) (pos : 0<span) (room : (i+1)*band≤lanes*span)
    (owner : ℕ→Fin roots)
    (same : ∀ x∈Finset.Ico (i*band) ((i+1)*band),∀ q : Fin lanes,
      x/span=q.val → owner x=dest q) :
    directionCount dest v band span i =
      ((Finset.Ico (i*band) ((i+1)*band)).filter fun x=>owner x=v).card :=
  rootSum_band_eq_card dest v span _ _ pos (Nat.mul_le_mul_right _ (Nat.le_succ i)) room owner same

/-- Every source *bit*, including the fixed description and advice, is counted
in precisely the factor that contains its initial physical input lane. -/
theorem inputCount_eq_card (dest : Fin lanes→Fin roots) (v : Fin roots)
    (cap pairSpan : ℕ) (pos : 0<pairSpan) (room : cap≤lanes*(2*pairSpan))
    (owner : ℕ→Fin roots)
    (same : ∀ x∈Finset.range cap,∀ q : Fin lanes,x/(2*pairSpan)=q.val → owner x=dest q) :
    inputCount dest v cap pairSpan = ((Finset.range cap).filter fun x=>owner x=v).card := by
  have eqn := rootSum_band_eq_card dest v (2*pairSpan) 0 cap (by omega)
    (Nat.zero_le _) room owner (fun x hx=>same x (by simpa using hx))
  have weights : FactorPinIntervals.bucketLength cap (2*pairSpan) =
      fun q=>bandLength (2*pairSpan) q 0 cap := by
    funext q
    simp [bandLength,FactorPinIntervals.bucketLength]
  rw [inputCount,weights]
  simpa only [Nat.Ico_zero_eq_range] using eqn


end Hierarchy.TraceAdmission

end OAI
