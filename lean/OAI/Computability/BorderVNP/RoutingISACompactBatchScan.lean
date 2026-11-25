import OAI.Computability.BorderVNP.RoutingISACompactBatchRow
import Mathlib.Algebra.BigOperators.Intervals

/-! # Native batch scan over all compact cell inputs

The scan executes one physical seed writer and one physical packer per cell. Its tick
allowance sums the actual per-row payload and external lengths, including the loop guard.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactBatch

open VPVNP.BurstRAM Finset

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8} {table count : ℕ}

private theorem setup_run (s : Bank w) (m : Memory w) (five : 5 < 2^w)
    (width : (s 2).val = w) (base : (s 32).val = table) (len : (s 33).val = count) :
    ∃ es t, Runs pub macros setup s m es t m ∧ traceCost es ≤ setup.slots ∧ Ready table count 0 t := by
  have safe : setup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    change 1 < 2^w ∧ 0 < 2^w ∧ 5 < 2^w
    exact ⟨by omega, Nat.two_pow_pos _, five⟩
  obtain ⟨es,t,r,c,he⟩ := setup.runReadOnly pub macros m s safe
  refine ⟨es,t,r,c,?_⟩
  change readings t 39 = 1 ∧ readings t 2 = w ∧ readings t 32 = table ∧
    readings t 33 = count ∧ readings t 34 = 0 ∧ readings t 35 = 5
  rw [he]
  simp (config := {decide := true}) [setup,Code.block,Code.evalNat,readings,width,base,len]

private theorem loop_run (m : Memory w) (tasks : ℕ → Task) (hw : 0 < w)
    (space : table+5*count ≤ 2^w) (rows : ∀ i < count,
      (tasks i).Stored (written m tasks i) table i ∧ (tasks i).Input (written m tasks i) ∧ (tasks i).Fits w)
    (i : ℕ) (le : i ≤ count) (s : Bank w) (h : Ready table count i s) :
    ∃ es t, Runs pub macros (.whileLt 34 33 body) s (written m tasks i) es t (written m tasks count) ∧
      traceCost es ≤ (∑ j ∈ Ico i count, ((tasks j).cost+1))+1 ∧ Ready table count count t := by
  by_cases last : i = count
  · subst i
    have guard : ¬ s 34 < s 33 := show ¬ (s 34).val < (s 33).val by rw [h.2.2.2.1,h.2.2.2.2.1]; omega
    exact ⟨_,s,Runs.whileDone guard,by change 1 ≤ _; omega,h⟩
  · have lt : i < count := by omega
    have guard : s 34 < s 33 := show (s 34).val < (s 33).val by rw [h.2.2.2.1,h.2.2.2.2.1]; exact lt
    obtain ⟨stored,input,fit⟩ := rows i lt
    obtain ⟨xs,u,first,c₁,ready⟩ := body_run (pub := pub) (macros := macros)
      (tasks i) s (written m tasks i) hw h lt space stored input fit
    obtain ⟨ys,t,rest,c₂,done⟩ := loop_run m tasks hw space rows (i+1) lt u ready
    refine ⟨_,t,Runs.whileStep guard first rest,?_,done⟩
    change 1+traceCost (xs++ys) ≤ _
    rw [show traceCost (xs++ys) = traceCost xs + traceCost ys from VPVNP.RAMBuckets.cost_append ..,
      Finset.sum_eq_sum_Ico_succ_bot lt]
    omega
termination_by count-i

/-- Execute all public descriptor rows, producing the exact accumulated word memory and
paying the sum of the actual task lengths. The team index and public frame are not needed
by this preparation phase. -/
theorem scan_run (s : Bank w) (m : Memory w) (tasks : ℕ → Task) (five : 5 < 2^w)
    (width : (s 2).val = w) (base : (s 32).val = table) (len : (s 33).val = count)
    (space : table+5*count ≤ 2^w)
    (rows : ∀ i < count, (tasks i).Stored (written m tasks i) table i ∧
      (tasks i).Input (written m tasks i) ∧ (tasks i).Fits w) :
    ∃ es t, Runs pub macros scan s m es t (written m tasks count) ∧
      traceCost es ≤ setup.slots+(∑ i ∈ range count, ((tasks i).cost+1))+1 ∧ Ready table count count t := by
  have hw : 0 < w := by
    cases w with
    | zero => contradiction
    | succ w => exact Nat.succ_pos _
  obtain ⟨xs,u,first,c₁,ready⟩ := setup_run (pub := pub) (macros := macros) s m five width base len
  obtain ⟨ys,t,rest,c₂,done⟩ := loop_run m tasks hw space rows 0 (Nat.zero_le _) u ready
  refine ⟨_,t,first.seq rest,?_,done⟩
  rw [show traceCost (xs++ys) = traceCost xs + traceCost ys from VPVNP.RAMBuckets.cost_append ..]
  simp only [Nat.Ico_zero_eq_range] at c₂
  omega

end RoutingISA.CompactBatch

end BorderVNP
end Computability
end OAI
