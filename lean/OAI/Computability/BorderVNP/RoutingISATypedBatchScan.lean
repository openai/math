import OAI.Computability.BorderVNP.RoutingISATypedBatchRow
import Mathlib.Algebra.BigOperators.Intervals

/-! # Running every prepared typed cell of the current team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedBatch

open VPVNP.BurstRAM Finset

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8} {base count : ℕ}

private theorem start (s : Bank w) (m : Memory w) (seven : 7 < 2^w)
    (width : (s 40).val=w) (table : (s 41).val=base) (length : (s 42).val=count) :
    ∃ es t, Runs pub macros setup s m es t m ∧ traceCost es ≤ setup.slots ∧ Ready base count 0 t := by
  have safe : setup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    have hw : w ≠ 0 := by rintro rfl; simp at seven
    simp [setup,Code.block,Code.safeReadOnly]
    omega
  obtain ⟨es,t,r,h,hr⟩ := setup.runReadOnly pub macros m s safe
  refine ⟨es,t,r,h,?_⟩
  change readings t 40 = _ ∧ readings t 41 = _ ∧ readings t 42 = _ ∧ readings t 43 = _ ∧
    readings t 44 = _ ∧ readings t 47 = _
  rw [hr]
  simp (config := {decide := true}) [setup,Code.block,Code.evalNat,readings,width,table,length]

/-- Sum of fetch, private input assembly, public pointer publication and loop guard ticks. -/
def rowCharge (cost : ℕ → ℕ) (i : ℕ) := fetch.slots + cost i + publish.slots + 1

private theorem loop_run (m : Memory w) (tasks : ℕ → Task)
    (space : base+7*count ≤ 2^w)
    (rows : ∀ i < count, (tasks i).Stored (written m tasks i) base i ∧ (tasks i).callRow+2 < 2^w ∧
      (tasks i).cell.Stored (written m tasks i) ∧ (tasks i).cell.Room w)
    (i : ℕ) (le : i ≤ count) (s : Bank w) (ready : Ready base count i s) :
    ∃ es t, Runs pub macros (.whileLt 43 42 body) s (written m tasks i) es t (written m tasks count) ∧
      traceCost es ≤ (∑ j ∈ Ico i count, rowCharge (fun k => (tasks k).cell.cost w) j)+1 ∧ Ready base count count t := by
  by_cases last : i = count
  · subst i
    have guard : ¬ s 43 < s 42 := show ¬ (s 43).val < (s 42).val by rw [ready.2.2.1,ready.2.2.2.1]; omega
    exact ⟨_,s,.whileDone guard,by change 1 ≤ _; omega,ready⟩
  · have lt : i < count := by omega
    have guard : s 43 < s 42 := show (s 43).val < (s 42).val by rwa [ready.2.2.1,ready.2.2.2.1]
    obtain ⟨row,fit,data,room⟩ := rows i lt
    obtain ⟨es,u,r,h,hu⟩ := body_run (pub := pub) (macros := macros) (tasks i) s (written m tasks i) ready row lt space fit data room
    obtain ⟨fs,z,next,hn,hz⟩ := loop_run m tasks space rows (i+1) lt u hu
    refine ⟨_,z,.whileStep guard r next,?_,hz⟩
    change 1+traceCost (es++fs) ≤ _
    rw [show traceCost (es++fs) = traceCost es + traceCost fs from VPVNP.RAMBuckets.cost_append ..,
      sum_eq_sum_Ico_succ_bot lt]
    dsimp only [rowCharge] at hn ⊢
    omega
termination_by count-i

/-- The exact row-by-row native execution writes the true compact argument pointer
and length into each indicated call directory row at its own chronological step. -/
theorem scan_run (s : Bank w) (m : Memory w) (tasks : ℕ → Task)
    (seven : 7 < 2^w) (width : (s 40).val=w) (table : (s 41).val=base) (length : (s 42).val=count)
    (space : base+7*count ≤ 2^w)
    (rows : ∀ i < count, (tasks i).Stored (written m tasks i) base i ∧ (tasks i).callRow+2 < 2^w ∧
      (tasks i).cell.Stored (written m tasks i) ∧ (tasks i).cell.Room w) :
    ∃ es t, Runs pub macros scan s m es t (written m tasks count) ∧
      traceCost es ≤ setup.slots + (∑ j ∈ range count, rowCharge (fun k => (tasks k).cell.cost w) j) + 1 ∧ Ready base count count t := by
  obtain ⟨es,u,r,h,hu⟩ := start (pub := pub) (macros := macros) s m seven width table length
  obtain ⟨fs,z,next,hn,hz⟩ := loop_run (pub := pub) (macros := macros) m tasks space rows 0 (Nat.zero_le _) u hu
  refine ⟨_,z,r.seq next,?_,hz⟩
  rw [show traceCost (es++fs) = traceCost es + traceCost fs from VPVNP.RAMBuckets.cost_append ..]
  simp only [Nat.Ico_zero_eq_range] at hn
  omega

end RoutingISA.TypedBatch

end BorderVNP
end Computability
end OAI
