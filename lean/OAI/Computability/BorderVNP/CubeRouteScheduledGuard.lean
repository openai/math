import OAI.Computability.BorderVNP.CubeRouteCompleteSchedule
import OAI.Computability.BorderVNP.CubeRouteIncidentCapacity
import OAI.Computability.BorderVNP.CubeRouteWrittenVolume
import OAI.Computability.BorderVNP.TransmissionInverseBit

/-! # The actual checked-budget subtrace of the returned group program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open BorderVNP.Cube VPVNP.BurstRAM

variable {w n bits : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {r t : Bank w} {m mt : Memory w} {es : List (TeamRAM.Event w)}

/-- The physical check runs on the same RAM that the group prefix returns. Its event
stream is a genuine chronological suffix of the group's public event stream. -/
theorem groupPrefix_budget_return (run : Runs pub mac (LocalRow.groupPrefix n bits) r m es t mt) :
    ∃ prior tail u, es = prior++tail ∧ Runs pub mac TeamBudget.check u mt tail t mt := by
  let first := [LabelIndex.directoryProgram,NativeIntervals.prepare,CubePowers.install,
    CubeHeaderInstall.install n bits,HeaderDecode.program,CubeLengths.minimum]
  change Runs pub mac (.block (first++[GroupWeights.checkedSchedule])) r m es t mt at run
  obtain ⟨v,mv,fs,gs,h,_,group⟩ := Runs.seq_iff.mp
    ((Runs.block_append_iff (List.cons_ne_nil _ _ : first ≠ []) (by decide : [GroupWeights.checkedSchedule] ≠ [])).mp run)
  obtain ⟨u,mu,ds,hs,k,_,guard⟩ := Runs.seq_iff.mp group
  have back := guard.memory_eq_of_storeFree (by decide)
  subst mu
  exact ⟨fs++ds,hs,u,by rw [h,k,List.append_assoc],guard⟩

/-- The actual group, capacity check and directory continuation within a return of the entire schedule. -/
theorem WriterHistory.groupBudget (H : WriterHistory n bits pub mac r m es t mt) :
    ∃ v mv first rest u prior guard,
      H.prefixTrace = first++rest ∧ Runs pub mac (LocalRow.groupPrefix n bits) r m first v mv ∧
      first = prior++guard ∧ Runs pub mac TeamBudget.check u mv guard v mv ∧
      Runs pub mac (.seq CellBanks.install PairDirectory.directory) v mv rest H.dataRegs H.dataInput := by
  let ps := [LabelIndex.directoryProgram,NativeIntervals.prepare,CubePowers.install,
    CubeHeaderInstall.install n bits,HeaderDecode.program,CubeLengths.minimum,GroupWeights.checkedSchedule]
  have split : Runs pub mac (.block (ps++[CellBanks.install,PairDirectory.directory])) r m H.prefixTrace H.dataRegs H.dataInput :=
    H.prefixRun
  obtain ⟨v,mv,fs,gs,whole,first,tail⟩ := Runs.seq_iff.mp
    ((Runs.block_append_iff (List.cons_ne_nil _ _ : ps ≠ []) (by decide : [CellBanks.install,PairDirectory.directory] ≠ [])).mp split)
  obtain ⟨prev,guard,u,sub,pass⟩ := groupPrefix_budget_return (n := n) (bits := bits) first
  exact ⟨v,mv,fs,gs,u,prev,guard,whole,first,sub,pass,tail⟩

/-- Numeric room and the physical frame of the guard on the actual post-assignment memory. -/
theorem scheduled_budget_frame {l : GroupWeights.Layout} {team : TeamNative.Layout} {X : ℕ}
    {orig : ℕ → ℕ} (checked : GroupWeights.CheckedFrame l team orig w X)
    (assigned : GroupWeights.ScheduleResult l team orig (readings mt)) (base : (pub 0).val = l.frame) :
    let budget : TeamBudget.Layout := ⟨team.r+1,X,team.totals⟩
    budget.Fields (readings pub 0) (readings mt) ∧ budget.Fits (readings pub 0) w := by
  intro budget
  change budget.Fields (pub 0).val (readings mt) ∧ budget.Fits (pub 0).val w
  rw [base]
  have keep (j : ℕ) (hj : j ∈ [1,31,76]) : readings mt (l.frame+j) = orig (l.frame+j) :=
    assigned.other _ (checked.keepBudget j hj).1 (checked.keepBudget j hj).2.1 (checked.keepBudget j hj).2.2
  exact ⟨⟨(keep 1 (by decide)).trans checked.budgetFields.teams,(keep 31 (by decide)).trans checked.budgetFields.X₀,
    (keep 76 (by decide)).trans checked.budgetFields.totals⟩,checked.budgetFits⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
