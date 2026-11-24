import OAI.Computability.VPVNP.LiveCompressedPairHandoff

/-! # Readback of actual online and terminal memory through both pair dispatches -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair
open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.Schedule LiveStageLink

variable {w d initial phases : ℕ} {C : Catalog d}
variable {b : Bootstrap} {plan : Online.Config C initial phases} {finalTable : PairTable} {pub : Fin 11 → Word w}

private theorem afterCons (m : Memory w) (r : Report w) (rs : List (Report w)) :
    after m (eventLog (r :: rs)) = after (after m r.events) (eventLog rs) := by
  simp only [eventLog,List.flatMap_cons,after,List.foldl_append]

private theorem completed_after {s : Stage} {f : ℕ} {st : Word w} {m : Memory w}
    {bs : List (List Bool)} {rs : List (Report w)} {last : Memory w}
    (h : Completion (components b plan finalTable) next pub (PairTag.address pub) s f st m bs rs last) :
    after m (eventLog (rs.map (report pub s))) = transferMemory (PairTag.address pub) (next s) last := by
  induction h with
  | last _ hh _ =>
    rw [List.map_cons,afterCons,(report_effect pub s _ _).2.2.2,hh]
    cases next s <;> rfl
  | more _ hh _ _ ih =>
    rw [List.map_cons,afterCons,(report_effect pub s _ _).2.2.2,hh]
    exact ih

theorem online_after {clock : ℕ} {m : Memory w}
    (a : StagePaths b plan finalTable pub clock Stage.online m) :
    after m (eventLog (onlineReports a)) = onlinePost a :=
  completed_after (completion_of_run (ordinaryRun a) a.property.choose_spec.2.1 a.property.choose_spec.2.2)

theorem terminal_after (m : Memory w) (rs : List (Report w)) :
    after m (eventLog (rs.map (report pub Stage.terminal))) = after m (eventLog rs) := by
  induction rs generalizing m with
  | nil => rfl
  | cons r rs ih =>
    rw [List.map_cons,afterCons,afterCons,(report_effect pub Stage.terminal r m).2.2.2]
    cases r.result <;> exact ih _

/-- Replaying the complete nested reports leaves precisely the physical
terminal worker's final memory, including its counter writes. -/
theorem joined_after (m : Memory w) (startup : List (Report w)) {clock : ℕ}
    (a : StagePaths b plan finalTable pub clock Stage.online (after m (eventLog startup)))
    (rs : List (Report w)) :
    after m (eventLog (startup ++ (onlineReports a ++ rs.map (report pub Stage.terminal)))) =
      after (onlinePost a) (eventLog rs) := by
  have append (mem : Memory w) (x y : List (Report w)) :
      after mem (eventLog (x++y)) = after (after mem (eventLog x)) (eventLog y) := by
    simp only [eventLog,List.flatMap_append,after,List.foldl_append]
  rw [append,append,online_after,terminal_after]

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
