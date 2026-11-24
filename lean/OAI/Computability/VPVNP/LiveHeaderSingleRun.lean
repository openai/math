import OAI.Computability.VPVNP.LiveHeaderScalarStages
import OAI.Computability.VPVNP.LiveHeaderPrefix

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule

/-- One scalar stage in the combined instruction table, including the native
handoff write and cursor reset. -/
theorem SingleRun.prefix {w : ℕ} {s : Sizes} {base : ℕ} {st : Stage} {m final : Memory w}
    (run : SingleRun s base st m final) (id : StageId) (hid : stage id = st) (hc : calls s st = 1) :
    ∃ x : StageTrace w, x.id = id ∧ x.Good s ∧
      StagePrefix s base (some id) m [x] (next id)
        (LiveStageLink.transferMemory (Fin.ofNat _ base) (next id) final) := by
  obtain ⟨es,hr,hm,_,hp,_⟩ := run
  let rep : Report w := ⟨es,none⟩
  let x : StageTrace w := ⟨id,40,[[]],[rep]⟩
  have hx : x.Exec s base m := by
    constructor
    · change runSegment ((stageTemplate (stage id)).2.instantiate w (rowData w s base (stage id))).program
        40 (some 0) m [[]] = some [rep]
      rw [hid]
      simp [runSegment,hr,rep]
    · rfl
    · exact LiveStageLink.PreservesTagOnReturns.singleton_accept _ _ _ rfl
  have hgood : x.Good s := by
    simp only [StageTrace.Good,x,hid,hc,List.replicate_succ,List.replicate_zero,List.length_singleton,
      List.mem_singleton,forall_eq,le_refl,true_and]
    exact hp
  have hend : x.finalMem (Fin.ofNat _ base) m =
      LiveStageLink.transferMemory (Fin.ofNat _ base) (next id) final := by
    simp [StageTrace.finalMem,x,rep,eventLog,hm]
  exact ⟨x,rfl,hgood,hend ▸ StagePrefix.single hx⟩

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
