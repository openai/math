import OAI.Hierarchy.TaggedWideScatterOrder
import OAI.Hierarchy.TaggedWideSpillLayout

namespace OAI
/-! # Physical nonoverlap of the three corrected role archives and every subsequent control scatter -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open ProbeStage.CoreBoard.HistoryRoles
open scoped Classical BigOperators
variable {T : ℕ} (z : SpillDates T)
local notation "g" => z.original

private theorem role_pages (rom start : ℕ) :
    Ordered start ((g).rolesEnd (z.roleRoot start 2)) (z.roleSheet rom start) := by
  have endAt : (g).rolesEnd (z.roleRoot start 2)=start+(3*((T+1)*3))*(g).roleSpan := by
    change start+2*((T+1)*(3*(g).roleSpan))+(T+1)*(3*(g).roleSpan)=_
    ring
  rw [endAt]
  apply Ordered.spaced (gap:=(g).roleSpan)
  · intro i
    obtain ⟨⟨family,x⟩,rfl⟩:=finProdFinEquiv.surjective i
    obtain ⟨⟨date,field⟩,rfl⟩:=finProdFinEquiv.surjective x
    simp only [SpillDates.roleSheet,Equiv.symm_apply_apply,Scatter.floor,Dated.rolePage,SpillDates.roles,
      Dated.roleStart,DatedRoleSheets.sheet,DatedRoleSheets.sink,SpillDates.roleRoot,Dated.roleSpan,
      Dated.roleWords,finProdFinEquiv_apply_val,Nat.add_sub_cancel]
    ring
  · intro i
    obtain ⟨⟨family,x⟩,rfl⟩:=finProdFinEquiv.surjective i
    obtain ⟨⟨date,field⟩,rfl⟩:=finProdFinEquiv.surjective x
    apply le_of_eq
    simp only [SpillDates.roleSheet,Equiv.symm_apply_apply,Scatter.stop,Dated.rolePage,SpillDates.roles,
      Dated.roleStart,DatedRoleSheets.sheet,DatedRoleSheets.sink,SpillDates.roleRoot,Dated.roleSpan,
      Dated.roleWords,DatedRoleSheets.span,finProdFinEquiv_apply_val]
    ring

theorem SpillDates.ordered (rom oldWork start : ℕ) (count : ∀j,(g).controlColumns j=SiteControls.fieldCount (g).roleCount) :
    Ordered start (z.endAt start) (z.sheets rom oldWork start count) := by
  let root:=z.roleRoot start 2
  have roles:=role_pages z rom start
  have a : Ordered ((g).rolesEnd root) ((g).controlStart root) (z.ballot rom oldWork start) := by
    apply party_order g (g).ballot ((g).rolesEnd root)
    intro j
    simp [SpillDates.ballot,root,Scatter.floor,Scatter.stop,Dated.ballotStart,Shape.sheet,Shape.span,Nat.add_assoc]
  have b : Ordered ((g).controlStart root) ((g).maskStart root) (z.packetControl rom oldWork start) := by
    apply party_order g (g).control ((g).controlStart root)
    intro j
    simp [SpillDates.packetControl,root,Scatter.floor,Scatter.stop,Dated.controlBase,Shape.sheet,Shape.span,Nat.add_assoc]
  have c : Ordered ((g).maskStart root) (z.endAt start) (fun j=>z.spillControl rom oldWork start j count) := by
    apply party_order g (g).control ((g).maskStart root)
    intro j
    simp [SpillDates.spillControl,SpillDates.spillStart,root,Scatter.floor,Scatter.stop,Shape.sheet,Shape.span,Nat.add_assoc]
  have rs : start≤(g).rolesEnd root := by change start≤ start+_+_;omega
  have ra : (g).rolesEnd root≤(g).controlStart root:=Nat.le_add_right ..
  have ab : (g).controlStart root≤(g).maskStart root:=Nat.le_add_right ..
  have bc : (g).maskStart root≤z.endAt start:=Nat.le_add_right ..
  have aligned:=Ordered.append rs ((ra.trans ab).trans bc) roles
    (Ordered.append ra (ab.trans bc) a (Ordered.append ab bc b c))
  exact ⟨fun i=>aligned.lower (Fin.cast _ i),fun i=>aligned.upper (Fin.cast _ i),
    fun i j hij=>aligned.separate (Fin.cast _ i) (Fin.cast _ j) hij⟩

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
