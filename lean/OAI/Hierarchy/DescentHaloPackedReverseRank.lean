import OAI.Hierarchy.DescentHaloChartHeader
import OAI.Hierarchy.DescentHaloRebaseRAM

namespace OAI
/-! # A raw forward path reads the actual reverse rank in its receiver's chart -/
namespace Hierarchy.DescentHaloPackedRebase
open DescentSharedCableNames
open scoped Classical
noncomputable section
variable {H : ℕ}

/-- The physical raw rank from an actual forward old endpoint path becomes
a one-based local donor digit on the packed occurrence, as required by its
collector. Every ghost and every unsuccessful forward path maps to zero. -/
theorem actual {D : ℕ} (R : Fin H→Fin D→Option (Fin H)) («mutual» : ∀v u i,R v i=some u→∃j,R u j=some v)
    (v u : Fin H) (p : Fin (DescentHaloWalkRAM.breadth D)) (hit : DescentHaloWalkRAM.walk R v (DescentHaloWalkRAM.path p) 4=some u) :
    let rank:=DescentHaloWalkRAM.Ranks.earlier (DescentHaloWalkRAM.Rebase.terminal R) u v.val
    ∃s : Fin (DescentHaloWalkRAM.breadth D),s.val=rank ∧ fetch _ (digest (DescentHaloWalkRAM.Rebase.digit R .rank v)) (Packed.token (some p))=Packed.token (some s) :=by
  intro rank;obtain ⟨q,back,_,calcRank⟩:=DescentHaloWalkRAM.Rebase.actual R «mutual» v u p hit
  have re : DescentHaloWalkRAM.Rebase.terminal R u q=v.val:=by simp [DescentHaloWalkRAM.Rebase.terminal,back,DescentHaloWalkRAM.number]
  have less :=DescentHaloWalkRAM.Ranks.bound (DescentHaloWalkRAM.Rebase.terminal R) u q
  rw [re] at less;exact ⟨⟨rank,less⟩,rfl,fetch_at _ _ _ calcRank⟩

end
end Hierarchy.DescentHaloPackedRebase

end OAI
