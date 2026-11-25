import OAI.Hierarchy.DescentResetPeerCandidates

namespace OAI
/-! # Decoding the self and neighbor socket numbers in a reset frame -/
namespace Hierarchy.DescentResetPeerUnionRAM.Candidates
open DescentSIMDLookup
open scoped Classical
variable {H D S w : ℕ}

theorem self_value (old : Fin H→Fin D→Option (Fin H)) (v x : Fin (H*S)) (other : Fin S) :
    (∃j : Fin (count S D),candidate old v j=some x ∧ D*S+other.val+1=j.val+1) ↔
      x=finProdFinEquiv ((finProdFinEquiv.symm v).1,other) := by
  obtain ⟨⟨parent,here⟩,rfl⟩:=finProdFinEquiv.surjective v
  rw [Equiv.symm_apply_apply]
  have read:=selfKey old parent here other
  have value : (atSlot (Fin.last D) other).val=D*S+other.val:=atSlot_val _ _
  constructor
  · rintro ⟨j,physical,num⟩
    have same : j=atSlot (Fin.last D) other:=Fin.ext (by omega)
    rw [same,read] at physical
    exact (Option.some.inj physical).symm
  · rintro rfl
    exact ⟨_,read,by omega⟩

theorem socket_value (old : Fin H→Fin D→Option (Fin H)) (v x : Fin (H*S)) (socket : Fin D) (other : Fin S) :
    (∃j : Fin (count S D),candidate old v j=some x ∧ socket.val*S+other.val+1=j.val+1) ↔
      (old (finProdFinEquiv.symm v).1 socket).map (fun parent=>finProdFinEquiv (parent,other))=some x := by
  obtain ⟨⟨parent,here⟩,rfl⟩:=finProdFinEquiv.surjective v
  rw [Equiv.symm_apply_apply]
  have read:=specific old parent here socket other
  have value : (atSlot socket.castSucc other).val=socket.val*S+other.val:=atSlot_val _ _
  constructor
  · rintro ⟨j,physical,num⟩
    have same : j=atSlot socket.castSucc other:=Fin.ext (by omega)
    simpa only [same,read] using physical
  · intro yes
    exact ⟨_,read.trans yes,by omega⟩

end Hierarchy.DescentResetPeerUnionRAM.Candidates

end OAI
