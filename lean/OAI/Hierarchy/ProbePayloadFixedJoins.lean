import OAI.Hierarchy.ProbeFabricBoard
import OAI.Hierarchy.ProbeRoutedSocketKeys

namespace OAI
/-! # Every free join of the actual routed payload strip belongs to the public permutation fabric -/
namespace Hierarchy.ProbeStage
noncomputable section
set_option quotPrecheck false

variable {h d : ℕ} (π : Equiv.Perm (Fin (2^h)))
local notation "N" => (permutationFabric h d).shapes.length
local notation "R" => Fin (2^h)

private def routePair (p : R) (t : StageAt h d) : (permutationFabric h d).Column × (permutationFabric h d).Column :=
  ((advisedRoute h d π).socketPairs p).get
    ⟨t.val,by simpa only [(advisedRoute h d π).socketPairs_length] using t.isLt⟩

private theorem routePair_at (p : R) (t : StageAt h d) :
    ((advisedRoute h d π).socketPairs p)[t.val]?=some (routePair π p t) :=
  List.getElem?_eq_getElem (by simpa only [(advisedRoute h d π).socketPairs_length] using t.isLt)

private theorem unflatten_route (p : R) (t : StageAt h d) (side : Bool) :
    (permutationFabric h d).unflatten ⟨t,(advisedStage h d π t).socket (s:=stageAt h d t) p side⟩=
      pairSocket side (routePair π p t) := by
  obtain ⟨l,selected,tag⟩:=Option.map_eq_some_iff.mp (advised_socket_tag h d π t p side)
  apply (permutationFabric h d).socketKey_injective
  rw [(permutationFabric h d).socketKey_unflatten,(advisedRoute h d π).socketPair_key p t.val _ l (routePair_at π p t) selected side,tag]
  rfl

private theorem output_board (p : R) (t : StageAt h d) :
    fabricBoard h d (payloadFreeFrom π p t.succ)=.inr (.inl (routePair π p t).2) := by
  rw [payloadFreeFrom,Fin.cases_succ,fabricBoard_stage]
  exact congrArg (fun c : (permutationFabric h d).Column=>Sum.inr (Sum.inl c)) (unflatten_route π p t true)

private theorem input_board (p : R) (t : StageAt h d) :
    fabricBoard h d (payloadFreeTo π p t.castSucc)=.inr (.inl (routePair π p t).1) := by
  rw [payloadFreeTo,Fin.lastCases_castSucc,fabricBoard_stage]
  exact congrArg (fun c : (permutationFabric h d).Column=>Sum.inr (Sum.inl c)) (unflatten_route π p t false)

/-- The identified free edges use the actual matching-independent fabric wiring, including
the two exterior joints. The matching only selects which already-present contact is used. -/
theorem payloadFree_fixed (p : R) (j : Fin (N+1)) :
    (permutationFabric h d).fixedAll (fabricBoard h d (payloadFreeFrom π p j)) (fabricBoard h d (payloadFreeTo π p j)) := by
  let route:=advisedRoute h d π
  have path:=route.socketSequence p
  have positive : 0<N := by simpa only [route.socketPairs_length] using path.nonempty
  by_cases zero : j.val=0
  · let t : StageAt h d:=⟨0,positive⟩
    have a : j=0 := Fin.ext zero
    have b : t.castSucc=j := Fin.ext zero.symm
    have right:=input_board π p t
    rw [b] at right
    rw [right,a]
    change (routePair π p t).1=(permutationFabric h d).firstColumn ((permutationTiles π).first p)
    exact path.first _ (routePair_at π p t)
  let prev : StageAt h d:=⟨j.val-1,by have:=j.isLt;omega⟩
  have pe : prev.succ=j := by apply Fin.ext;change j.val-1+1=j.val;omega
  have left:=output_board π p prev
  rw [pe] at left
  rw [left]
  by_cases stop : j.val=N
  · have last : j=Fin.last N := Fin.ext stop
    rw [last,payloadFreeTo,Fin.lastCases_last,fabricBoard_output]
    change (routePair π p prev).2=(permutationFabric h d).lastColumn ((permutationTiles π).last p)
    exact path.last prev.val _ (by rw [route.socketPairs_length];change j.val-1+1=N;omega) (routePair_at π p prev)
  · let next : StageAt h d:=⟨j.val,by have:=j.isLt;omega⟩
    have ne : next.castSucc=j := Fin.ext rfl
    have right:=input_board π p next
    rw [ne] at right
    rw [right]
    apply path.adjacent prev.val _ _ (routePair_at π p prev)
    have same : prev.val+1=next.val := by change j.val-1+1=j.val;omega
    rw [same]
    exact routePair_at π p next


end
end Hierarchy.ProbeStage

end OAI
