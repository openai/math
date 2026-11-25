import OAI.Hierarchy.DescentOrdinaryRetainedParentRanks
import OAI.Hierarchy.DescentParentFilterRoster

namespace OAI
/-! # The selected old donor column and the first serial at each surviving cable end -/
namespace Hierarchy.DescentParallelBase.ParentFilter.Measured
open DescentSharedCableNames DescentHaloWalkRAM
noncomputable section
variable {U E X T V : Type} [Fintype E] [DecidableEq U] [Fintype X] [Fintype T]
  {n D H Q O K L : ℕ} {B : Ends U n} (C : Blocks B E)
  (R : Fin H→Fin D→Option (Fin H)) (symm : ∀v u i,R v i=some u→∃j,R u j=some v)
  (Z : Measured C R X T V Q O K L)

theorem address_at (h:U) (e:Local C h) (p:Fin (breadth D)) (o:Fin O)
    (chosen:Gather.select (Gather.reaching R) (Z.venue h).1 p=some (Z.loc (Z.raw h e)).1)
    (column:(Z.loc (Z.raw h e)).2=o):
    (roster C R symm Z).address h e=finProdFinEquiv (p,o):=by
  let old:=Z.loc (Z.raw h e)
  have unique:=Gather.once (Gather.reaching R) (Z.venue h).1 old.1 (near C R symm Z h e)
  have picked:=Resident.visit_read C h (fun u=>(Z.venue u).1) Z.loc (Z.raw h)
    (Gather.reaching R) (near C R symm Z h) e
  change finProdFinEquiv (visit C R symm Z h e,(Z.loc (Z.raw h e)).2)=_
  have path:visit C R symm Z h e=p:=unique.unique picked chosen
  rw [path,column]

end
end Hierarchy.DescentParallelBase.ParentFilter.Measured

namespace Hierarchy.DescentOrdinarySignedAll
open DescentSixParty DescentColonies DescentSharedCableNames DescentParallelBase
open DescentOrdinarySignedRanks
noncomputable section
variable {F P V J E : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] [Fintype E]
  {d k i Q T K X H gg:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
  (A:GroupStage W G price ε J V k) (native:W.graph.Edge↪ℕ) (S:DescentCompiler.AtomSchedule) (ready:A.StateBounds S i)
local notation "Host" => Stage.Host J V k
variable (names:Stage.Host J V k↪ℕ) (C:Blocks (Stage.source A native) E) (marked:E→Prop)
  (emit:DescentResetWindowFields.Emission A native C marked)
  (Z:Incidence.Census C Q T A.cap K) (home:Fin X→Fin H→Fin gg→Option (Stage.Host J V k))

omit [Fintype E] in
theorem first_serial_live (x:Fin X) (v:Fin H) (g:Fin gg) (h:Host) (found:home x v g=some h)
    (e:Local C h) (side:Bool) :
    result C Z home (Stage.measured A native S ready) x 1 (Z.addr h e) v g =
      (DescentPackedOperand.Public.endpoint A native S ready names side
        (emit.units ⟨e.val,⟨0,e.property.1⟩⟩)).wire.val:=by
  calc
    _ = _ := first_serial_at A native S ready C Z home x v g h found e
    _ = _ := by
      simpa only [Nat.add_zero] using
        (DescentResetWindowFields.serial A native S ready names C marked emit e.val ⟨0,e.property.1⟩ side).symm

end
end Hierarchy.DescentOrdinarySignedAll

end OAI
