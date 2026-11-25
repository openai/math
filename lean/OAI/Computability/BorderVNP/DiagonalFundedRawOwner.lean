import OAI.Computability.BorderVNP.CubePhysicalGreedyTally
import OAI.Computability.BorderVNP.CubeScatterTransmissionRouted

/-! # The registered owner on the exact routed declaration -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open BorderVNP.Cube Physical Scatter.Assignment

variable {n d blocks b h K s R cells : ℕ} {A : Type*} [Fintype A]
    {label : Fin cells → Label (n+1) d} {recv : A → Fin cells} {amount : A → ℕ}
    {decl : LengthDeclaration n d}

local notation3 (prettyPrint := false) "owns" =>
  greedyOwner (blocks:=blocks) (K:=K) (h:=h) R b s label recv amount

/-- Each original cell lies in the allocated range. The native owner selected
by its decoded label is the greedy owner of the routed selector's chosen axis
when the advertised declaration is the one spelled by that route. -/
theorem fundedOwnerOfRoute {q : NativeAssignments.Routed (b:=b) (s:=s) owns}
    (matched : (Routed.encode owns q).declaration=decl) (c : Fin cells) :
    (if hc : c.val<cells then
      TeamNative.owner R (declarationWeight blocks b K h decl label recv amount) (label ⟨c.val,hc⟩ decl.1).val
     else 0).val = (owns q.1 (label c (chosen b s q.1))).val := by
  simp only [dite_eq_left c.isLt,Fin.eta]
  have same : Routed.trueDeclaration b s q.1 = decl := matched
  exact (congrArg (fun d' : LengthDeclaration n d =>
    (TeamNative.owner R (declarationWeight blocks b K h d' label recv amount) (label c d'.1).val).val) same).symm

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
