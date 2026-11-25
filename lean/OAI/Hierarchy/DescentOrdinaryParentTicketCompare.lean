import OAI.Hierarchy.DescentHaloRebaseRAM
import OAI.Hierarchy.DescentCableDonorNames

namespace OAI
/-! The rank digit in two retained parents can be compared at their common new source. -/
namespace Hierarchy.DescentOrdinaryIssuedTicket
open DescentHaloWalkRAM
open scoped Classical
noncomputable section
variable {H D size : ℕ} (R : Fin H→Fin D→Option (Fin H))
variable (symmetric : ∀v u i,R v i=some u→∃j,R u j=some v)
variable (a b center : Fin H) (p q : Fin (breadth D))
    (ha : walk R a (path p) 4=some center) (hb : walk R b (path q) 4=some center)

include symmetric ha hb in
theorem anchor_order (x y : Fin size) :
    Rebase.value R .rank a p*size+x.val < Rebase.value R .rank b q*size+y.val ↔
       a.val<b.val ∨ a=b ∧ x<y :=by
  obtain ⟨pa,backA,_,rankA⟩:=Rebase.actual R symmetric a center p ha
  obtain ⟨pb,backB,_,rankB⟩:=Rebase.actual R symmetric b center q hb
  have oldA:Rebase.terminal R center pa=a.val:=by simp [Rebase.terminal,backA,number]
  have oldB:Rebase.terminal R center pb=b.val:=by simp [Rebase.terminal,backB,number]
  have ab:=Ranks.compare (Rebase.terminal R) center pa pb
  have ba:=Ranks.compare (Rebase.terminal R) center pb pa
  rw [oldA,oldB] at ab ba
  rw [rankA,rankB,DescentCableDonorNames.digit_lt x.isLt y.isLt,ab]
  have eqn:Ranks.earlier (Rebase.terminal R) center a.val=Ranks.earlier (Rebase.terminal R) center b.val ↔ a=b:=by
    constructor
    · intro eqn;apply Fin.ext;exact le_antisymm (not_lt.mp (fun gt=>((ba.2 gt).ne) eqn.symm))
        (not_lt.mp (fun gt=>((ab.2 gt).ne) eqn))
    · rintro rfl;rfl
  simp only [eqn,Fin.lt_def]

end
end Hierarchy.DescentOrdinaryIssuedTicket

end OAI
