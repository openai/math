import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card

namespace OAI
/-! # Bounded port ranks in the increasing order of the actual physical site IDs -/
namespace Hierarchy.DescentPackedExchange
open scoped Classical
noncomputable section
variable {V : Type} {H : ℕ}
private theorem siteCount (name : V≃Fin H) (ns : Finset V) :
    (ns.map name.toEmbedding).card=Fintype.card ns := by simp

def neighborOrder (name : V≃Fin H) (ns : Finset V) : ns≃Fin (Fintype.card ns) :=
  (Finset.equivMap name.toEmbedding ns).trans
    ((ns.map name.toEmbedding).orderIsoOfFin (siteCount name ns)).symm.toEquiv

theorem neighborOrder_read (name : V≃Fin H) (ns : Finset V) (j : Fin (Fintype.card ns)) :
    name ((neighborOrder name ns).symm j).val=
      ((ns.map name.toEmbedding).sort (·≤·))[j.val]'(by simpa using j.isLt) := by
  let S:=ns.map name.toEmbedding
  let p : ns≃S := Finset.equivMap name.toEmbedding ns
  let q:=S.orderIsoOfFin (siteCount name ns)
  have eq : name ((neighborOrder name ns).symm j).val=(q j).val :=
    congrArg Subtype.val (p.apply_symm_apply (q j))
  exact eq.trans ((S.coe_orderIsoOfFin_apply (siteCount name ns) j).trans
    (S.orderEmbOfFin_apply (siteCount name ns) j))

end
end Hierarchy.DescentPackedExchange

end OAI
