import OAI.Hierarchy.DescentOrdinaryParallelSide
import OAI.Hierarchy.DescentOrdinaryParentBlocks
import OAI.Hierarchy.DescentOrdinaryDonorOrder

namespace OAI
/-! # A short two-sided comparison equals the true ordinary source-grouped chronology -/
namespace Hierarchy.DescentParallelBase
open DescentStageEdgeReceipt DescentOrdinaryDonorHalo DescentCableDonorNames
open scoped Classical
noncomputable section
variable {E U : Type} [Fintype E] {K D L : ℕ}

theorem grouped_compare (t : Tape E) (src : E→U) (site : U↪ℕ) (width : E→ℕ) (e f : E)
    (ep : 0<width e) (fp : 0<width f) :
    t.sourceKey src site width e<t.sourceKey src site width f ↔ site (src e)<site (src f) ∨ src e=src f ∧ t.ancestry e<t.ancestry f:=by
  have limit (i : E) : t.ancestry i<pitch t.ancestry:=Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
  simp only [Tape.sourceKey,Function.Embedding.coeFn_mk,ite_eq_left ep,ite_eq_left fp,Tape.grouped,grouped_val,lex (limit e) (limit f),Function.Embedding.apply_eq_iff_eq]

/-- At the upper end of an undirected pair the sources can differ. The
one orientation bit separates the source bands. For equal sources the
actual rebase comparator uses the prior donor slot and immutable raw role. -/
theorem ticket_compare (t : Tape E) (src dst : E→U) (site : U↪ℕ) (width : E→ℕ) (e f : E) (a b : Entry D K L)
    (ep : 0<width e) (fp : 0<width f) (parallel : (src e=src f ∧ dst e=dst f) ∨ (src e=dst f ∧ dst e=src f))
    (side_e : a.upper=side site (src e) (dst e)) (side_f : b.upper=side site (src f) (dst f))
    (localOrder : src e=src f→(t.sourceKey src site width e<t.sourceKey src site width f ↔ a.ticket<b.ticket)) :
    priority a<priority b ↔ t.sourceKey src site width e<t.sourceKey src site width f :=by
  rw [priority,priority,side_e,side_f,orient site parallel a.ticket b.ticket,grouped_compare t src site width e f ep fp]
  by_cases same : src e=src f
  · have equivalence: t.ancestry e<t.ancestry f ↔ a.ticket<b.ticket:=
      (t.sourceKey_lt src site width e f ep fp same).symm.trans (localOrder same)
    simp [same,equivalence]
  · simp [same]

end
end Hierarchy.DescentParallelBase

end OAI
