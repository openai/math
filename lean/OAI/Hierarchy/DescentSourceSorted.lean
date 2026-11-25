import OAI.Hierarchy.DescentStageEdgeReceipt
import OAI.Hierarchy.DescentStageReindex
import OAI.Hierarchy.DescentPhysicalOrder

namespace OAI
/-! # Sorting positive cables by their actual installed source site -/
namespace Hierarchy.DescentSixParty
open DescentStageEdgeReceipt DescentPacking DescentPhysicalOrder
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {n : ℕ} {bits : P→ℕ}

def SourceSorted (W : MarkedWorld F n P bits) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) : Prop :=
  ∀e f,0<W.graph.width e→0<W.graph.width f→
    originalId W.graph.Site (W.graph.src e)<originalId W.graph.Site (W.graph.src f)→ order e<order f

abbrev IntrinsicallySorted (W : MarkedWorld F n P bits) := SourceSorted W (Fintype.equivFin W.graph.Edge).toEmbedding

omit [Field F] in
theorem IntrinsicallySorted.expose {W : MarkedWorld F n P bits} (h : IntrinsicallySorted W)
    (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (actual : ∀e,originalId W.graph.Edge e=(order e).val) :
    SourceSorted W order := by
  intro e f ep fp less
  change (order e).val<(order f).val
  rw [←actual,←actual];exact h e f ep fp less

theorem sourceKey_before {E V : Type} [Fintype E] (t : Tape E) (src : E→V) (location : V↪ℕ)
    (width : E→ℕ) (e f : E) (ep : 0<width e) (fp : 0<width f) (less : location (src e)<location (src f)) :
    t.sourceKey src location width e<t.sourceKey src location width f := by
  have drop : t.ancestry e<pitch t.ancestry:=Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ e))
  have step:=Nat.mul_le_mul_right (pitch t.ancestry) less
  rw [Nat.succ_mul] at step
  simp only [Tape.sourceKey,Function.Embedding.coeFn_mk,ite_eq_left ep,ite_eq_left fp,Tape.grouped,
    DescentCableDonorNames.grouped_val]
  omega

omit [Field F] in
theorem physically_sorted (W : MarkedWorld F n P bits) (t : Tape W.graph.Edge) (id : W.graph.Site↪ℕ) :
    IntrinsicallySorted (PhysicalRename.world W (rename id) (rename (t.sourceKey W.graph.src id W.graph.width))) := by
  let k:=t.sourceKey W.graph.src id W.graph.width
  let s:=rename id
  let e:=rename k
  intro i j
  obtain ⟨u,rfl⟩:=e.surjective i
  obtain ⟨v,rfl⟩:=e.surjective j
  change 0<W.graph.width (e.symm (e u))→0<W.graph.width (e.symm (e v))→
    (Fintype.equivFin W.graph.Site (s (W.graph.src (e.symm (e u))))).val <
      (Fintype.equivFin W.graph.Site (s (W.graph.src (e.symm (e v))))).val →
    Fintype.equivFin W.graph.Edge (e u)<Fintype.equivFin W.graph.Edge (e v)
  simp only [Equiv.symm_apply_apply,s,e,code_rename]
  intro ep fp old
  apply (physical_lt_iff k u v).2
  exact sourceKey_before t W.graph.src id W.graph.width u v ep fp
    ((physical_lt_iff id (W.graph.src u) (W.graph.src v)).1 old)

end
end Hierarchy.DescentSixParty

end OAI
