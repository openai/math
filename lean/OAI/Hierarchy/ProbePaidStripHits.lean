import OAI.Hierarchy.ProbePaidOccupancy
import OAI.Hierarchy.ProtocolRAMCalendarPaidReporter
import OAI.Hierarchy.ProtocolRAMCommittedTape

namespace OAI
/-! # The actual paid occurrence and its owner in the disjoint strip directory -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe Strip Calendar Calendar.StockCommit RepairHistogram
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical Fin.CommRing BigOperators

variable {w edges k rows ports q : ℕ} {Ball X : Type}

/-- The quotient/remainder enumerator is injective even when an arbitrary
number of preceding candidate rows were never admitted. The two physical
endpoints are allowed in either order. -/
theorem PaidWidths.Slice.strip_hits (s : PaidWidths.Slice) (m : Memory w) (e : Fin edges)
    (loc : Fin s.count ≃ (Σ _ : Fin rows,Fin ports)) (atRow : Ball ↪ Fin rows)
    (place : Ball×X ↪ Fin k) (geom : Fin edges→Chord k)
    (ends : Ball→Fin ports→DistinctPair X) (cap : ℕ)
    (live : ∀i : Fin s.count,0<(s.amount.eval m (i.val:Word w)).val →
      ∃p,atRow p=(loc i).1)
    (read : ∀p t,(s.edge.eval m ((loc.symm ⟨atRow p,t⟩).val:Word w)).val=e.val →
      0<(s.amount.eval m ((loc.symm ⟨atRow p,t⟩).val:Word w)).val →
      geom e=reportedRole place (ends p) p t)
    (bound : ∀i : Fin s.count,(s.amount.eval m (i.val:Word w)).val≤cap) :
    s.load m e≤ports*cap := by
  let owner (i : s.Positive m e) : Ball:=Classical.choose (live i.val i.property.2)
  have row (i : s.Positive m e) : atRow (owner i)=(loc i.val).1 :=
    Classical.choose_spec (live i.val i.property.2)
  have recover (i : s.Positive m e) : loc.symm ⟨atRow (owner i),(loc i.val).2⟩=i.val := by
    apply loc.injective
    rw [Equiv.apply_symm_apply]
    exact Sigma.ext (row i) (heq_of_eq rfl)
  apply s.live_load m e place (fun f=>(geom f).val.1) ports cap owner (fun i=>(loc i.val).2)
  · intro i
    have matchEdge:=read (owner i) (loc i.val).2
      (by rw [recover];exact i.property.1) (by rw [recover];exact i.property.2)
    rw [matchEdge]
    let : Fintype Ball := Fintype.ofInjective atRow atRow.injective
    exact reported_owner place (ends (owner i)) (owner i) (loc i.val).2
  · intro i j same slot
    apply Subtype.ext
    rw [←recover i,←recover j,same,slot]
  · intro i
    exact bound i.val

theorem Calendar.StockCommit.PortPlan.actual_width {st : Calendar.StockCommit}
    {b : Batch q ports} {v : Memory w} (P : PortPlan st b v rows) (i : Fin st.occurrences) :
    RepairHistogram.installedBits st.columns v i≤b.maxWidth*b.copies := by
  let t:=(P.enum.symm i).2
  have credit:=(fromBatch_read P.owner P.data P.dest P.ball P.field b P.tabs v (i.val:Word w)
    t P.portRoom (P.localIndex i)).1
  simp only [RepairHistogram.installedBits,P.columns,credit]
  exact b.wire_bound v _ _ P.termRoom P.copyRoom P.sumRoom

/-- Nonzero archived direct or mate credit implies a genuinely admitted
source row. The source is recovered without manufacturing an element of
an empty purchased board. -/
theorem Calendar.StockCommit.PortPlan.paid_hits {st : Calendar.StockCommit} {b : Batch q ports}
    {v : Memory w} (P : PortPlan st b v rows) (s : PaidWidths.Slice)
    (back : Fin s.count ≃ Fin st.occurrences) (m : Memory w) (e : Fin edges)
    (atRow : Ball ↪ Fin rows) (place : Ball×X ↪ Fin k) (geom : Fin edges→Chord k)
    (ends : Ball→Fin ports→DistinctPair X)
    (active : ∀j∈liveRows b v rows, ∃p,atRow p=j)
    (credit : ∀i : Fin s.count,(s.amount.eval m (i.val:Word w)).val ≤ RepairHistogram.installedBits st.columns v (back i))
    (read : ∀p t,
      (s.edge.eval m ((back.symm (P.enum ⟨atRow p,t⟩)).val:Word w)).val=e.val →
      0<(s.amount.eval m ((back.symm (P.enum ⟨atRow p,t⟩)).val:Word w)).val →
      geom e=reportedRole place (ends p) p t) :
    s.load m e≤ports*(b.maxWidth*b.copies) := by
  let loc:=back.trans P.enum.symm
  apply s.strip_hits m e loc atRow place geom ends _ _ read (fun i=>(credit i).trans (P.actual_width _))
  intro i positive
  apply active
  by_contra dead
  exact (Nat.not_lt_of_ge ((credit i).trans_eq (P.off (back i) dead).1)) positive

/-- The true archive equation, as returned by `Calendar.archived_credit`,
is sufficient for both physical charge columns. -/
theorem archive_widths (a : Calendar.StockCommit.Area) (s : Calendar.StockCommit.Sources)
    (g : Calendar.StockCommit.LabelSource) (_b : Batch q ports) (m v : Memory w)
    (isCatalyst mate : Expr) (size : a.occurrences≤2^w)
    (archive : ∀i : Fin a.occurrences,
      (m (a.direct+i.val)).val=if kind (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns v i=none
        then RepairHistogram.installedBits (fresh a s).columns v i else 0) :
    (∀i : Fin a.occurrences,((PaidWidths.paidDirect a s g).amount.eval m (i.val:Word w)).val≤
      RepairHistogram.installedBits (fresh a s).columns v i) ∧
    (∀i : Fin a.occurrences,((PaidWidths.paidMate a s isCatalyst mate).amount.eval m (i.val:Word w)).val≤
      RepairHistogram.installedBits (fresh a s).columns v i) := by
  constructor <;> intro i
  · rw [PaidWidths.paidDirect_bits _ _ _ m i size,archive]
    split <;> simp
  · rw [PaidWidths.paidMate_bits _ _ _ _ m i size,archive]
    split_ifs <;> simp

end Hierarchy.ProtocolRAM
end

end OAI
