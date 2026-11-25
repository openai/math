import OAI.Hierarchy.ProtocolRAMCommittedTape
import OAI.Hierarchy.ProtocolRAMLocalCharge

namespace OAI
/-! # Local committed prices from the actual packet histogram and audited RAM -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM
open RepairHistogram AdaptiveProbe
open ThreeFlat.Diagonal.MotifOuterTerms
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Fin.CommRing Classical
noncomputable section

variable {w q d rows : ℕ}

theorem PortPlan.funded {s : StockCommit} {b : Batch q d} {m : Memory w} (P : PortPlan s b m rows)
    (i : Fin s.goods) (position : ∀ j : Fin rows, ∀ a : Fin d,
      RepairHistogram.kind s.plan.bank s.columns m (P.enum ⟨j,a⟩)=some i →
        ((b.stock a).eval m (j.val:Word w)).val=(m (s.plan.bank.base+i.val)).val)
    (unique : ∀ u v : Fin s.occurrences, RepairHistogram.kind s.plan.bank s.columns m u=some i →
      RepairHistogram.kind s.plan.bank s.columns m v=some i → 0<consumedBits s.columns m u →
      0<consumedBits s.columns m v → u=v) :
    OuterBank.resourceBits (RepairHistogram.kind s.plan.bank s.columns m) (consumedBits (n:=s.occurrences) s.columns m) i≤
      (m (s.plan.bank.base+i.val)).val := by
  apply funded_of_unique _ _ (fun t : Fin s.goods=>(m (s.plan.bank.base+t.val)).val) i _ unique
  intro e hit
  obtain ⟨⟨j,a⟩,rfl⟩ := P.enum.surjective e
  rw [(P.read j a).2,←position j a hit]
  exact debit_funded b a m (j.val:Word w) P.termRoom P.copyRoom P.sumRoom

private theorem sum_on {E A : Type*} [Fintype E] [AddCommMonoid A] (ports : E↪Fin d) (f : Fin d→A)
    (zero : ∀ i,(∀ e,ports e≠i) → f i=0) : ∑i,f i=∑e,f (ports e) := by
  have bound : (∑i∈Finset.univ.map ports,f i)=∑i,f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ absent
    exact zero i fun e h=>absent (Finset.mem_map.mpr ⟨e,Finset.mem_univ _,h⟩)
  simpa using bound.symm

/-- Positive-demand aliases and ordinary-link options can have different signed
prices. Extra option positions in the shared ISA are zeroed in each local row. -/
theorem PortPlan.local_quote {F E A : Type*} [Field F] [Fintype E] [Fintype A]
    {k : ℕ} [Nonempty (Fin k)] {edge : E→Chord k} {req : A→E}
    (packet : Probe.Packet F edge req) (extra : ℕ) {s : StockCommit} {b : Batch (packet.terms+extra) d}
    {m : Memory w} (P : PortPlan s b m rows) (j : Fin rows) (live : j∈liveRows b m rows)
    (h : Histogram (Fin packet.terms) b.copies) (ports : E↪Fin d)
    (fields : ∀ t,((b.field t).eval m (j.val:Word w)).val=((padHistogram h extra).val t).val)
    (opts : ∀ e t,(P.tabs (ports e) t).eval m (j.val:Word w)=(padCounts packet.count extra t e:Word w))
    (need : ∀ e,((b.need (ports e)).eval m (j.val:Word w)).val=debited req (b.copies*packet.width) e)
    (inactive : ∀ i,(∀ e,ports e≠i) → installedBits s.columns m (P.enum ⟨j,i⟩)=0 ∧
      consumedBits s.columns m (P.enum ⟨j,i⟩)=0)
    (bounded : ∀ t e,packet.count t e≤b.maxWidth) (fits : b.maxWidth<2^w) (wide : b.copies*b.maxWidth<2^w)
    (price : Fin d→ℝ) (quoted : E→ℝ) (broadcast tree err γ : ℝ) (nonneg : 0≤err)
    (accuracy : ∀ e,quoted e≤price (ports e) ∧ price (ports e)≤quoted e+err)
    (treeCost : broadcast=b.copies*(tree*packet.selectorBits))
    (catalogue : (∑ e,(histWidth packet.count h e:ℝ)*quoted e)+b.copies*(tree*packet.selectorBits)≤
      b.copies*((packet.width:ℝ)*((∑ a,quoted (req a))-γ)))
    (resolution : (Fintype.card E:ℝ)*b.maxWidth*err≤packet.width*γ/2) :
    (∑ i,(installedBits s.columns m (P.enum ⟨j,i⟩):ℝ)*price i)+broadcast+b.copies*(packet.width*γ/2)≤
     ∑ i,(consumedBits s.columns m (P.enum ⟨j,i⟩):ℝ)*price i := by
  have active : committed b m (j.val:Word w) := (Finset.mem_filter.mp live).2
  rw [sum_on ports (fun i=>(installedBits s.columns m (P.enum ⟨j,i⟩):ℝ)*price i)
    (by intro i miss; simp [(inactive i miss).1]),treeCost,
    sum_on ports (fun i=>(consumedBits s.columns m (P.enum ⟨j,i⟩):ℝ)*price i)
    (by intro i miss; simp [(inactive i miss).2])]
  have read (e : E) : consumedBits s.columns m (P.enum ⟨j,ports e⟩)=debited req (b.copies*packet.width) e := by
    rw [(P.read j (ports e)).2,debit_eval b (ports e) m (j.val:Word w) P.termRoom P.copyRoom P.sumRoom,ite_eq_left active]
    exact need e
  simp only [read,fun i=>(P.read j i).1]
  exact local_charge packet extra b m (fun _=>(j.val:Word w)) (fun e=>P.tabs (ports e)) h (fun _=>active.1)
    (fun _=>active.2.1) P.termRoom P.copyRoom P.sumRoom (fun _=>fields) opts bounded fits wide
    (fun e=>price (ports e)) quoted err γ tree nonneg accuracy catalogue resolution

end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
