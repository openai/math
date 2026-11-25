import OAI.Hierarchy.ProtocolRAMLocalCharge
import OAI.Hierarchy.ProtocolRAMStockPortPlan

namespace OAI
/-! # Installed and consumed bits at an admitted packet port -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram AdaptiveProbe
open ThreeFlat.Diagonal.MotifOuterTerms
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {F E A : Type*} [Field F] [Fintype E] [Fintype A] {k : ℕ} [Nonempty (Fin k)]
variable {edge : E→Chord k} {req : A→E} {w d rows : ℕ} {s : StockCommit} {mem : Memory w}

/-- Physical readback fields of one particular admitted packet at its shared padded
native arity. Names of requests may coincide; all occurrences are retained in `need`. -/
structure NativePacketRow (P : Probe.Packet F edge req) (extra : ℕ) (b : Batch (P.terms+extra) d)
    (layout : PortPlan s b mem rows) (j : Fin rows) where
  live : j∈liveRows b mem rows
  h : Histogram (Fin P.terms) b.copies
  ports : E ↪ Fin d
  fields : ∀ t,((b.field t).eval mem (j.val:Word w)).val=((padHistogram h extra).val t).val
  entries : ∀ e t,(layout.tabs (ports e) t).eval mem (j.val:Word w)=(padCounts P.count extra t e:Word w)
  need : ∀ e,((b.need (ports e)).eval mem (j.val:Word w)).val=debited req (b.copies*P.width) e
  unused : ∀ v,(∀e,ports e≠v) → installedBits s.columns mem (layout.enum ⟨j,v⟩)=0 ∧
    consumedBits s.columns mem (layout.enum ⟨j,v⟩)=0
  bound : ∀ t e,P.count t e≤b.maxWidth
  fit : b.maxWidth<2^w
  wide : b.copies*b.maxWidth<2^w

namespace NativePacketRow
variable {P : Probe.Packet F edge req} {extra : ℕ} {b : Batch (P.terms+extra) d}
  {layout : PortPlan s b mem rows} {j : Fin rows}

omit [Nonempty (Fin k)] in
theorem amounts (R : NativePacketRow P extra b layout j) (e : E) :
    installedBits s.columns mem (layout.enum ⟨j,R.ports e⟩)=histWidth P.count R.h e ∧
    consumedBits s.columns mem (layout.enum ⟨j,R.ports e⟩)=debited req (b.copies*P.width) e := by
  have active := (Finset.mem_filter.mp R.live).2
  have term := packet_wire P extra b mem (j.val:Word w) e (layout.tabs (R.ports e)) R.h
    active.1 active.2.1 layout.termRoom layout.copyRoom layout.sumRoom R.fields (R.entries e) (fun t=>R.bound t e) R.fit
  have fits := (histWidth_le P.count R.h e b.maxWidth (fun t=>R.bound t e)).trans_lt R.wide
  refine ⟨(layout.read j (R.ports e)).1.trans ((congrArg Fin.val term).trans (Fin.val_cast_of_lt fits)),?_⟩
  rw [(layout.read j (R.ports e)).2,debit_eval b _ mem _ layout.termRoom layout.copyRoom layout.sumRoom,ite_eq_left active]
  exact R.need e

end NativePacketRow

end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
