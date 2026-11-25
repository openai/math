import OAI.Hierarchy.TaggedWireBranchRead
import OAI.Hierarchy.ProtocolRAMCalendarPricedFields

namespace OAI
/-! # Reading an elected strip histogram across the pricing preamble -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM ProtocolRAM.Calendar ProtocolRAM.PurchaseStage Tagged
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped BigOperators Classical Fin.CommRing

variable {X : Type} {W q d : ℕ} {C : Chart W q d}

open ProtocolRAM.Calendar.StockCommit ProtocolRAM.RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph

variable {F E A : Type} [Field F] [Fintype E] [Fintype A] {k extra : ℕ} [Nonempty (Fin k)]
    {edge : E→Chord k} {req : A→E} {P : Probe.Packet F edge req}
    {chart : Chart W (P.terms+extra) d} (D : HistogramFormat chart X)
    (a : Attempt) (x : X) (m : Memory W) (i : Fin (chart.layout a).candidates)
local notation "b" => enabledBatch (chart.layout a) (ProtocolRAM.Calendar.repair chart a)
local notation "snap" => HistogramShelf.snapshot chart a m

omit [Nonempty (Fin k)] in
theorem HistogramFormat.chosen_histogram_at (actual : Memory W) {st : StockCommit} {layout : PortPlan st b actual (chart.layout a).candidates}
    (R : NativePacketRow P extra b layout i)
    (chosen : (b).selected snap (i.val:Word W))
    (same : ∀j,((b).field j).eval actual (i.val:Word W)=((b).field j).eval snap (i.val:Word W))
    (choice : BallChoices (D.letters a x) (D.copies a x)) (physical : D.observed a x m)
    (arity : ((b).termCount.read snap ((b).packet.eval snap (i.val:Word W))).val=P.terms)
    (ok : ready chart (.attempt a) m)
    (safe : ∀l : Fin ((chart.layout a).candidates*(P.terms+extra)),
      protected chart ((D.bank a).base+l.val) (.attempt a))
    (tape : (D.slot (.attempt a)).word x choice=D.windows.read (.attempt a) m) :
    ∃(letters : D.letters a x i=P.terms)(copies : D.copies a x i=(b).copies),
      R.h=cast (congrArg₂ (fun j n=>Histogram (Fin j) n) letters copies) (choice i) := by
  have letters : D.letters a x i=P.terms := (physical.1 i).trans arity
  have copies : D.copies a x i=(b).copies := (physical.2 i).trans (ite_eq_left chosen)
  refine ⟨letters,copies,hist_eq letters copies (choice i) R.h (fun j=>((b).field j).eval actual (i.val:Word W)) R.fields ?_⟩
  intro j
  have read:=D.field_on_branch a x m choice i (j.castAdd extra) ok safe tape
  have low:=counter_of_active (D.letters a x) (D.copies a x) choice (D.width a x) (D.count a x) i (j.cast letters.symm)
  exact (congrArg Fin.val ((same _).trans read)).trans low

end Hierarchy.WireTelescope.CalendarTape

end
end OAI
