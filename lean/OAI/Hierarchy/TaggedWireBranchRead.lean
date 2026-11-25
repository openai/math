import OAI.Hierarchy.TaggedWireCausalTape
import OAI.Hierarchy.ProbeNativePacketBuild
import OAI.Hierarchy.ProbeSelectedPacketWidths

namespace OAI
/-! # Matching the signed branch to the native committed histogram on this row -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM ProtocolRAM.Calendar ProtocolRAM.PurchaseStage Tagged
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped BigOperators Classical Fin.CommRing

variable {X : Type} {W q d : ℕ} {C : Chart W q d}

theorem HistogramFormat.field_on_branch (D : HistogramFormat C X) (a : Attempt) (x : X) (m : Memory W)
    (choice : BallChoices (D.letters a x) (D.copies a x)) (i : Fin (C.layout a).candidates) (j : Fin q)
    (ready : Calendar.ready C (.attempt a) m)
    (preserved : ∀l : Fin ((C.layout a).candidates*q),protected C ((D.bank a).base+l.val) (.attempt a))
    (typed : (D.slot (.attempt a)).word x choice=D.windows.read (.attempt a) m) :
    ((C.raw a).batch.field j).eval (HistogramShelf.snapshot C a m) (i.val:Word W)=
      counterRows (D.letters a x) (D.copies a x) choice (D.count a x) i j := by
  let pos:=finProdFinEquiv (i,j)
  have get : (arrayBits ((C.layout a).candidates*q) W).symm (D.windows.read (.attempt a) m)=fun l=>m ((D.bank a).base+l.val) :=
    (arrayBits _ _).symm_apply_apply _
  rw [D.fields,HistogramShelf.read_field _ _ i j (D.fits a) (D.room a)]
  change HistogramShelf.snapshot C a m ((D.bank a).base+pos.val)=_
  rw [HistogramShelf.snapshot_frame C a m _ ready (preserved pos)]
  rw [←congrFun get pos,←typed]
  exact HistogramShelf.encoded_words (D.letters a x) (D.copies a x)
    (D.width a x) (D.count a x) choice i j

theorem cast_counter {h r n t : ℕ} (letters : h=n) (copies : r=t) (c : Histogram (Fin h) r) (j : Fin n) :
    ((cast (congrArg₂ (fun a b=>Histogram (Fin a) b) letters copies) c).val j).val=
      (c.val (j.cast letters.symm)).val := by
  subst n t
  rfl

/-- Both quantities come from the very same native field bytes. Leading digits
recover the branch exactly, even if another histogram gives identical widths. -/
theorem hist_eq {h r n t extra : ℕ} (letters : h=n) (copies : r=t) (c : Histogram (Fin h) r)
    (native : Histogram (Fin n) t) (words : Fin (n+extra)→Word W)
    (read : ∀j,(words j).val=((padHistogram native extra).val j).val)
    (branch : ∀j:Fin n,(words (j.castAdd extra)).val=(c.val (j.cast letters.symm)).val) :
    native=cast (congrArg₂ (fun a b=>Histogram (Fin a) b) letters copies) c := by
  apply Subtype.ext
  funext j
  apply Fin.ext
  rw [cast_counter letters copies]
  apply Eq.trans _ (branch j)
  simpa only [padHistogram,Fin.addCases_left] using (read (j.castAdd extra)).symm

open ProtocolRAM.Calendar.StockCommit ProtocolRAM.RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph

variable {F E A : Type} [Field F] [Fintype E] [Fintype A] {k extra : ℕ} [Nonempty (Fin k)]
    {edge : E→Chord k} {req : A→E} {P : Probe.Packet F edge req}
    {chart : Chart W (P.terms+extra) d} (D : HistogramFormat chart X)
    (a : Attempt) (x : X) (m : Memory W) (i : Fin (chart.layout a).candidates)
local notation "b" => enabledBatch (chart.layout a) (ProtocolRAM.Calendar.repair chart a)
local notation "snap" => HistogramShelf.snapshot chart a m

omit [Nonempty (Fin k)] in
theorem HistogramFormat.chosen_histogram {st : StockCommit} {layout : PortPlan st b snap (chart.layout a).candidates}
    (R : NativePacketRow P extra b layout i)
    (choice : BallChoices (D.letters a x) (D.copies a x)) (physical : D.observed a x m)
    (arity : ((b).termCount.read snap ((b).packet.eval snap (i.val:Word W))).val=P.terms)
    (ok : ready chart (.attempt a) m)
    (safe : ∀l : Fin ((chart.layout a).candidates*(P.terms+extra)),
      protected chart ((D.bank a).base+l.val) (.attempt a))
    (tape : (D.slot (.attempt a)).word x choice=D.windows.read (.attempt a) m) :
    ∃(letters : D.letters a x i=P.terms)(copies : D.copies a x i=(b).copies),
      R.h=cast (congrArg₂ (fun j n=>Histogram (Fin j) n) letters copies) (choice i) := by
  have letters : D.letters a x i=P.terms := (physical.1 i).trans arity
  have chosen : (b).selected snap (i.val:Word W) := (Finset.mem_filter.mp R.live).2.1
  have copies : D.copies a x i=(b).copies := (physical.2 i).trans (ite_eq_left chosen)
  refine ⟨letters,copies,hist_eq letters copies (choice i) R.h (fun j=>((b).field j).eval snap (i.val:Word W)) R.fields ?_⟩
  intro j
  have read:=D.field_on_branch a x m choice i (j.castAdd extra) ok safe tape
  have low:=counter_of_active (D.letters a x) (D.copies a x) choice (D.width a x) (D.count a x) i (j.cast letters.symm)
  exact (congrArg Fin.val read).trans low

end Hierarchy.WireTelescope.CalendarTape

end
end OAI
