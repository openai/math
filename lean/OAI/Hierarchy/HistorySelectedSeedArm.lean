import OAI.Hierarchy.HistorySelectedReached
import OAI.Hierarchy.HistorySelectedPublisher
import OAI.Hierarchy.HistorySelectedSeedPrice
import OAI.ThreeFlat.Diagonal.HistoryCursorVisits

namespace OAI
/-! # A funded, originally issued seed arm at a reached receiver cursor -/

namespace Hierarchy.HistorySelectedSeed
open ThreeFlat RAM RAM.DescriptorExpr RAM.HistoryInitialSeed
open RAM.PhysicalProcedure RAM.HistoryStageBody.Physical RAM.HistoryNodeDirectory
open Diagonal.TickWorkspace Diagonal.PhysicalStage Computability.VPVNP.BurstRAM PrivateRAM
open HistorySelectedReceiverLoop RAM.NavigationNodeRows
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {W count n u p kernel : ℕ}

/-- No endpoint output or gate stream is part of the entry conditions. The
source has the mounted node's true kernel pair, its immutable mask/prototype
metadata and the one numerical interval word for its original input lane. -/
theorem emitReceiver (B : Block F) (bank : Archive) (shape : TraceBucketAtom.Layout)
    (rom : TraceRawLookup.Layout) (z : Site) (rest : Fin 1→Word W)
    (tag : ((Fin 3→Bool)→F)→ℕ) (N : BitNetwork F p) (src : Memory W) (slot : ℕ)
    (D : HistoryNodeDirectory.Selected.Directory W n) (values : Fin n→NodeValue F) (j : Fin n) (jEq : z.index=j.val)
    (valuation : values j=node N z.extPins slot (streamAt u count z.index) (endsAt u count z.index))
    (b : Banks) (paidMem : ℕ→ℕ) (start pages height coeff : ℕ) (unit : 1≤coeff)
    (live : 1≤archiveColumn b paidMem j.val 0/b.unitWork)
    (rowMass : z.rows (initial u shape)≤archiveColumn b paidMem j.val 0/b.unitWork)
    (pinMass : z.extPins≤2*(archiveColumn b paidMem j.val 0/b.unitWork))
    (kindZero : (src (base u 44+8*z.index)).val=0)
    (control : ControlImage (initial u shape) z kernel src)
    (separate : Separated (initial u shape) z)
    (room : (initial u shape).ctrl+42<2^W)
    (four : 4<2^W) (early : z.index<count)
    (arity : p=z.extPins+2*shape.bank) (cells : N.cells=z.rows (initial u shape))
    (hidden : N.internal=z.bits (initial u shape))
    (headerFit : ∀ j : Fin 6,z.words (initial u shape) ⟨36+j.val,by omega⟩<2^W)
    (fit : (initial u shape).intervals+4*z.lane+3<2^W)
    (safe : ¬z.writes (initial u shape) ((initial u shape).intervals+4*z.lane+3))
    (offset : src ((initial u shape).intervals+4*z.lane+3)=(slot:Word W))
    (size : 4*z.rows (initial u shape)≤volume u) (ext : z.extPins≤volume u)
    (v : 2≤volume u) (scratch : volume u+42≤ stride u)
    (raw : RawReads (initial u shape) z (TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W)) (TraceBucketAtom.publicData shape rest) src
      (recordAt tag N (z.stream (initial u shape)))) :
    let arm := fun i : Fin n => B.nativeArmTime height coeff b paidMem i.val
    let decoder := TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W)
    Emitted (u:=u) bank (procedure (initial u shape) decoder (TraceBucketAtom.publicData shape rest))
      (families B start pages) D values tag (B.nativeVisitCost height coeff b paidMem)
      arm (fun i _=>arm i) j src := by
  let A := initial u shape
  let dec := TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W)
  let table := TraceBucketAtom.publicData shape rest
  obtain ⟨out,run,cached,frame⟩ := publish shape z dec table tag N src slot control separate room four
    early arity cells hidden headerFit fit safe offset size ext v scratch raw
  have align : nodeAddress u src=base u 44+8*z.index := by
    unfold nodeAddress
    have c : (src (base u 18)).val=z.index+1 := control.cursor
    rw [c,Nat.add_sub_cancel]
  have zero : (src (nodeAddress u src)).val=0 := by rw [align]; exact kindZero
  have bound : nodeAddress u src+5<2^W := by
    rw [align]; have := control.nodeFits
    change base u 44+8*z.index+7<2^W at this
    omega
  have price := nativeArm_dispatch (u:=u) (height:=height) (K:=coeff) (idx:=j.val) B b paidMem start pages src live unit
  rw [bodyCost_seed_at u src zero] at price
  have cost := block_ticks (W:=W) B A z rom _ live rowMass pinMass
  refine Emitted.ofSeed (D:=D) (j:=j) (out:=out) zero bound price ?_ ?_ ?_
  · exact nativeArm_seed (height:=height) (K:=coeff) (idx:=j.val) B b paidMem
      (procedure A dec table) src out (ticks A z dec) unit cost run
  · simpa only [valuation, ←jEq] using cached
  · simpa only [←jEq] using frame

end
end Hierarchy.HistorySelectedSeed

end OAI
