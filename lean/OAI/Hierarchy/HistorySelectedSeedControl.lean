import OAI.ThreeFlat.Diagonal.TraceSeedEntryFrame
import OAI.ThreeFlat.RAM.HistoryNodeDirectoryRow

namespace OAI
/-! # The selected seed cursor decoded from the receiver's own physical metadata -/

namespace Hierarchy.HistorySelectedSeed
open ThreeFlat Diagonal.TickWorkspace Diagonal.NavigationPass
open RAM RAM.HistoryInitialSeed RAM.HistoryStageBody.Physical RAM.HistoryNodeDirectory
open RAM.HistoryNodeDirectory.Selected RAM.NavigationNodeRows Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {W u n : ℕ}

def archivedSite (a : Diagonal.NavigationPass.Archive) (rank : Fin a.initialSites)
    (extPins : ℕ) : Site :=
  ⟨a.cursor.node+rank.val,rank.val%a.remainingLanes,rank.val/a.remainingLanes,extPins⟩

omit [Field F] [Fintype F] in
/-- The S44 row stores the actual five-word kernel pointer and doubles the S43
pair count. Its two kernel operands recover the original lane and stage. -/
theorem receiverControl (a : Diagonal.NavigationPass.Archive) (b : Banks)
    (rank : Fin a.initialSites) (shape : TraceBucketAtom.Layout)
    {D : Directory W n} {tag : ((Fin 3→Bool)→F)→ℕ} {values : Fin n→NodeValue F}
    {input before : Memory W} (idx : Fin n) (pairs ext : ℕ)
    (live : Ledger u D tag values (TickTerminalRoot.slotKeep u) input idx.val before)
    (number : idx.val=a.cursor.node+rank.val)
    (mounted : RAM.HistoryStageSetup.DirectoryRow b a.seedLayer rank input)
    (nodes : b.nodes=base u 44) (charge : input (b.charges+2*idx.val+1)=(pairs:Word W))
    (external : ext=2*pairs)
    (kernel : ∀ c : Fin 5,input (a.initialRecords+5*rank.val+c.val)=
      ((![(a.seed),rank.val,0,rank.val%a.remainingLanes,rank.val/a.remainingLanes] : Fin 5→ℕ) c : Word W))
    (kernelHigh : base u 19≤a.initialRecords) (cursorFits : base u 18<2^W)
    (numberFits : idx.val+1<2^W) (nodeFits : base u 44+8*idx.val+7<2^W)
    (kernelFits : a.initialRecords+5*rank.val+4<2^W) (extFits : ext<2^W)
    (laneFits : rank.val%a.remainingLanes<2^W) (stageFits : rank.val/a.remainingLanes<2^W)
    (scratch : HistoryStageBody.Physical.seed u+42≤base u 18) :
    ControlImage (initial u shape) (archivedSite a rank ext) (a.initialRecords+5*rank.val)
      (bump (ownerData W u) before) := by
  let now := bump (ownerData W u) before
  have pos : 0< stride u := by unfold stride; positivity
  have high (x : ℕ) (hx : base u 19≤x) : now x=input x :=
    NativeNavigation.bumped_kept live cursorFits pos x (.inr hx)
  have rowLow : base u 19≤base u 44 := Nat.mul_le_mul_right _ (by decide : 20≤45)
  have klow : base u 19≤a.initialRecords+5*rank.val := kernelHigh.trans (Nat.le_add_right _ _)
  have row5 := mounted.kernel
  have row7 := mounted.external
  change input (b.nodes+8*(a.cursor.node+rank.val)+5)=
    ((a.initialRecords+rank.val*5:ℕ):Word W) at row5
  change input (b.nodes+8*(a.cursor.node+rank.val)+7)=2*input (b.charges+2*(a.cursor.node+rank.val)+1) at row7
  rw [nodes,←number,Nat.mul_comm rank.val] at row5
  rw [nodes,←number,charge,←Nat.cast_ofNat (R:=Word W) (n:=2),←Nat.cast_mul,←external] at row7
  have row5n : (now (base u 44+8*idx.val+5)).val=a.initialRecords+5*rank.val := by
    rw [high _ (by omega),row5,Fin.val_cast_of_lt (by omega)]
  have row7n : (now (base u 44+8*idx.val+7)).val=ext := by
    rw [high _ (by omega),row7,Fin.val_cast_of_lt extFits]
  have col3 := kernel 3
  have col4 := kernel 4
  change input (a.initialRecords+5*rank.val+3)=((rank.val%a.remainingLanes:ℕ):Word W) at col3
  change input (a.initialRecords+5*rank.val+4)=((rank.val/a.remainingLanes:ℕ):Word W) at col4
  have idxn : (archivedSite a rank ext).index=idx.val := number.symm
  have above : base u 18≤base u 19 := Nat.mul_le_mul_right _ (by decide : 19≤20)
  constructor
  · change (now (base u 18)).val=(archivedSite a rank ext).index+1
    rw [idxn]; exact NativeNavigation.bumped_index live cursorFits numberFits
  · change (now (base u 44+8*(archivedSite a rank ext).index+5)).val=a.initialRecords+5*rank.val
    rwa [idxn]
  · change (now (a.initialRecords+5*rank.val+3)).val=rank.val%a.remainingLanes
    rw [high _ (by omega),col3,Fin.val_cast_of_lt laneFits]
  · change (now (a.initialRecords+5*rank.val+4)).val=rank.val/a.remainingLanes
    rw [high _ (by omega),col4,Fin.val_cast_of_lt stageFits]
  · change (now (base u 44+8*(archivedSite a rank ext).index+7)).val=ext
    rwa [idxn]
  · exact Or.inr scratch
  · apply Or.inr
    change HistoryStageBody.Physical.seed u+42≤base u 44+8*(archivedSite a rank ext).index
    omega
  · exact Or.inr (scratch.trans (above.trans klow))
  · exact cursorFits
  · change base u 44+8*(archivedSite a rank ext).index+7<2^W
    rwa [idxn]
  · exact kernelFits

end Hierarchy.HistorySelectedSeed

end OAI
