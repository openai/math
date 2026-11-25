import OAI.Hierarchy.HistorySelectedSeedBounds
import OAI.Hierarchy.HistorySelectedSeedControl
import OAI.Hierarchy.TraceReceiverSeedSlot

namespace OAI
/-! # Constructing the seed arm from its charged numerical archive and recovered original pins -/

namespace Hierarchy.HistorySelectedSeed
open ThreeFlat Diagonal.TickWorkspace Diagonal.HistoryContraction Diagonal.PhysicalStage
open Diagonal.NavigationPass RAM RAM.HistoryInitialSeed RAM.HistoryStageBody.Physical
open RAM.HistoryNodeDirectory RAM.HistoryNodeDirectory.Selected RAM.NavigationNodeRows RAM.HistoryPartyBatchExec
open RAM.HistoryStageSetup
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F Pins E : Type} [Field F] [Fintype F] {W u n count : ℕ}
    (a : Diagonal.NavigationPass.Archive) (rank : Fin a.initialSites)
    (g : Run.SelectedNode F Pins E) (ext : ℕ) (shape : TraceBucketAtom.Layout)
    (rom : TraceRawLookup.Layout) (rest : Fin 1→Word W)
    (tag : ((Fin 3→Bool)→F)→ℕ) (pointer : E→ℕ) (j : Fin n)
    (D : Directory W n) (values : Fin n→NodeValue F)
    (warm prev issued : Memory W) (b : Banks)
local notation "z" => archivedSite a rank ext
local notation "A" => initial u shape
local notation "now" => bump (ownerData W u) prev
local notation "storedSlot" => (now ((A).intervals+4*(z).lane+3)).val
local notation "decoder" => TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W)
local notation "table" => TraceBucketAtom.publicData shape rest

/-- Only physical input words appear among the tape premises. The cursor, paid
work, six output word bounds, contiguous endpoint pointers and output geometry
are determined inside the construction. -/
def buildOriginal
    (live : Ledger u D tag values (TickTerminalRoot.slotKeep u) warm j.val prev)
    (number : j.val=a.cursor.node+rank.val) (early : j.val<count)
    (mounted : DirectoryRow b a.seedLayer rank warm) (nodes : b.nodes=base u 44)
    (pairs work : ℕ) (unit : 0<b.unitWork)
    (charge : warm (b.charges+2*j.val+1)=(pairs:Word W)) (external : ext=2*pairs)
    (bill : archiveColumn b (numeric issued) j.val 0=b.unitWork*work)
    (alive : 1≤work) (funded : g.tree.resources≤work) (ports : g.arity≤2*work)
    (smallWork : 4*work≤volume u)
    (kernel : ∀ c : Fin 5,warm (a.initialRecords+5*rank.val+c.val)=
      ((![(a.seed),rank.val,0,rank.val%a.remainingLanes,rank.val/a.remainingLanes] : Fin 5→ℕ) c : Word W))
    (guard : warm (b.nodes+8*j.val)=0)
    (kernelHigh : base u 19≤a.initialRecords) (word : base u 19<2^W)
    (nodeFit : base u 44+8*j.val+7<2^W) (kernelFit : a.initialRecords+5*rank.val+4<2^W)
    (laneFit : (z).lane<2^W) (stageFit : (z).stage<2^W)
    (v : 2≤volume u) (scratch : volume u+42≤ Diagonal.TickWorkspace.stride u)
    (stream : base u 12+(j.val+1)*(volume u)^2≤base u 13)
    (result : base u 13+8*j.val+8≤base u 14) (bins : 4*(z).lane+4≤ Diagonal.TickWorkspace.stride u)
    (value : values j=NodeValue.ofSite g pointer (streamAt u count j.val) (endsAt u count j.val))
    (realExt : g.external=ext) (wiring : ∀ i,pointer (g.origin i)=2+storedSlot+i.val)
    (arity : g.arity=ext+2*shape.bank) (rows : g.net.cells=(z).rows A)
    (hidden : g.net.internal=(z).bits A)
    (raw : RawReads A z decoder table now (recordAt tag g.net ((z).stream A))) :
    Operands shape rom rest tag now values j b (numeric issued) u count := by
  have index : (z).index=j.val := number.symm
  have cur : base u 18<2^W := (Nat.mul_le_mul_right _ (by decide : 19≤20)).trans_lt word
  have startFit : j.val+1<2^W := by omega
  have covers : volume u<2^W := by
    have h:=Diagonal.TickWorkspace.lower u 19
    omega
  have extFit : ext<2^W := by omega
  have ctrlScratch : HistoryStageBody.Physical.seed u+42≤base u 18 := by
    have :=apart (u:=u) (by decide : 14<18)
    change base u 14+volume u+42≤_
    omega
  have entry := receiverControl a b rank shape j pairs ext live number mounted nodes
    charge external kernel kernelHigh cur startFit nodeFit kernelFit extFit laneFit stageFit ctrlScratch
  have rowsLe : g.net.cells≤work := by
    change g.tree.compile.cells≤work
    rw [Tree.compiled_rows]
    exact (show g.tree.rows≤g.tree.resources by unfold Tree.resources Stage.treeWork;omega).trans funded
  have bitsLe : g.net.internal≤work := by
    change g.tree.compile.internal≤work
    rw [Tree.compiled_bits]
    exact (show g.tree.bits≤g.tree.resources by unfold Tree.resources Stage.treeWork;omega).trans funded
  have cost := paid g.tree z shape b (numeric issued) work unit (by simpa only [index] using bill) alive funded ports arity rows
  have inc : 4*(z).rows A≤volume u := by omega
  have extLe : (z).extPins≤volume u := by change ext≤_;omega
  obtain ⟨apartBanks,spanFits,four,fields,locator,untouched⟩ := physicalBounds (W:=W) shape z v scratch word inc
    extLe (by change ext+2*shape.bank<_;omega) (by omega) (by simpa only [index] using stream) (by simpa only [index] using result) bins
  have flag : (now (base u 44+8*(z).index)).val=0 := by
    rw [index, NativeNavigation.bumped_kept live cur (by unfold Diagonal.TickWorkspace.stride; positivity) _
      (.inr (show base u 19≤base u 44+8*j.val from (Nat.mul_le_mul_right _ (by decide : 20≤45)).trans (Nat.le_add_right _ _))),
      ←nodes,guard]
    rfl
  refine {
    site := z
    ar := g.arity
    net := g.net
    slot := storedSlot
    kernel := a.initialRecords + 5 * rank.val
    index := index
    value := ?_
    active := ?_
    rowMass := ?_
    pinMass := ?_
    zero := flag
    control := entry
    separate := apartBanks
    room := spanFits
    four := four
    early := by simpa only [index] using early
    arity := arity
    cells := rows
    hidden := hidden
    headerFit := fields
    fit := locator
    safe := untouched
    offset := ?_
    size := inc
    ext := extLe
    volume := v
    scratch := scratch
    raw := raw }
  · rw [value,node_eq g pointer storedSlot _ _ wiring,realExt,index]
    rfl
  · simpa only [index] using cost.1
  · simpa only [index] using cost.2.1
  · simpa only [index] using cost.2.2
  · simp only [Fin.cast_val_eq_self]

end
end Hierarchy.HistorySelectedSeed

end OAI
