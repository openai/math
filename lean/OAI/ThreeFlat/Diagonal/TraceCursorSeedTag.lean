import OAI.ThreeFlat.Diagonal.TraceCursorSlotControl
import OAI.ThreeFlat.RAM.HistoryStageBody

namespace OAI
/-! # The selected seed kind at the post-increment address -/
namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation
open Computability.VPVNP.BurstRAM PrivateRAM RAM PhysicalStage NodePublication NavigationNodeRows HistoryInitialSeed
open scoped Fin.CommRing Classical
variable {W d l : ℕ} {F : Type} [Field F] [Fintype F] {X : State d l}
    {start pay : X.Site→ℕ} {budget : ℕ}

private theorem first_kind (n : NodeArchive) (m : Memory W) (O : X.ArchiveSites) (data : LayerData O.layer)
    (parent : Parent) (owners : Fin O.layer.count→ℕ) (tail : List NodeRow)
    (space : RunBounds W n (records (⟨O.layer,parent,data,owners⟩::tail)) budget)
    (order : Chronological (records (⟨O.layer,parent,data,owners⟩::tail))) (v : X.Site) :
    let xs:=(⟨O.layer,parent,data,owners⟩:NodeRow)::tail
    let out:=state n (program xs) m (records xs).length
    out (n.banks.nodes+8*O.id v)=(O.layer.kind:Word W) := by
  let xs:=(⟨O.layer,parent,data,owners⟩:NodeRow)::tail
  let i : Fin (records xs).length:=⟨0,by simp [records,xs]⟩
  exact final_node_word n (program xs) m space order i (O.ord v) (0:Fin 8)

omit [Fintype F] in
theorem Selection.seed_kind {r : Run F X} {C : r.Charges} {O : X.ArchiveSites} {seed : LayerData O.layer}
    {n : NodeArchive} {a : RootArchive} {rows : List Layers} {m out : Memory W}
    (s : Selection r C O seed start pay n a rows budget m)
    (ran : out=state n (program (r.archiveList s.history C O s.path seed)) m rows.length)
    (v : X.Site) : out (n.banks.nodes+8*O.id v)=(O.layer.kind:Word W) := by
  have room:=s.source.room
  have ordered:=archive_chronological r s.history C O s.path seed
  have visits := congrArg List.length s.layout
  rw [ran, ←visits]
  cases r <;> exact first_kind n m O seed _ _ _ room ordered v

theorem CursorSeed.kind {T depth : ℕ} {A : HistoryInitialSeed.Layout} {z : HistoryInitialSeed.Site}
    {kernel : ℕ} {now : Memory W} (h : CursorSeed F W T depth A z kernel now) :
    (now (A.nodes+8*z.index)).val=0 := by
  cases h with
  | published s ran archive G base width seedMem metadata v j rank kernelBase A nodeBase stays keep cursor
      low nodeSafe ptrSafe cf nf kf jf ef kind positive bankLanes total perLane =>
    have same:=stays (0:Fin 8)
    have tag:=s.seed_kind ran v
    simp only [Fin.val_zero, Nat.add_zero] at same
    rw [←nodeBase,kind] at tag
    change (now (A.nodes+8*_)).val=0
    simpa using congrArg Fin.val (same.trans tag)

/-- The physical guard's address and its word bound follow from the very same
S18 cursor and S44 directory used for the S12 leaf compiler. -/
theorem CursorSeed.header {u T depth : ℕ} {B : TraceBucketAtom.Layout} {z : HistoryInitialSeed.Site}
    {kernel : ℕ} {now : Memory W}
    (h : CursorSeed F W T depth (HistoryStageBody.Physical.initial u B) z kernel now) :
    (now (HistoryStageBody.Physical.nodeAddress u now)).val=0 ∧
    HistoryStageBody.Physical.nodeAddress u now+5<2^W := by
  let A:=HistoryStageBody.Physical.initial u B
  have ctrl:=h.control
  have ptr : HistoryStageBody.Physical.nodeAddress u now=A.nodes+8*z.index := by
    change A.nodes+8*((now A.cursor).val-1)=_
    rw [ctrl.cursor]; simp
  rw [ptr]
  have nodeFits : A.nodes+8*z.index+7 < 2^W := ctrl.nodeFits
  exact ⟨h.kind, (Nat.add_le_add_left (by decide : 5 ≤ 7) (A.nodes+8*z.index)).trans_lt nodeFits⟩

end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

end OAI
