import OAI.ThreeFlat.Diagonal.TraceCursorSeedTag
import OAI.ThreeFlat.Diagonal.TraceSelectedArenas
import OAI.ThreeFlat.RAM.HistorySelectedFamily
import OAI.ThreeFlat.RAM.TickLedgerTerminal

namespace OAI
/-! # The physical seed cursor and its grouped endpoint headers after the native bump -/
namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation
open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression PrivateRAM RAM PhysicalStage NodePublication NavigationNodeRows
open HistoryInitialSeed HistoryStageBody.Physical HistoryNodeDirectory HistoryNodeDirectory.Selected TickWorkspace
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] [Fintype F] {u W n d l budget : ℕ} {X : State d l}
variable {D : Directory W n} {tag : ((Fin 3→Bool)→F)→ℕ} {values : Fin n→NodeValue F}
    {input before : Memory W} {i : Fin n}
    (live : Ledger u D tag values (TickTerminalRoot.slotKeep u) input i.val before)
local notation "now" => bump (ownerData W u) before

include live in
omit [Field F] [Fintype F] in
theorem bumped_kept (ctrl : base u 18<2^W) (pos : 0<stride u) (a : ℕ)
    (whereAt : TickTerminalRoot.slotKeep u a) : now a=input a := by
  have other : a≠base u 18 := by
    change a<13*stride u ∨ 20*stride u≤a at whereAt
    change a≠19*stride u
    omega
  exact (bumped_outside u before ctrl other).trans (live.durable a whereAt)

include live in
omit [Field F] [Fintype F] in
theorem bumped_index (ctrl : base u 18<2^W) (step : i.val+1<2^W) :
    (now (base u 18)).val=i.val+1 := by
  let data:=ownerData W u
  have adr : (data 0).val=base u 18:=Fin.val_cast_of_lt ctrl
  have pre : before (data 0).val=(i.val:Word W) :=
    Fin.ext (live.cursor.trans (Fin.val_cast_of_lt (by omega)).symm)
  have written : bump data before (data 0).val = before (data 0).val + 1 := by
    exact ite_eq_left (rfl : (data 0).val = (data 0).val)
  have successor : (i.val : Word W) + 1 = ((i.val + 1 : ℕ) : Word W) :=
    (Nat.cast_succ i.val).symm
  calc
    (now (base u 18)).val = (bump data before (data 0).val).val :=
      congrArg (fun addr => (bump data before addr).val) adr.symm
    _ = ((i.val + 1 : ℕ) : Word W).val :=
      congrArg Fin.val (written.trans ((congrArg (fun value : Word W => value + 1) pre).trans successor))
    _ = i.val + 1 := Fin.val_cast_of_lt step

include live in
/-- Construct the seed control image from actual chronological S44 and S49 sources,
the selected ledger and the high-window preservation of its starting image. -/
theorem Selection.bumped_seed_control {start pay : X.Site→ℕ} {r : Run F X} {C : r.Charges}
    {O : X.ArchiveSites} {seedData : LayerData O.layer} {narch : NodeArchive} {a : RootArchive}
    {layers : List Layers} {m out : Memory W}
    (s : Selection r C O seedData start pay narch a layers budget m)
    (ran : out=state narch (program (r.archiveList s.history C O s.path seedData)) m layers.length)
    (archive : NavigationPass.Archive) {V : Type} {k : ℕ}
    (G : LiftedSlots V archive.initialDegree (BitWord k)) (index : V≃Fin archive.axes)
    (width : SlotImage.Edge V (BitWord k) archive.initialDegree→ℕ)
    (seedMem : Memory W) («meta» : archive.InitialNodeMetadata G index width seedMem)
    (B : TraceBucketAtom.Layout) (v : X.Site) (j : Fin archive.initialSites)
    (rank : (O.ord v).val=j.val) (idAt : O.id v=i.val)
    (kernelBase : O.layer.kernels=archive.initialRecords) (nodeBase : base u 44=narch.banks.nodes)
    (S44 : ∀ c : Fin 8,input (base u 44+8*i.val+c.val)=out (base u 44+8*i.val+c.val))
    (S49 : ∀ c : Fin 5,input (archive.initialRecords+5*j.val+c.val)=seedMem (archive.initialRecords+5*j.val+c.val))
    (high : base u 19≤archive.initialRecords)
    (room : volume u + 42 ≤ stride u) (ctrl : base u 18<2^W) (step : i.val+1<2^W)
    (nodeFit : base u 44+8*i.val+7<2^W) (kerFit : archive.initialRecords+5*j.val+4<2^W)
    (extFit : 2*pay v<2^W) (kind : O.layer.kind=0) (positive : 0<archive.remainingLanes)
    (bankLanes : narch.banks.lanes=archive.remainingLanes) {T depth : ℕ}
    (total : narch.banks.totalPairs=T) (perLane : narch.banks.perLanePairs=2^depth) :
    CursorSeed F W T depth (initial u B)
      ⟨O.id v,j.val%archive.remainingLanes,j.val/archive.remainingLanes,2*pay v⟩
      (archive.initialRecords+5*j.val) now := by
  have pos : 0 < stride u := lt_of_lt_of_le (by omega : 0 < volume u + 42) room
  have safe : (initial u B).ctrl+42≤base u 18 := by
    change 15*stride u+volume u+42≤19*stride u
    omega
  have safe49 : base u 18≤archive.initialRecords := by
    change 20*stride u≤archive.initialRecords at high
    change 19*stride u≤archive.initialRecords
    omega
  apply CursorSeed.published s ran archive G index width seedMem «meta» v j rank kernelBase (initial u B) nodeBase
  · intro c
    change now (base u 44+8*O.id v+c.val)=out (base u 44+8*O.id v+c.val)
    rw [idAt,bumped_kept live ctrl pos]
    · exact S44 c
    · right; change 20*stride u≤45*stride u+8*i.val+c.val;omega
  · intro c
    rw [bumped_kept live ctrl pos]
    · exact S49 c
    · right;omega
  · change (now (base u 18)).val = O.id v + 1
    rw [idAt]
    exact bumped_index live ctrl step
  · exact Or.inr safe
  · right; change (initial u B).ctrl+42≤45*stride u+_;change _≤19*stride u at safe;omega
  · right;omega
  · exact ctrl
  · change base u 44 + 8 * O.id v + 7 < 2^W
    rw [idAt]
    exact nodeFit
  · exact kerFit
  · omega
  · exact extFit
  · exact kind
  · exact positive
  · exact bankLanes
  · exact total
  · exact perLane


end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

end OAI
