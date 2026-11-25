import OAI.Computability.BorderVNP.CubeRouteDirectoryPass
import OAI.Computability.BorderVNP.CubeRouteDemandEntry

/-! # The checked group prefix and the genuine native transmission-data entry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open BorderVNP.Cube CubeHeaderInstall LocalRow CubeArena VPVNP.BurstRAM Transmission Packing.Directory

variable {w R X ticks width : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {s : Bank w} {m : Memory w} {ok : Prop}

/-- All five remaining operands for the cell and pair writers, measured at the raw directory publication. -/
structure DirectoryPointers (a : CubeArena.Layout) (frame controls : ℕ) (m : ℕ → ℕ) : Prop where
  host : m (frame+72)=a.hostDirectory
  pair : m (frame+91)=a.pairDirectory
  controlsAt : m (frame+92)=controls
  bank : m (controls+9)=a.cellBank
  stride : m (controls+10)=a.cellStride

/-- The two actual fixed public operands are read from the joint boot extension. The control
pointer and its two target words are supplied by the published geometry output. -/
theorem DirectoryPointers.of_boot (a : CubeArena.Layout) (old : Fin 81 → Word w)
    (fresh profile gates outputs bits off ell controls : ℕ) {f : BroadcastFrame} {raw : List Bool}
    (h : BootPins pub f (jointFields (a.extension old) fresh profile gates outputs bits off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) raw m)
    (control : readings m ((pub 0).val+92)=controls ∧ readings m (controls+9)=a.cellBank ∧
      readings m (controls+10)=a.cellStride) (room : a.stop < 2^w) :
    DirectoryPointers a (pub 0).val controls (readings m) := by
  obtain ⟨_,_,_,_,pair,host,rec,stop⟩ := a.writer_order
  exact ⟨h.arenaOperand a old fresh profile gates outputs bits off ell rfl (by omega),
    h.arenaOperand a old fresh profile gates outputs bits off ell rfl (by omega),control.1,control.2.1,control.2.2⟩

/-- The two native directory runs preserve the reached schedule and its exact relation
to the original raw rows, including the physical receiving teams and absolute cell addresses. -/
structure NativeEntry (a : CubeArena.Layout) (frame controls : ℕ) (axis : Fin (a.n+1)) (R : ℕ)
    (input original after : ℕ → ℕ) : Prop where
  /-- Actual owner and label-pair images of an intermediate team schedule. -/
  image : ∃ scheduled, GroupWeights.ScheduleResult (weightLayout a frame axis.val) (teamLayout a R) input scheduled ∧
    DirectoryImage a frame controls axis R input scheduled after
  /-- Every protected raw demand and public scalar word comes from the original memory. -/
  low : ∀ j < a.header.header, after j=original j

/-- Both intermediate word memories of the physical directory installers, retaining
the verified property of the checked schedule's returned memory. -/
def DirectorySources (a : CubeArena.Layout) (frame controls : ℕ) (axis : Fin (a.n+1))
    (P : (ℕ → ℕ) → Prop) (w : ℕ) (after : ℕ → ℕ) : Prop :=
  let banks := a.cellWriter frame controls axis
  let pairs := a.pairWriter frame
  ∃ scheduled cells : Memory w, P (readings scheduled) ∧
    readings cells=banks.written (readings scheduled) banks.cells ∧
    PairDirectory.Image pairs (readings cells) pairs.count after

/-- Compose the actual seven-stage checked grouping program with the two directory programs.
The nine-stage code is exactly the prefix executed by the signed evaluator. -/
theorem beforeWriters_test (a : CubeArena.Layout) (controls : ℕ) (axis : Fin (a.n+1)) (input : ℕ → ℕ) (P : (ℕ → ℕ) → Prop)
    (checked : GroupWeights.CheckedFrame (weightLayout a (pub 0).val axis.val) (teamLayout a R) input w X)
    (first : TestRun pub mac (groupPrefix a.n width) s m ticks ok (fun z =>
      GroupWeights.ScheduleResult (weightLayout a (pub 0).val axis.val) (teamLayout a R) input z.mem ∧
      P z.mem ∧ ∀ x < a.header.header, z.mem x=readings m x))
    (pointers : DirectoryPointers a (pub 0).val controls (readings m))
    (two : 2 ≤ a.header.d) (bank : 0 < Cube.Tally.bankWidth a.n a.b a.h a.K a.s)
    (low : (pub 0).val+112 ≤ a.header.header) (ctl : controls+10 < a.header.header) (room : a.stop < 2^w) :
    TestRun pub mac (.block (beforeWriters a.n width)) s m
      (ticks+((CellBanks.setup.slots+a.cells*15+1)+(30+(a.pairWriter (pub 0).val).count*(24+27*(a.n+1)))))
      ok (fun z => NativeEntry a (pub 0).val controls axis R input (readings m) z.mem ∧
        DirectorySources a (pub 0).val controls axis P w z.mem) := by
  let codes := [LabelIndex.directoryProgram,NativeIntervals.prepare,CubePowers.install,CubeHeaderInstall.install a.n width,
    HeaderDecode.program,CubeLengths.minimum,GroupWeights.checkedSchedule]
  let tail := [CellBanks.install,PairDirectory.directory]
  let post := fun z : NatState => NativeEntry a (pub 0).val controls axis R input (readings m) z.mem
    ∧ DirectorySources a (pub 0).val controls axis P w z.mem
  have combined := first.seq (b:=Code.block tail) (ob:=True) (Q:=post) (fun t mt hs => by
    obtain ⟨schedule,property,keep⟩ := hs
    have fs := a.writer_fields (pub 0).val controls axis checked schedule low
      ((keep _ (by omega)).trans pointers.host) ((keep _ (by omega)).trans pointers.pair)
      ((keep _ (by omega)).trans pointers.controlsAt) ((keep _ (by omega)).trans pointers.bank)
      ((keep _ ctl).trans pointers.stride)
    have written := a.directoryPass_run (pub 0).val controls axis R pub mac t mt input schedule rfl fs.1 fs.2 two bank low ctl room
    obtain ⟨es,u,mu,run,cost,img⟩ := written
    obtain ⟨c,mc,_,_,_,rc,rp⟩ := Runs.seq_iff.mp run
    have cell := ((CellBanks.install_run pub mac (a.cellWriter (pub 0).val controls axis) t mt rfl fs.1
      (a.cellWriter_fits (pub 0).val controls axis (by omega) low ctl room)).asTest (by decide)).sound rc
    have im := img.pairRows
    have cm := cell.2
    change readings mc = _ at cm
    rw [← cm] at im
    have bounded : BoundedRun pub mac (.block tail) t mt _ post :=
      ⟨es,u,mu,run,cost,⟨⟨readings mt,schedule,img⟩,fun j hj => (img.beforeHeader j hj).trans (keep j hj)⟩,
        mt,mc,property,cm,im⟩
    exact bounded.asTest (by decide))
  change TestRun pub mac (.block (codes++tail)) s m _ ok post
  constructor
  · intro good
    obtain ⟨es,t,mt,run,cost,out⟩ := combined.complete ⟨good,trivial⟩
    exact ⟨es,t,mt,(Runs.block_append_iff (by simp [codes]) (by simp [tail])).mpr run,cost,out⟩
  · intro es t mt run
    obtain ⟨h,out⟩ := combined.sound ((Runs.block_append_iff (by simp) (by simp [tail])).mp run)
    exact ⟨h.1,out⟩

/-- The actual input state of any returning nine-stage prefix satisfies the native data compiler's
complete arithmetic and column specification. The same statement applies to the forward return. -/
theorem NativeEntry.demand (a : CubeArena.Layout) (controls : ℕ) (axis : Fin (a.n+1)) (input : ℕ → ℕ)
    (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (L : Pins.Layout) (slotted entry : Memory w) (base : ℕ)
    (native : NativeEntry a (pub 0).val controls axis R input
      (readings (Packing.Directory.ISA.publish slotted (pub 0).val base (D.directory pp lp))) (readings entry))
    (pinFrame : Pins.Frame L (readings pub) (readings slotted))
    (pointers : readings slotted ((pub 0).val+8) = base ∧ readings slotted ((pub 0).val+12) = a.records ∧
      readings slotted ((pub 0).val+72) = a.hostDirectory)
    (low : (pub 0).val+112 ≤ base) (endRaw : base+(D.directory pp lp).length*7 ≤ a.header.header)
    (sameTeams : D.teams=L.teams) (fields : 0<D.fields) (tails : D.entries*D.description ≤ D.teams*D.processors*(D.literal/2))
    (rows : (D.directory pp lp).length ≤ a.maxRows) (room : a.stop < 2^w)
    (teams : 0 < L.teams) (processors : D.processors = L.processors) (literal : D.literal = L.literal)
    (inputLow : L.processors*L.stride ≤ a.pairBase) (sub : L.ibase+L.count ≤ a.pairBase)
    {I : Type*} [Fintype I] {cell : I → Fin a.cells} {id : I ↪ ℕ} {widths : I → ℕ}
    (place : BankPlacement D pp lp I cell id widths) (bound : D.DestinationBounds)
    (fitBank : ∀ c, DataSlabs.size cell widths c ≤ a.cellStride) :
    DemandInput a D pp lp (a.receivingOwner (pub 0).val axis R input) pub entry ∧
    (DataWriter.layout (readings pub) (readings entry)).pins=L := by
  obtain ⟨_,_,actual⟩ := native.image
  exact DemandInput.of_publication a L slotted entry base _ pinFrame pointers native.low actual.hostRows low endRaw
    sameTeams fields tails rows room teams processors literal inputLow sub place bound fitBank

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
