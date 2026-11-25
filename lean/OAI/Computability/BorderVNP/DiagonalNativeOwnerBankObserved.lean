import OAI.Computability.BorderVNP.DiagonalNativeOwnerBankRoster
import OAI.Computability.BorderVNP.DiagonalPhysicalPinStart
import OAI.Computability.BorderVNP.DiagonalPositiveCoreSignedDirectory
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostRetention
import OAI.Computability.BorderVNP.RoutingISASignedPrepOwned

/-! # Dispatch ownership on the actually observed all-team positive preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PositiveTeam

open VPVNP.BurstRAM CellDispatch CompactMachine CellMacro.Generator BorderVNP.Cube

variable {ar : CubeArena.Layout} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ}
    {gen : Fragment IO} {n w R : ℕ}

/-- All chronological stages of one true positive prefix, starting after its
own substituted pin guess. -/
noncomputable abbrev stages {dim box lanes choices supply : ℕ} {id : TableEntry dim box lanes choices supply → ℕ}
    (S : PositiveTeam id gen n w) (p : S.Prefix) :=
  (SignedPrep.visitsEquiv id S.pub (install gen n S.routines)
    (S.pins p.1).val.2.1 (S.pins p.1).val.2.2).symm p.2

/-- The actual public registers, RAM and owned histories for a simultaneous
tuple of returning positive preparations. -/
noncomputable abbrev ownedScans (S : Fin (R+1) → PositiveTeam id gen n w) (p : ∀ u, (S u).Prefix) :=
  SignedPrep.ownedHistory ar (fun u => (S u).pub) (fun u => install gen n (S u).routines)
    (fun u => ((S u).stages (p u)).constants.val.2.1) (fun u => ((S u).stages (p u)).constants.val.2.2)
    (fun u => ((S u).stages (p u)).owned)

end RoutingISA.Evaluator.PositiveTeam

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM CellDispatch CompactMachine CellMacro.Generator BorderVNP.Cube

variable {ar : CubeArena.Layout} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ}
    {gen : Fragment IO} {n w R : ℕ}

/-- All chronological stages of one true positive prefix, starting after its
own substituted pin guess. -/
noncomputable abbrev visited {dim box lanes choices supply : ℕ} {id : TableEntry dim box lanes choices supply → ℕ}
    (S : PinStart gen n w) (p : S.Prefix id) :=
  (SignedPrep.visitsEquiv id S.pub (install gen n S.routines)
    (S.pins p.1).val.2.1 (S.pins p.1).val.2.2).symm p.2

/-- The actual public registers, RAM and owned histories for a simultaneous
tuple of returning positive preparations. -/
noncomputable abbrev ownedVisits (S : Fin (R+1) → PinStart gen n w) (p : ∀ u, (S u).Prefix id) :=
  SignedPrep.ownedHistory ar (fun u => (S u).pub) (fun u => install gen n (S u).routines)
    (fun u => ((S u).visited (p u)).constants.val.2.1) (fun u => ((S u).visited (p u)).constants.val.2.2)
    (fun u => ((S u).visited (p u)).owned)

end RoutingISA.Evaluator.PinStart

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing
open BorderVNP.Cube Physical Scatter TeamRows Scatter.Assignment FiniteEvaluator
open CellDispatch CompactMachine CellMacro.Generator ScheduleClock PositiveTeam DiagonalTallyCellReports

section Bare

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {receive : ℕ → Fin (R+1)} {origin stride : ℕ}
    {hist : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    {f : ReturnedDelivery G pin ext wire D pp lp receive origin stride hist pins} {g : SharedRows.Layout}
    {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
    {a : SignedTaskArena.Layout} {id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ}
    {gen : Fragment IO} (S : Fin (R+1) → PinStart gen n w) (p : ∀ u, (S u).Prefix id)
    {decl : LengthDeclaration a.cube.n a.cube.header.d} {group : Fin a.cube.header.d → Fin (R+1)}
    {A : Type*} [Fintype A] (label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d)
    (recv : A → Fin a.cube.cells) (width : A → ℕ)
    {template : DiagonalTallyPacketEmit.Frame} {count : ℕ}
    {offsets live ports bundles b description ctl u₀ v₀ k : ℕ}
    {l : ReportLayout} {cursor : ReportCursor} {cs : List (ReportCell l)}
    (bundleOwner : Fin bundles → Fin a.cube.cells) (header : Fin bundles → Packing.BottomReports.BundleHeader)
    {Site : Type}

set_option quotPrecheck false
local notation "own" => greedyOwner R a.cube.b a.cube.s label recv width
local notation "F" => PinStart.ownedVisits (ar:=a.cube) S p

set_option maxHeartbeats 800000 in
/-- Read the common selector's physical owner directly on every earlier
owned-scan result, before the private report source is chosen. Independent
team RAM images can contain different data away from the schedule. -/
theorem SharedWriters.bare_received_owner (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) a.cube.header.blocks a.cube.K a.cube.h decl group)
    (handoff : OwnedHandoff f g src a.cube decl group template id count F)
    {q : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) own}
    (receipt : ObservedOwned a.cube decl group F own (f.receivedRows g group) q) (u : Fin (R+1))
    {bits : ℕ} {rr rt : Bank w} {initial last : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory a.cube.n bits (hist u).pub (hist u).macros rr initial es rt last)
    (data : DataReady (hist u).pub W.dataInput)
    (records : (DataWriter.layout (readings (hist u).pub) (readings W.dataInput)).output=a.cube.records)
    (source : src u=readings W.sharedInput) (profile : ℕ → ℕ) :
    let V := (S u).visited (p u)
    let head := readings (S u).pub 0
    NativeEntry a.cube head ctl decl.1 R profile (readings initial) (readings W.dataInput) →
    GroupWeights.PhysicalImage (LocalRow.weightLayout a.cube head decl.1.val) profile
      a.cube.header.blocks a.cube.b a.cube.K a.cube.h decl label recv width →
    ∀ c : Fin a.cube.cells, readings V.owned.val.2.2 (a.cube.hostDirectory+2*c.val)=
      (own q.1 (label c (chosen a.cube.b a.cube.s q.1))).val := by
  intro V head entry physical c
  have pubEq : (S u).pub=(hist u).pub := handoff.pub u
  have frame : head=readings (hist u).pub 0 := congrFun (congrArg readings pubEq) 0
  have keep := writer.owned_host_retention symbols handoff receipt u W data records source profile (frame ▸ entry)
  have pass : passesLengths a.cube.b a.cube.s q.1 decl := (passesLengths_iff ..).mpr receipt.observed.1.symm
  obtain ⟨scheduled,sched,_⟩ := entry.image
  let banks := a.cube.cellWriter head ctl decl.1
  have picked := selected_cell_owner q.1 pass label recv width (cell_schedule_layout a.cube head ctl R decl.1)
    sched physical c
  have positive : 0<a.cube.header.d := Nat.zero_lt_of_lt (label c decl.1).isLt
  have stored := (banks.written_at scheduled (show c.val < banks.cells from c.isLt)).1
  exact (a.retainedOwner entry keep c).trans
    ((a.cube.receivingOwner_eq head ctl decl.1 R profile scheduled sched positive c.val c.isLt).symm.trans
      (stored.symm.trans picked))

set_option maxHeartbeats 1600000 in
/-- Every complete positive team tuple on its recovered selector and routed
cube assignment has the true global row count, order and owner word on the
actual post-memory of each team. The native report scanner can return any
count or use assignment on its received cells. -/
theorem SharedWriters.bare_owner_roster (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) a.cube.header.blocks a.cube.K a.cube.h decl group)
    (handoff : OwnedHandoff f g src a.cube decl group template id count F)
    {q : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) own}
    (receipt : ObservedOwned a.cube decl group F own (f.receivedRows g group) q) (u : Fin (R+1))
    {bits : ℕ} {rr rt : Bank w} {initial last : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory a.cube.n bits (hist u).pub (hist u).macros rr initial es rt last)
    (data : DataReady (hist u).pub W.dataInput)
    (records : (DataWriter.layout (readings (hist u).pub) (readings W.dataInput)).output=a.cube.records)
    (source : src u=readings W.sharedInput) (profile : ℕ → ℕ) :
    let V := (S u).visited (p u)
    let head := readings (S u).pub 0
    let rows := a.controlRows u.val head offsets ctl live ports
    let H := a.openInputs u.val head offsets ctl live ports bundles b bundleOwner header
    let report := readings V.reports.val.2.2
    let fr := FragmentRows.Layout.fromFrame head report
    let parts := (argumentVisitsEquiv (S u).pub (install gen n (S u).routines)
      V.reports.val.2.1 V.reports.val.2.2).symm V.arguments
    NativeEntry a.cube head ctl decl.1 R profile (readings initial) (readings W.dataInput) →
    GroupWeights.PhysicalImage (LocalRow.weightLayout a.cube head decl.1.val) profile
      a.cube.header.blocks a.cube.b a.cube.K a.cube.h decl label recv width →
    a.OpenRoom head offsets ctl live ports bundles (2^b) w →
    OpenSuffix.Placement H a.cube a.before head (readings V.owned.val.2.2) →
    OpenSuffix.Ready H head (readings V.owned.val.2.2) w →
    PreparedReportInput (S u).pub V.controls.val.2.2 cs cursor description →
    ReportAllocation a.before a.after (a.cube.cellWriter head ctl decl.1) l cs cursor →
    a.SparsePlacement head ctl → fr.Fits w report → report (head+92)=ctl →
    (∀ j : Fin 37, report (ctl+j.val)=a.controls j.val) → fr.host.count=a.cube.cables →
    report (head+9)≤a.cube.maxRows → report (head+11)=a.cube.cells → a.endAddress w u₀ v₀ k<2^w →
    ∀ (placed : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
      (packet : SparseCallInput (S u).pub parts.2.1.val.2.2),
    ProducedRoster a rows (readings parts.1.val.2.2) placed geom extra packet →
    (∀ c : Fin a.cube.cells, readings V.owned.val.2.2 (a.cube.hostDirectory+2*c.val)=
      (own q.1 (label c (chosen a.cube.b a.cube.s q.1))).val) ∧
    OwnerTable (S u).pub (p u).2.val.2.2 ⟨u.val,a.before.limit,a.cube.cells⟩
      (ownerWord (fun c : Fin a.cube.cells => own q.1 (label c (chosen a.cube.b a.cube.s q.1)))) := by
  intro V head rows H report fr parts entry physical room position ready seed alloc place fit ptr words cables raw cells high
    placed geom extra packet produced
  have pubEq : (S u).pub=(hist u).pub := handoff.pub u
  have frame : head=readings (hist u).pub 0 := congrFun (congrArg readings pubEq) 0
  have keep := writer.owned_host_retention symbols handoff receipt u W data records source profile (frame ▸ entry)
  have pass : passesLengths a.cube.b a.cube.s q.1 decl := (passesLengths_iff ..).mpr receipt.observed.1.symm
  constructor
  · exact writer.bare_received_owner S p label recv width symbols handoff receipt u W data records source profile entry physical
  have roster := selected_ownerTable_on_visits label recv width q.1 bundleOwner header V pass physical entry keep
    room position ready seed alloc place fit ptr words cables raw cells high placed geom extra packet produced
  let E := SignedPrep.visitsEquiv id (S u).pub (install gen n (S u).routines)
    ((S u).pins (p u).1).val.2.1 ((S u).pins (p u).1).val.2.2
  change OwnerTable _ (E (E.symm (p u).2)).val.2.2 _ _ at roster
  rw [E.apply_symm_apply] at roster
  exact roster

end Bare

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {receive : ℕ → Fin (R+1)} {origin stride : ℕ}
    {hist : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    {f : ReturnedDelivery G pin ext wire D pp lp receive origin stride hist pins} {g : SharedRows.Layout}
    {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
    {a : SignedTaskArena.Layout} {id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ}
    {gen : Fragment IO} (S : Fin (R+1) → PositiveTeam id gen n w) (p : ∀ u, (S u).Prefix)
    {decl : LengthDeclaration a.cube.n a.cube.header.d} {group : Fin a.cube.header.d → Fin (R+1)}
    {A : Type*} [Fintype A] (label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d)
    (recv : A → Fin a.cube.cells) (width : A → ℕ)
    {template : DiagonalTallyPacketEmit.Frame} {count : ℕ}
    {offsets live ports bundles b description ctl u₀ v₀ k : ℕ}
    {l : ReportLayout} {cursor : ReportCursor} {cs : List (ReportCell l)}
    (bundleOwner : Fin bundles → Fin a.cube.cells) (header : Fin bundles → Packing.BottomReports.BundleHeader)
    {Site : Type}

set_option quotPrecheck false
local notation "own" => greedyOwner R a.cube.b a.cube.s label recv width
local notation "F" => ownedScans (ar:=a.cube) S p

set_option maxHeartbeats 1600000 in
/-- Every complete positive team tuple on its recovered selector and routed
cube assignment has the true global row count, order and owner word on the
actual post-memory of each team. The native report scanner can return any
count or use assignment on its received cells. -/
theorem SharedWriters.positive_owner_roster (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) a.cube.header.blocks a.cube.K a.cube.h decl group)
    (handoff : OwnedHandoff f g src a.cube decl group template id count F)
    {q : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) own}
    (receipt : ObservedOwned a.cube decl group F own (f.receivedRows g group) q) (u : Fin (R+1))
    {bits : ℕ} {rr rt : Bank w} {initial last : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory a.cube.n bits (hist u).pub (hist u).macros rr initial es rt last)
    (data : DataReady (hist u).pub W.dataInput)
    (records : (DataWriter.layout (readings (hist u).pub) (readings W.dataInput)).output=a.cube.records)
    (source : src u=readings W.sharedInput) (profile : ℕ → ℕ) :
    let V := (S u).stages (p u)
    let head := readings (S u).pub 0
    let rows := a.controlRows u.val head offsets ctl live ports
    let H := a.openInputs u.val head offsets ctl live ports bundles b bundleOwner header
    let report := readings V.reports.val.2.2
    let fr := FragmentRows.Layout.fromFrame head report
    let parts := (argumentVisitsEquiv (S u).pub (install gen n (S u).routines)
      V.reports.val.2.1 V.reports.val.2.2).symm V.arguments
    NativeEntry a.cube head ctl decl.1 R profile (readings initial) (readings W.dataInput) →
    GroupWeights.PhysicalImage (LocalRow.weightLayout a.cube head decl.1.val) profile
      a.cube.header.blocks a.cube.b a.cube.K a.cube.h decl label recv width →
    a.OpenRoom head offsets ctl live ports bundles (2^b) w →
    OpenSuffix.Placement H a.cube a.before head (readings V.owned.val.2.2) →
    OpenSuffix.Ready H head (readings V.owned.val.2.2) w →
    PreparedReportInput (S u).pub V.controls.val.2.2 cs cursor description →
    ReportAllocation a.before a.after (a.cube.cellWriter head ctl decl.1) l cs cursor →
    a.SparsePlacement head ctl → fr.Fits w report → report (head+92)=ctl →
    (∀ j : Fin 37, report (ctl+j.val)=a.controls j.val) → fr.host.count=a.cube.cables →
    report (head+9)≤a.cube.maxRows → report (head+11)=a.cube.cells → a.endAddress w u₀ v₀ k<2^w →
    ∀ (placed : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
      (packet : SparseCallInput (S u).pub parts.2.1.val.2.2),
    ProducedRoster a rows (readings parts.1.val.2.2) placed geom extra packet →
    OwnerTable (S u).pub ((S u).postMemory (p u)) ⟨u.val,a.before.limit,a.cube.cells⟩
      (ownerWord (fun c : Fin a.cube.cells => own q.1 (label c (chosen a.cube.b a.cube.s q.1)))) := by
  intro V head rows H report fr parts entry physical room position ready seed alloc place fit ptr words cables raw cells high
    placed geom extra packet produced
  exact (SharedWriters.bare_owner_roster (fun u => (S u).start) p label recv width bundleOwner header writer
    symbols handoff receipt u W data records source profile entry physical room position ready seed alloc place fit ptr
    words cables raw cells high placed geom extra packet produced).2

end TeamContraction

end BorderVNP
end Computability
end OAI
