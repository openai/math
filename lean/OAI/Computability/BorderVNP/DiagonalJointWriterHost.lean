import OAI.Computability.BorderVNP.DiagonalJointWriterProfile
import OAI.Computability.BorderVNP.DiagonalSignedWriterReceipt
import OAI.Computability.BorderVNP.DiagonalReturnedRouteState
import OAI.Computability.BorderVNP.DiagonalNativeOwnerBankObserved
import OAI.Computability.BorderVNP.DiagonalSignedFragmentPublication

/-! # Delivery and retained host words of the chosen writer on a joint prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open RoutingISA.CompactMachine ProcessorSlots BorderVNP.Cube Physical Tally Scatter Scatter.Assignment FiniteEvaluator

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {wire : WireLayout (R+1) r link} {header : List Bool} {ar : CubeArena.Layout}
    {decl : LengthDeclaration ar.n ar.header.d} {pin : Fin d → Bool}
    {pub : HeaderExterior wire header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior wire header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior wire header → Fin (R+1) → Bank w}
    {mem : HeaderExterior wire header → Fin (R+1) → Memory w}
    (F : PreparationFrame G wire ar decl header pin pub mac reg mem)
    (x : HeaderExterior wire header) {hardware : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
    (B : ∀ u, BootedPinStart SparseExterior.driver G (pub x) hardware args pin x.val u)
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (a : PinStart.JointPrefix id (fun u => (B u).start))

local notation3 (prettyPrint := false) "V(" u ")" => PinStart.visits id (fun i => (B i).start) (a u)
local notation3 (prettyPrint := false) "pins" => fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u)
local notation3 (prettyPrint := false) "lib" => fun u => install SparseExterior.driver n (B u).start.routines

set_option maxRecDepth 6000
set_option maxHeartbeats 1500000

/-- The physical relay and shared writers of a joint return are recovered on its own
routed registers, memory, and shared word, for any of the later owned reports. -/
theorem PreparationFrame.jointDelivery
    (installed : ∀ u, mac x u=(lib) u)
    (start : ∀ u, (reg x u,mem x u)=((B u).pins (a u).1).val.2) :
    ∃ (H : Fin (R+1) → TeamHistory w)
      (f : ReturnedDelivery G pin x.val wire F.dataDir F.privatePlacement F.livePlacement F.cellOwner
        F.origin F.stride H pins),
      f.table=F.tab ∧ f.row=F.row ∧ f.before=(fun u => readings (V(u)).profile.val.2.2) ∧
      SharedWriters f F.rows (F.source x) ∧
      (∀ u, (H u).pub=pub x u ∧ (H u).macros=(lib) u ∧ (H u).history.val.2=(V(u)).routing.val.2) ∧
      (∀ u, Pins.SubstitutionAt ((pins) u) (F.guess u) (H u).initial) ∧
      f.receivedRows F.rows F.group =
        readRouteRows F.row F.rows F.group (fun u => (V(u)).routing.val.2.2) := by
  have profiles := F.jointProfile x B id a installed start
  have ram := funext fun u => congrArg (fun z => z.2.2) (profiles u)
  have ready := F.initialized x
  rw [ram] at ready
  have emitted (u : Fin (R+1)) := F.emitted x u
  simp only [profiles] at emitted
  obtain ⟨H,f,table,rows,before,writer,actual,subst,read⟩ := ready.ownedDelivery lib (fun u => (V(u)).profile.val.2.1)
    (fun u => (V(u)).routing) emitted (F.fitted x) F.records F.count F.room
  exact ⟨H,f,table,rows,before,writer,actual,subst,read F.group⟩

variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)}
    {group : Fin ar.header.d → Fin (R+1)} {frame : ℕ} {guess : Fin (R+1) → ℕ → Bool}
    {dst ib hb sb : Fin (R+1) → ℕ}
    {epoch : ∀ y u, Returns epochPlacement (pub y u) (mac y u) (reg y u) (mem y u)}
    {published : ∀ y u, Returns Packing.Directory.ISA.program (pub y u) (mac y u)
      (epoch y u).val.2.1 (epoch y u).val.2.2}
    {bootFrame : HeaderExterior wire header → Fin (R+1) → BroadcastFrame}
    (received : ∀ y u, SignedPrep.HeaderWriterReceipt ar D pp lp owner decl group (G.pinLayout u (ib u) (hb u) (sb u))
      (bootFrame y u) (pub y u) (mac y u) (published y u).val.2.1 (published y u).val.2.2)
    (chosen : PreparationFrame.WriterProjection G wire ar D pp lp owner decl group frame header pin guess dst ib hb sb
      pub mac reg mem epoch published (fun y u => (received y u).endReg) (fun y u => (received y u).out)
      (fun y u => (received y u).events) (fun y u => (received y u).history) F)

variable {H : Fin (R+1) → TeamHistory w}
    {f : ReturnedDelivery G pin x.val wire F.dataDir F.privatePlacement F.livePlacement F.cellOwner F.origin F.stride H
      (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))}
    (writer : SharedWriters f F.rows (F.source x))
    {template : DiagonalTallyPacketEmit.Frame} {count : ℕ}
    (handoff : OwnedHandoff f F.rows (F.source x) ar decl F.group template id count
      (PinStart.ownedVisits (ar:=ar) (fun i => (B i).start) a))
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    {q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners}
    (observed : ObservedOwned ar decl F.group (PinStart.ownedVisits (ar:=ar) (fun i => (B i).start) a) owners
      (f.receivedRows F.rows F.group) q) (u : Fin (R+1))

include chosen writer handoff observed in
/-- The actual owned return retains the original publication below the header and
the data writer's output tables up to the routing records. The signed writer receipt
and the selected frame identify both input memories. -/
theorem PreparationFrame.WriterProjection.jointHostRetention :
    CubeAllocation.HostRetention ar (readings (pub x u) 0) (readings (published x u).val.2.2)
      (readings (received x u).history.dataInput) (readings (V(u)).owned.val.2.2) := by
  let W := (received x u).history
  have done := (received x u).done
  have primary : readings (pub x u) 0+112 ≤ ar.header.header := by
    have pubEq : pub x u=(H u).pub := handoff.pub u
    rw [pubEq]
    exact (handoff.room u).primary
  have rowFrame : F.rows.frame=readings (pub x u) 0 :=
    (handoff.frame u).trans (congrFun (congrArg readings (handoff.pub u)) 0).symm
  have keep (j : ℕ) (hj : j<ar.records) (extent : j<ar.header.header+13 ∨ ar.publicBase≤j)
      (not13 : j≠readings (pub x u) 0+13) (not46 : j≠readings (pub x u) 0+46) :
      readings (V(u)).owned.val.2.2 j=readings W.dataInput j := by
    have kept := writer.owned_output_static (F.frame x) handoff observed u j hj extent (rowFrame ▸ not13) not46
    have same : W.sharedInput j=W.dataInput j := by
      rw [W.dataImage done.emission.demand.ready,DataWriter.publish,Function.update_of_ne (show j≠(pub x u 0).val+13 from not13),
        Packing.Directory.ISA.putWords_outside _ _ _ _ (.inl (done.emission.demand.records ▸ hj))]
    exact kept.trans ((congrFun (chosen.image x u) j).trans (congrArg Fin.val same))
  obtain ⟨_,_,_,_,_,_,_,_⟩ := ar.writer_order
  refine ⟨primary,fun j hj n₁₃ n₄₆ => (keep j (by omega) (.inl (by omega)) n₁₃ n₄₆).trans
    (congrArg Fin.val (done.low j hj)),?_⟩
  intro j lo hi
  exact keep j hi (.inr lo) (by omega) (by omega)

open SignedTaskArena DiagonalTallyAllocation DiagonalTallyCellReports

include chosen writer handoff observed in
/-- On this prefix's own report memory, the native publisher, selected writer,
and signed reporter preserve the host pointers and compacted demand count. -/
theorem PreparationFrame.WriterProjection.jointReportWords
    (task : SignedTaskArena.Layout) (cube : task.cube=ar)
    {placed : Memory w} {base offsets ctl live ports bundles bits description : ℕ}
    (publishedAt : (published x u).val.2.2=Packing.Directory.ISA.publish placed
      (pub x u 0).val base (D.directory pp lp))
    (fits : (D.directory pp lp).length < 2^w)
    (host : Fin bundles → Fin task.cube.cells) (header : Fin bundles → Packing.BottomReports.BundleHeader)
    {l : ReportLayout} {cs : List (ReportCell l)} {cur : ReportCursor} {banks : CellBanks.Layout}
    (seed : PreparedReportInput (pub x u) (V(u)).controls.val.2.2 cs cur description)
    (ready : OpenSuffix.Ready (task.openInputs u.val (pub x u 0).val offsets ctl live ports bundles bits host header)
      (pub x u 0).val (readings (V(u)).owned.val.2.2) w)
    (position : OpenSuffix.Placement (task.openInputs u.val (pub x u 0).val offsets ctl live ports bundles bits host header)
      task.cube task.before (pub x u 0).val (readings (V(u)).owned.val.2.2))
    (alloc : ReportAllocation task.before task.after banks l cs cur) (start : banks.bankStart=task.cube.cellBank) :
    let ram := readings (V(u)).reports.val.2.2
    ReportWords task (pub x u 0).val
      (readings (Packing.Directory.ISA.publish placed (pub x u 0).val base (D.directory pp lp)))
      (readings (received x u).history.dataInput) ram true ∧
      (FragmentRows.Layout.fromFrame (pub x u 0).val ram).count=(D.directory pp lp).length := by
  intro ram
  have keep := PreparationFrame.WriterProjection.jointHostRetention F x B id a received chosen writer handoff observed u
  rw (occs := .pos [1]) [←cube] at keep
  rw (occs := .pos [1]) [publishedAt] at keep
  have words := task.signed_report_words host header (V(u)).controls (V(u)).reports seed keep ready position alloc start
  exact ⟨words,words.compacted_count fits⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
