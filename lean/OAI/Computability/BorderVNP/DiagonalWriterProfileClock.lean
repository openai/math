import OAI.Computability.BorderVNP.DiagonalBootedJointClock
import OAI.Computability.BorderVNP.DiagonalSignedWriterReceipt
import OAI.Computability.BorderVNP.DiagonalAdmittedEndpointWidths

/-! # The two front windows of a team's paid writer on its calibrated route -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube Physical TeamContraction ScheduleClock

/-- Use the paid writer at the paired placement/directory scan's own
registers and RAM, including the four native words in its clock. -/
theorem HeaderWriterReceipt.scheduleAt
    {ar : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {R w : ℕ}
    {owner : ℕ → Fin (R+1)} {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R+1)}
    {pins : Pins.Layout} {f : BroadcastFrame} {pub : Arg → Word w} {mac lib : TeamOpcode.Macros w 8}
    {s s' : Bank w} {m m' : Memory w} {frame : ℕ}
    (receipt : HeaderWriterReceipt ar D pp lp owner decl group pins f pub mac s m)
    (installed : mac=lib) (returned : (s,m)=(s',m')) (base : (pub 0).val=frame) :
    PublicSchedule ar D pp lp owner decl group pins pub lib s' m'
      (rawScheduleTicks ar frame f.dst decl.1.val R (D.directory pp lp).length (readings m')) True := by
  cases installed
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj returned
  subst frame
  exact receipt.done.publicSchedule receipt.cost

end RoutingISA.Evaluator.SignedPrep

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open RoutingISA.CompactMachine ProcessorSlots BorderVNP.Cube Physical Tally PackedHistoryCircuit LocalRow
open Cube.MeanChoice Cube.LabelIndex Crossing RoutingISA.Evaluator.ScheduleClock TeamScales Finset

/-- The two front windows after calibrating the header, route rows and writer
on a joint prefix. The remaining measurements are the startup geometry and its
own directory scan; their output state fixes the subsequent group schedule. -/
def ProcessorSlots.BootedPinStart.ProfileClock {R r t d link inner n w : ℕ} {Edge : Type}
    {G : Wiring R r t d link inner n Edge} {pub : Fin (R+1) → Arg → Word w}
    {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses} {pin : Fin d → Bool}
    {ext : Exterior R r link → Bool} {ar : CubeArena.Layout}
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (B : ∀ u, BootedPinStart SparseExterior.driver G pub reg args pin ext u)
    (a : PinStart.JointPrefix id (fun k => (B k).start)) (u : Fin (R+1))
    (header count geometry scanTicks : ℕ) (published : Bank w × Memory w) (budget : PhaseCharges) : Prop :=
  let mac := install SparseExterior.driver n (B u).start.routines
  let f := G.transferFrame u (args u).header (args u).dst
  let fields := G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase
  let v := PinStart.visits id (fun k => (B k).start) (a u)
  ∀ (runs : (Fin (B u).start.guessWidth → Bool) ≃ Returns (withStartup pinGeometry) (pub u) mac (reg u)
      (processorMemory fields w))
    (scan : Returns (.seq PrivatePlacement.program Packing.Directory.ISA.program) (pub u) mac
      (runs (a u).1).val.2.1 (runs (a u).1).val.2.2),
    (args u).header=header → w≤count → count≤r →
    (∀ g,(runs g).val.1.flatMap TeamRAM.Event.choices=List.ofFn g) →
    traceCost (runs (a u).1).val.1≤jointBudget count w+f.readTicks+2+
      (pinSetup.slots+17*(f.processors*f.literal)+1)+geometry →
    scan.val.2=published → traceCost scan.val.1 ≤ scanTicks →
    (B u).used+traceCost ((B u).pins (a u).1).val.1+traceCost v.profile.val.1+traceCost v.routing.val.1 ≤
      budget.core+budget.before


section Returned

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pub : Fin (R+1) → Arg → Word w} {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {ar : CubeArena.Layout}
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ) (B : ∀ u, BootedPinStart SparseExterior.driver G pub reg args pin ext u)
    (a : PinStart.JointPrefix id (fun i => (B i).start)) (u : Fin (R+1))
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {frame : ℕ} {wire : WireLayout (R+1) r link}
    {header : ℕ} {label : Fin ar.cells → Label (ar.n+1) ar.header.d} {recv : Fin (D.directory pp lp).length → Fin ar.cells}
    {decl : LengthDeclaration ar.n ar.header.d} {α ξ : ℝ}
local notation3 (prettyPrint := false) "entries" => D.directory pp lp
local notation3 (prettyPrint := false) "amount" => fun i : Fin (entries).length => (entries)[i.val].width
local notation3 (prettyPrint := false) "group" => fun j : Fin ar.header.d => TeamNative.owner R
  (declarationWeight ar.header.blocks ar.b ar.K ar.h decl label recv amount) j.val
local notation3 (prettyPrint := false) "owner" => fun c : ℕ => if h:c<ar.cells then (group) (label ⟨c,h⟩ decl.1) else 0
local notation3 (prettyPrint := false) "row" => RouteRecords.combinedRow entries owner ar.header.blocks ar.K ar.h decl group
local notation3 (prettyPrint := false) "table" => ar.table frame ((entries).length+ar.header.d.choose 2)
local notation3 (prettyPrint := false) "visit(" i ")" => PinStart.visits id (fun j => (B j).start) (a i)

/-- The admitted load and a real local writer pay the two initial phases on
any calibrated layout for the physical memory of the entire tuple. -/
theorem ProcessorSlots.BootedPinStart.profileClock_of_writer
    {guess : Fin (R+1) → ℕ → Bool}
    (ready : SharedRoutePrepared G pin ext wire D pp lp owner ar.cellBank ar.cellStride table row pub
      (fun i => (visit(i)).profile.val.2.2) (fun i => (args i).dst) (fun i => (args i).ibase)
      (fun i => (args i).hbase) (fun i => (args i).starbase) guess)
    (same : wire.header=header) (linkFit : link=TeamScales.link ξ (R+1) n)
    (admitted : declarationCapacity R (exterior ξ r n) ar.header.blocks ar.b ar.K ar.h decl label recv amount)
    (hosts : ∀ i,(recv i).val=(entries)[i.val].cell) (pr : D.processors=r) (lit : D.literal=G.program.length+t)
    (literalRoom : D.literal≤TeamScales.literal α n)
    (pos : 0<D.processors) (fieldsPos : 0<D.fields) (two : D.fields≤2) (block : 0<D.block)
    {pins : Pins.Layout} {lib : TeamOpcode.Macros w 8} {published : Bank w × Memory w}
    (W : SignedPrep.HeaderWriterReceipt ar D pp lp owner decl group pins (G.transferFrame u header (args u).dst)
      (pub u) lib published.1 published.2)
    (installed : lib=install SparseExterior.driver n (B u).start.routines)
    (budget : PhaseCharges) (count geometry : ℕ) (bound : CoreAt α ξ n)
    (coreRoom : 2048*(exterior ξ r n+(R+1+1)^3+(table).count+r+1)≤budget.core)
    (beforeRoom : geometry+beforeDirectory (R+1) D.sites D.entries+
      rawScheduleTicks ar frame (args u).dst decl.1.val R (entries).length (readings published.2)≤budget.before) :
    BootedPinStart.ProfileClock (ar:=ar) id B a u header count geometry (deliveryScanTicks D.entries (R+1) D.sites)
      published budget := by
  dsimp only [BootedPinStart.ProfileClock]
  intro runs scan hdr wc cr words runCost scanState scanCost
  have load (v : Fin (R+1)) :
      (∑ i ∈ range (table).count, endpointWidth ((row) i) v.val) ≤
        3*r*(TeamScales.literal α n)+exterior ξ r n/256 := by
    calc
      _ ≤ 3*D.processors*D.literal+exterior ξ r n/256 := admitted.row_endpoints D pp lp label recv hosts pos fieldsPos two block v
      _ ≤ 3*D.processors*(TeamScales.literal α n)+exterior ξ r n/256 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ literalRoom) _
      _ = _ := by rw [pr]
  have paid := W.scheduleAt installed scanState.symm (show (pub u 0).val=frame from ready.base u)
  exact BootedPinStart.early_on_joint_prefix id B a u bound ready runs words geometry count D.sites runCost
    scan scanCost _ _ paid (hdr.trans same.symm) ready.teams linkFit (lit.symm.trans_le literalRoom)
    wc cr load budget coreRoom (by rw [congrArg Prod.snd scanState]; exact beforeRoom)

end Returned

end TeamContraction

end BorderVNP
end Computability
end OAI
