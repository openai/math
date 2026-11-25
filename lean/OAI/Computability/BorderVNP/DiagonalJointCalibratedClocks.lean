import OAI.Computability.BorderVNP.DiagonalJointCalibratedFront
import OAI.Computability.BorderVNP.DiagonalWriterProfileClock

/-! # The two front clock windows of a joint return on its calibrated wire -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Transmission RoutingISA.CompactMachine
open Routing BorderVNP.Cube Physical Tally LocalRow PackedHistoryCircuit
open ScheduleClock

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {pub : Fin (R+1) → Arg → Word w}
    {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses} {ar : CubeArena.Layout}
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (B : ∀ u, BootedPinStart SparseExterior.driver G pub reg args pin ext u)
    (a : PinStart.JointPrefix id (fun u => (B u).start))

local notation3 (prettyPrint := false) "lib(" i ")" => install SparseExterior.driver n (B i).start.routines
local notation3 (prettyPrint := false) "sub(" i ")" => (B i).pins (a i).1
local notation3 (prettyPrint := false) "loc(" i ")" => G.pinLayout i (args i).ibase (args i).hbase (args i).starbase
local notation3 (prettyPrint := false) "cpu(" i ")" => G.processorFields i pin ext (args i).ibase (args i).hbase (args i).starbase
local notation3 (prettyPrint := false) "bf(" i ")" => G.transferFrame i (args i).header (args i).dst

variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    (word : Broadcast ar.n ar.header.d ar.header.cap)
    {frame hdr : ℕ}
local notation3 (prettyPrint := false) "declared" => Prod.mk (Fin.ofNat (ar.n+1) (readCode (ar.n+1) word.1))
  (fun (p : Sym2 (Fin ar.header.d)) (j : Fin (ar.n+1)) => readCode (ar.header.cap+1) (word.2 p j))
local notation3 (prettyPrint := false) "tab" => ar.table frame ((D.directory pp lp).length+ar.header.d.choose 2)
variable (label : Fin ar.cells → Label (ar.n+1) ar.header.d) (recv : Fin (D.directory pp lp).length → Fin ar.cells)
local notation3 (prettyPrint := false) "amount" => fun i : Fin (D.directory pp lp).length => (D.directory pp lp)[i.val].width
local notation3 (prettyPrint := false) "groups" => fun j : Fin ar.header.d => TeamNative.owner R
  (declarationWeight ar.header.blocks ar.b ar.K ar.h declared label recv amount) j.val
local notation3 (prettyPrint := false) "owners" => fun c : ℕ => if h:c<ar.cells then (groups) (label ⟨c,h⟩ (declared).1) else 0

set_option maxRecDepth 5500
set_option maxHeartbeats 1500000

/-- The admitted geometric labels of this prefix determine its route, and
each team's actual writer at its scanned directory pays the same two front
windows. A single calibrated wire serves the entire tuple. -/
theorem joint_calibrated_clocks
    (epoch : ∀ u, Returns epochPlacement (pub u) (lib(u)) (sub(u)).val.2.1 (sub(u)).val.2.2)
    (published : ∀ u, Returns Packing.Directory.ISA.program (pub u) (lib(u))
      (epoch u).val.2.1 (epoch u).val.2.2)
    (empty : ∀ u, (epoch u).val.1.flatMap TeamRAM.Event.choices=[])
    {atWriter : Fin (R+1) → Bank w × Memory w}
    (scanState : ∀ u, atWriter u=(published u).val.2)
    (W : ∀ u, SignedPrep.HeaderWriterReceipt ar D pp lp owners declared groups (loc(u)) (bf(u))
      (pub u) (lib(u)) (atWriter u).1 (atWriter u).2)
    {α ξ : ℝ} (fit : Diagonal.RouteTableInputs ar D α ξ n w frame link)
    (base : ∀ u, (pub u 0).val=frame) (headers : ∀ u, (args u).header=hdr)
    (pointers : ∀ u, TablePointers tab (readings (published u).val.2.2))
    (sources : ∀ u, ProfileRouteInputs (cpu(u)) (bf(u)) (pub u) (Pins.extendGuess (a u).1) (published u).val.2.2)
    (inputSize : ∀ u, (cpu(u)).header.length=(pub u 0).val)
    (subRoom : ∀ u, frame+13<(args u).ibase ∧ (args u).ibase+(loc(u)).count≤ar.header.header)
    (frameFit : ∀ u, (bf(u)).Fits w (pub u 0).val)
    {I : Type*} [Fintype I] {cell : I → Fin ar.cells} {key : I ↪ ℕ} {widths : I → ℕ}
    {mid : Memory w} {raw : ℕ} (writer : SlottedWriter ar D pp lp (loc(0)) (pub 0) mid raw cell key widths)
    (atRaw : (published 0).val.2.2=Packing.Directory.ISA.publish mid (pub 0 0).val raw (D.directory pp lp))
    (processors : D.processors=r) (literal : D.literal=G.program.length+t) (teams : D.teams=R+1)
    (literalRoom : D.literal≤TeamScales.literal α n) (headerRoom : (hdr:ℝ)≤r*(n:ℝ)^(24/25:ℝ))
    (old : Fin 81 → Word w) (fresh gates outputs bitWidth off ell controls : ℕ) (profile : List Bool)
    (claims : List (List Bool)) (pad : ℕ)
    (room : SignedPrep.PinnedRawInput (ar:=ar) (D:=D) (pp:=pp) (lp:=lp) (pub:=pub 0) (slotted:=mid) (base:=raw)
      (bf(0)) old fresh gates outputs bitWidth off ell controls profile claims pad word R (TeamScales.exterior ξ r n))
    (valid : declarationInRange word)
    (allowed : broadcastAllowed R (TeamScales.exterior ξ r n) ar.header.blocks ar.b ar.K ar.h label recv amount word)
    (hosts : ∀ i,(recv i).val=(D.directory pp lp)[i.val].cell)
    (pos : 0<D.processors) (two : D.fields≤2) (block : 0<D.block)
    (budget : PhaseCharges) (count geometry : ℕ) (bound : CoreAt α ξ n)
    (coreRoom : 2048*(TeamScales.exterior ξ r n+(R+1+1)^3+(tab).count+r+1)≤budget.core)
    (beforeRoom : ∀ u, geometry+beforeDirectory (R+1) D.sites D.entries+
      rawScheduleTicks ar frame (args u).dst (declared).1.val R (D.directory pp lp).length
        (readings (atWriter u).2)≤budget.before) :
    ∀ u, ProfileClock (ar:=ar) id B a u hdr count geometry (deliveryScanTicks D.entries (R+1) D.sites)
      (atWriter u) budget := by
  obtain ⟨wire,head,ready,_⟩ := joint_calibrated_front id B a word epoch published empty scanState W fit
    base headers pointers sources inputSize subRoom frameFit writer atRaw processors literal teams literalRoom
    headerRoom old fresh gates outputs bitWidth off ell controls profile claims pad room valid
  intro u
  exact profileClock_of_writer (ar:=ar) (D:=D) (pp:=pp) (lp:=lp) (frame:=frame) (label:=label) (recv:=recv)
    (decl:=declared) (α:=α) (ξ:=ξ) (published:=atWriter u) id B a u ready head (fit.physicalLink.trans (by rw [room.teamArena]))
    allowed.2 hosts processors literal literalRoom pos writer.fields two block (headers u ▸ W u)
    rfl budget count geometry bound coreRoom (beforeRoom u)

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
