import OAI.Computability.BorderVNP.DiagonalJointSparseWindow
import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart
import OAI.Computability.BorderVNP.DiagonalSignedReferenceCalibration
import OAI.Computability.BorderVNP.DiagonalSignedWriterReceipt
import OAI.Computability.BorderVNP.RoutingISASignedPrepWriterFrame

/-! # Calibrating the signed route on the joint prefix's own exterior -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Transmission RoutingISA.CompactMachine
open Routing BorderVNP.Cube Physical Tally LocalRow PackedHistoryCircuit
open private schedule_native from OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {pub : Fin (R+1) → Arg → Word w}
    {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses} {ar : CubeArena.Layout}
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (B : ∀ u, BootedPinStart SparseExterior.driver G pub reg args pin ext u)
    (a : PinStart.JointPrefix id (fun u => (B u).start))

local notation3 (prettyPrint := false) "vst(" i ")" => PinStart.visits id (fun k => (B k).start) (a i)
local notation3 (prettyPrint := false) "lib(" i ")" => install SparseExterior.driver n (B i).start.routines
local notation3 (prettyPrint := false) "sub(" i ")" => (B i).pins (a i).1
local notation3 (prettyPrint := false) "digits" => fun i => Pins.extendGuess (a i).1
local notation3 (prettyPrint := false) "loc(" i ")" => G.pinLayout i (args i).ibase (args i).hbase (args i).starbase
local notation3 (prettyPrint := false) "cpu(" i ")" => G.processorFields i pin ext (args i).ibase (args i).hbase (args i).starbase
local notation3 (prettyPrint := false) "bf(" i ")" => G.transferFrame i (args i).header (args i).dst

variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)}
    {group : Fin ar.header.d → Fin (R+1)} (word : Broadcast ar.n ar.header.d ar.header.cap)
    {frame hdr : ℕ}
local notation3 (prettyPrint := false) "declared" => Prod.mk (Fin.ofNat (ar.n+1) (readCode (ar.n+1) word.1))
  (fun (p : Sym2 (Fin ar.header.d)) (j : Fin (ar.n+1)) => readCode (ar.header.cap+1) (word.2 p j))
local notation3 (prettyPrint := false) "tab" => ar.table frame ((D.directory pp lp).length+ar.header.d.choose 2)
local notation3 (prettyPrint := false) "row" => RouteRecords.combinedRow (D.directory pp lp) owner ar.header.blocks ar.K ar.h declared group

set_option maxRecDepth 5500
set_option maxHeartbeats 1500000

/-- Calibrate the wire layout from the lead team's actual publication. The other
teams use their own returned row writers at their substituted pins. The shared
route is ready on the literal visit RAM and its entire profile trace is retained. -/
theorem joint_calibrated_front
    (epoch : ∀ u, Returns epochPlacement (pub u) (lib(u)) (sub(u)).val.2.1 (sub(u)).val.2.2)
    (published : ∀ u, Returns Packing.Directory.ISA.program (pub u) (lib(u))
      (epoch u).val.2.1 (epoch u).val.2.2)
    (empty : ∀ u, (epoch u).val.1.flatMap TeamRAM.Event.choices=[])
    {atWriter : Fin (R+1) → Bank w × Memory w}
    (scanState : ∀ u, atWriter u=(published u).val.2)
    (W : ∀ u, SignedPrep.HeaderWriterReceipt ar D pp lp owner declared group (loc(u)) (bf(u))
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
    (valid : declarationInRange word) :
    ∃ wire : WireLayout (R+1) r link, wire.header=hdr ∧
      SharedRoutePrepared G pin ext wire D pp lp owner ar.cellBank ar.cellStride tab row pub
        (fun u => (vst(u)).profile.val.2.2)
        (fun u => (args u).dst) (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) digits ∧
      ∀ u, (vst(u)).profile.val.2=((W u).endReg,(W u).out) ∧
        (vst(u)).profile.val.1=(epoch u).val.1++((published u).val.1++(W u).events) := by
  have scan := funext scanState
  subst atWriter
  let label := (W 0).labeling
  obtain ⟨wire,head,prepared⟩ := signed_reference_writer_layout (G:=G) (pin:=pin) (ext:=ext) (header:=hdr)
    (ib:=fun u => (args u).ibase) (hb:=fun u => (args u).hbase) (sb:=fun u => (args u).starbase)
    (dst:=fun u => (args u).dst) (guess:=digits) fit (fun u => (W u).history) base pointers
    (fun u => headers u ▸ sources u) (fun u => ((inputSize u).trans (base u)).le) subRoom
    (fun u => headers u ▸ frameFit u) cell key widths mid raw writer atRaw processors literal teams literalRoom
    headerRoom old fresh gates outputs bitWidth off ell controls profile claims pad word (headers 0 ▸ room) owner group
    valid label.val.2.2 label.property (fun c => by rw [←base 0]; exact (W 0).owners c)
    (by funext j; rw [←base 0]; exact (W 0).groups j) (fun u => (W u).done)
  have same (u : Fin (R+1)) := SignedPrep.return_eq_of_empty (pub u) (lib(u)) (schedule_native ..)
    (SignedPrep.returnedSchedule (epoch u) (published u) (W u).history) (vst(u)).profile
    (SignedPrep.returnedSchedule_empty (epoch u) (published u) (W u).history (empty u))
  have states (u : Fin (R+1)) : (vst(u)).profile.val.2=((W u).endReg,(W u).out) :=
    congrArg (fun p => p.val.2) (same u).symm
  have ram := funext fun u => congrArg Prod.snd (states u)
  refine ⟨wire,head,ram ▸ prepared,fun u => ⟨states u,?_⟩⟩
  exact congrArg (fun p => p.val.1) (same u).symm

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
