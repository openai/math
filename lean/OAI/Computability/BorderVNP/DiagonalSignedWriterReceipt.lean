import OAI.Computability.BorderVNP.DiagonalSignedHeaderWriterRun
import OAI.Computability.BorderVNP.RoutingISAScheduleClockFinitePrefix

/-! # The physical return attached to a chosen signed header and pin -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing Packing Packing.Directory VPVNP.BurstRAM TeamContraction JointHeader
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.GroupWeights Cube.LabelIndex Cube.MeanChoice Cube.Tally LocalRow
open private loads_congr from OAI.Computability.BorderVNP.CubePhysicalGreedyTally
open scoped Classical

/-- One actual signed-prefix execution, including the measured label pass inside the schedule and the
complete writer at this team's own memory. The owners used by its directory are common on live cells. -/
structure HeaderWriterReceipt (ar : CubeArena.Layout) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    {R w : ℕ} (representative : ℕ → Fin (R+1)) (decl : LengthDeclaration ar.n ar.header.d)
    (group : Fin ar.header.d → Fin (R+1)) (pins : Pins.Layout) (f : BroadcastFrame)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (reg : Bank w) (mem : Memory w) where
  /-- The actual label-index and interval pass before the group scheduler. -/
  labeling : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub mac reg mem
  labelCost : traceCost labeling.val.1 ≤ labelPrefixCost (pub 0).val (readings mem)
  kept : ∀ j < ar.publicBase,readings labeling.val.2.2 j=readings mem j
  groups : ∀ j : Fin ar.header.d,TeamNative.owner R
    ((weightLayout ar (pub 0).val decl.1.val).weight (powerHeaderImage ar f.dst (readings labeling.val.2.2))) j.val=group j
  owners : ∀ c : Fin ar.cells,ar.receivingOwner (pub 0).val decl.1 R
    (powerHeaderImage ar f.dst (readings labeling.val.2.2)) c.val=representative c.val
  /-- The events of the entire native eleven-stage writer. -/
  events : List (TeamRAM.Event w)
  /-- Registers after the last shared-row writer. -/
  endReg : Bank w
  /-- The physical output RAM at that return. -/
  out : Memory w
  /-- The ordered decomposition of these events into the actual writer stages. -/
  history : WriterHistory ar.n (selectorWidth ar.n ar.K ar.h) pub mac reg mem events endReg out
  done : ReturnedWriters ar D pp lp representative decl group pins history
  cost : traceCost events ≤ ScheduleClock.rawScheduleTicks ar (pub 0).val f.dst decl.1.val R (D.directory pp lp).length
    (readings mem)

variable {w R X : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w}
  {ar : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp pp' lp' : ℕ → ℕ × ℕ} {pins : Pins.Layout}
  {slotted : Memory w} {base : ℕ} {I : Type*} [Fintype I] {host : I → Fin ar.cells}
  {id : I ↪ ℕ} {width : I → ℕ} (writer : SlottedWriter ar D pp lp pins pub slotted base host id width)
  (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs bitWidth off ell controls : ℕ)
  (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (word : Broadcast ar.n ar.header.d ar.header.cap)
  (room : PinnedRawInput (ar:=ar) (D:=D) (pp:=pp) (lp:=lp) (pub:=pub) (slotted:=slotted) (base:=base)
    f old fresh gates outputs bitWidth off ell controls G claims pad word R X)
  {dim : ℕ} {P A : Type*} [Fintype A] {bits : P → ℕ}
  (N : Network dim P bits) (cell : N.Site → Fin ar.cells) (recv : A → Fin ar.cells) (size : A → ℕ)
local notation3 (prettyPrint := false) "ram" => ISA.publish slotted (pub 0).val base (D.directory pp lp)
local notation3 (prettyPrint := false) "dir" => LabelIndex.layout (pub 0).val (readings ram)
local notation3 (prettyPrint := false) "ix" => readCode (ar.n+1) word.1
local notation3 (prettyPrint := false) "axis" => Fin.ofNat (ar.n+1) ix
local notation3 (prettyPrint := false) "decl" => Prod.mk axis (fun (p : Sym2 (Fin ar.header.d)) (j : Fin (ar.n+1)) =>
  readCode (ar.header.cap+1) (word.2 p j))
local notation3 (prettyPrint := false) "hd" => (Nat.zero_lt_of_lt room.alphabet : 0 < ar.header.d)
local notation3 (prettyPrint := false) "label" => meanPackedLabel N cell recv size (List.finRange ar.cells) ar.n ar.header.d hd
local notation3 (prettyPrint := false) "wl" => weightLayout ar (pub 0).val ix
local notation3 (prettyPrint := false) "tl" => teamLayout ar R
local notation3 (prettyPrint := false) "input" m => powerHeaderImage ar f.dst (readings m)
local notation3 (prettyPrint := false) "labelTicks" => labelPrefixCost (pub 0).val (readings ram)
local notation3 (prettyPrint := false) "ticks" => ((labelTicks+publicBootCost ar f.dst)+(minimumCost ar.n+
  (GroupWeights.ticks wl+TeamNative.assignmentTicks tl+(TeamBudget.setup.slots+(R+1)*(TeamBudget.row.slots+1)+1))))+
  directoryTicks ar (pub 0).val
local notation3 (prettyPrint := false) "charge" => declarationWeight ar.header.blocks ar.b ar.K ar.h decl label recv size
local notation3 (prettyPrint := false) "group" => fun j : Fin ar.header.d => TeamNative.owner R charge j.val
local notation3 (prettyPrint := false) "owner" => fun c : ℕ => if h : c < ar.cells then group (label ⟨c,h⟩ axis) else 0

set_option maxHeartbeats 1500000 in
/-- Execute the common broadcast on the true directory-published memory and retain the returned writer. -/
noncomputable def geometricHeaderReceipt {edgeOrd : N.CrossingEdge cell ↪ Fin (dir).cableCount}
    {dataOrd : A ↪ Fin (dir).deliveryCount}
    (placed : RowPlacement (networkRows N cell recv size) (fromTables dir (readings ram) room.labels.endpoints)
      (finCongr room.cells.symm) (edgeOrd.sumMap dataOrd))
    (valid : declarationInRange word)
    (allowed : broadcastAllowed R X ar.header.blocks ar.b ar.K ar.h label recv size word)
    (ref : BankPlacement D pp' lp' I host id width) (same : ∀ k,writer.placement.key k=ref.key k)
    (published : Memory w) (after : published=ram) :
    HeaderWriterReceipt ar D pp' lp' owner decl group pins f pub mac reg published := Classical.choice <| by
  subst published
  obtain ⟨ev,lb,selected,run,cost,kept,groups,owners,log,r,mt,W,done,paid⟩ :=
    geometric_header_writers writer f old fresh gates outputs bitWidth off ell controls G claims pad word room
      N cell recv size placed valid allowed ref same
  have ixEq : (axis).val=ix := Nat.mod_eq_of_lt valid.1
  exact ⟨{ labeling := ⟨(ev,lb,selected),run⟩
           labelCost := cost
           kept := kept
           groups := by simpa only [ixEq] using groups
           owners := owners
           events := log
           endReg := r
           out := mt
           history := W
           done := done
           cost := by simpa only [ScheduleClock.rawScheduleTicks,ixEq] using paid }⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
