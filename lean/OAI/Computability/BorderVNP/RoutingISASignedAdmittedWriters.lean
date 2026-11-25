import OAI.Computability.BorderVNP.RoutingISASignedPrepRange

/-! # The complete native group writer for an admitted signed broadcast -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing Packing TeamContraction CubeHeaderInstall VPVNP.BurstRAM
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.Tally LocalRow JointHeader

variable {w R X : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w}
  {ar : CubeArena.Layout} {D : Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {pins : Pins.Layout}
  {slotted : Memory w} {base : ℕ} {I : Type*} [Fintype I] {cell : I → Fin ar.cells}
  {id : I ↪ ℕ} {widths : I → ℕ} (P : SlottedWriter ar D pp lp pins pub slotted base cell id widths)
  (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs width off ell controls : ℕ)
  (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (word : Broadcast ar.n ar.header.d ar.header.cap)

local notation3 (prettyPrint := false) "published" => Directory.ISA.publish slotted (pub 0).val base (D.directory pp lp)
local notation3 (prettyPrint := false) "ix" => readCode (ar.n+1) word.1
local notation3 (prettyPrint := false) "axis" => Fin.ofNat (ar.n+1) ix
local notation3 (prettyPrint := false) "dec" => Prod.mk axis (fun p j => readCode (ar.header.cap+1) (word.2 p j))
local notation3 (prettyPrint := false) "wl" => weightLayout ar (pub 0).val ix
local notation3 (prettyPrint := false) "tl" => teamLayout ar R
local notation3 (prettyPrint := false) "initial" m => powerHeaderImage ar f.dst (readings m)
local notation3 (prettyPrint := false) "labelTicks" => labelPrefixCost (pub 0).val (readings published)
local notation3 (prettyPrint := false) "ticks" => ((labelTicks+publicBootCost ar f.dst)+(minimumCost ar.n+
  (GroupWeights.ticks wl+TeamNative.assignmentTicks tl+(TeamBudget.setup.slots+(R+1)*(TeamBudget.row.slots+1)+1))))+
  directoryTicks ar (pub 0).val
local notation3 (prettyPrint := false) "owners" m => fun j : Fin ar.header.d => TeamNative.owner R ((wl).weight (initial m)) j.val

include P in
/-- A declaration passing the true label and histogram guards yields a physical
eleven-stage return with its writer receipts and measured charge. Its first
label memory is available for comparison across different exterior assignments. -/
theorem admitted_writers
    (room : PinnedRawInput (ar:=ar) (D:=D) (pp:=pp) (lp:=lp) (pub:=pub) (slotted:=slotted) (base:=base)
      f old fresh gates outputs width off ell controls G claims pad word R X)
    (range : declarationInRange word) (minimum : declaredMinimum word)
    (admitted : ∀ {es z m}, Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg
      published es z m → capacities wl tl X (initial m)) :
    ∃ es z selected, Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg published es z selected ∧
      traceCost es ≤ labelTicks ∧ (∀ j<ar.publicBase, readings selected j=readings published j) ∧
      TestRun pub mac (.block (beforeWriters ar.n (selectorWidth ar.n ar.K ar.h))) reg published
        ticks (declarationInRange word ∧ declaredMinimum word ∧ capacities wl tl X (initial selected))
        (fun h => WriterSources ar (pub 0).val controls f.team R dec (owners selected) (readings pub)
          (initial selected) (readings published) h.mem w) ∧
      ∃ events endReg out, ∃ H : WriterHistory ar.n (selectorWidth ar.n ar.K ar.h) pub mac reg published events endReg out,
        ReturnedWriters ar D pp lp (ar.receivingOwner (pub 0).val axis R (initial selected)) dec (owners selected)
          pins H ∧ traceCost events ≤ ticks+writerTicks (D.directory pp lp).length ar.header.d := by
  obtain ⟨es,z,selected,run,cost,low,source,forward⟩ :=
    P.raw_schedule f old fresh gates outputs width off ell controls mac reg G claims pad word R X
      room.boot room.geometry room.frameSpace room.copied room.alphabet room.blocks room.bank room.arena
      room.labels room.cells room.teamCount room.teamArena room.budget room.million room.scaled room.controlLow
      room.pointers room.processors room.payload room.fields room.rawSpace room.records
  exact ⟨es,z,selected,run,cost,low,source,forward.1 ⟨range,minimum,admitted run⟩⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
