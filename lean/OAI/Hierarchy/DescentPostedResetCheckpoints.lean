import OAI.Hierarchy.DescentRegisteredResetStep
import OAI.Hierarchy.DescentPhysicalDateHistory

namespace OAI
/-! # Checkpoints of the actual posted reset on the common native date history -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ) (prev : DatePorts) (floor w : ℕ)
local notation "cap" => ((capCalendar G.b S.rounds gain S.height).take age).prod*256
local notation "oldExp" => NativePitch.resetCut S k tail p f h age
local notation "nextM" => NativePitch.incoming S k tail p f h ordinary (age+1)
local notation "token" => DescentPrimitivePalette.printedBits G s Z op
local notation "cut" => receiverCut G S board k tail age p f gain drift degree h oldExp nextM op.C op.w
  prev.operandLanes prev.roleLanes token prev.venue
local notation "fits" => scheduled_cut_origin G S board k tail age p f gain drift degree h ordinary op s Z
  prev.operandLanes prev.roleLanes prev.venue
local notation "priorFits" => preceding_cut S k tail p f h age
local notation "innerFloor" => prev.priorStart k floor
local notation "earlier" => (prev.afterPad k floor).archive
local notation "publisher" => priorArchivePhase G S board k tail age p f gain drift degree h ordinary op s Z prev floor w
local notation "layout" => previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z prev floor
local notation "a" => (scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z prev floor).inner
local notation "room" => ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
  prev.operandLanes prev.roleLanes prev.venue prev.io innerFloor w earlier
variable (capacity : prev.venue.cap=cap) (space : room)

local notation "inputs" => resetInputs G S board k tail age p f gain drift degree h ordinary op s Z prev floor w space
local notation "issued" => resetDate G S board k tail age p f gain drift degree h ordinary op s Z prev floor w capacity space
local notation "L₀" => (a).ingress
local notation "phase" => (L₀).phase innerFloor w prev.io.hubs (fun x=>prev.io.atoms x.val)
  (fun j=>prev.io.wire j.1.val j.2.val)

/-- The operand and output programs use the same public previous register bank. -/
def resetFinalInputs : (inputs).FinalInputs :=
  FinalInputs.fromArchive G S board k tail age p f gain drift degree h cut oldExp (2^cut) nextM op.C op.w
    prev.operandLanes prev.roleLanes token prev.venue prev.io innerFloor w fits fits priorFits (earlier).count
    space.prepared space.scene earlier s Z op capacity

local notation "finish" => resetFinalInputs G S board k tail age p f gain drift degree h ordinary op s Z prev floor w capacity space

/-- The signed ingress, scan up to the operands, full reset and public history
all agree on the same three memories, including their padding. -/
theorem reset_checkpoints (calendar : ℕ→DateCode w) (boot : Memory w)
    (printed : calendar age=issued) (ready : (inputs).Ready) (fitted : (finish).Room)
    (src : ∀j,(prev.archive.prior layout j).Fits w floor)
    (roles : ∀j:Fin (prev.resetPad k).blocks,(prev.archive.roles.bank j.val).Fits w floor)
    (hubFit : prev.io.hubs.Fits w floor)
    (atomFit : ∀x : Fin (2^(L₀).k),(prev.io.atoms x.val).Fits w floor)
    (wireFit : ∀x : (L₀).signed.Slot,(prev.io.wire x.1.val x.2.val).Fits w floor)
    (spaceAt : (a).stageStart innerFloor < 2^w) :
    let before:=DateCode.history calendar boot age
    let paidMem:=(publisher).image before
    let startMem:=(phase).image paidMem
    (publisher).Runs before ∧ (phase).Runs paidMem ∧ ∃mid,(inputs).throughOperandDate.Runs startMem mid ∧
      (PhysicalReset.date finish).Runs startMem (DateCode.history calendar boot (age+1)) ∧
      (issued).Runs before (DateCode.history calendar boot (age+1)) :=by
  let before:=DateCode.history calendar boot age
  let paidMem:=(publisher).image before
  let startMem:=(phase).image paidMem
  have low:floor≤ innerFloor:=(prev.pad_order k floor).1.trans (prev.pad_order k floor).2
  have padRoom:innerFloor<2^w:=((L₀).after innerFloor).trans_lt spaceAt
  have pad:=prev.full_pad_any k floor (prev.archive.prior layout) (fun x=>prev.archive.roles.bank x.val) before src roles padRoom
  have lift {b:Bank} (fit:b.Fits w floor) : b.Fits w innerFloor:=⟨fit.1,fit.2.1,fit.2.2.trans low⟩
  obtain ⟨intake,_⟩:=(L₀).any innerFloor prev.io.hubs _ _ paidMem (lift hubFit) (fun x=>ProtocolRAMGeneratedWrite.fits_mono _ low (atomFit x)) (fun j=>lift (wireFit j)) spaceAt
  obtain ⟨mid,scan,_,_⟩:=(inputs).run_to_operands ready startMem
  obtain ⟨out,runAt,_,_⟩:=PhysicalReset.date_any finish ready fitted startMem
  have whole : (issued).Runs before out:=by
    intro P₀ R₀ K₀ machine
    exact Procedure.Exec.then pad.1 (Procedure.Exec.then intake runAt) machine
  have posted : (calendar age).Runs before out:=printed.symm ▸ whole
  have same : DateCode.history calendar boot (age+1)=out:=(calendar age).nextMemory_eq posted
  exact ⟨pad.1,intake,mid,scan,same.symm ▸ runAt,same.symm ▸ whole⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
