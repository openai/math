import OAI.Hierarchy.DescentPhysicalResetDateOperands

namespace OAI
/-! # The exact control-register memory inside the reset's fixed operand date -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSixParty DescentSixParty.Chronology DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (v : ResetOutput) (u : v.RankInputs) (base : ℕ)
local notation "L" => v.rankBook u base

include u in
theorem control_cuts : v.candidateEnd base ≤ v.controlFloor base ∧
    v.controlFloor base ≤ v.operandFloor base ∧ v.operandFloor base ≤ v.scalarEnd base := by
  obtain ⟨a,b,c,d⟩:=(L).ordered
  have rank : v.rankPortEnd base ≤ v.rankEnd base:=((a.trans b).trans c).trans d
  have mid : v.rankEnd base ≤ v.controlFloor base:=by
    change v.rankEnd base ≤ DescentNextSignedWindow.Native.All.endAddress (v.fieldsEnd base) _ _ _ _ _ _
    unfold fieldsEnd DescentResetFieldAssembler.endAddress DescentNextSignedWindow.Native.All.endAddress
    omega
  have first : v.controlFloor base ≤ v.operandFloor base:=by
    change v.controlFloor base ≤ v.controlRegisters.endAddress (v.controlFloor base)
    rw [v.controlRegisters.translated]
    exact Nat.le_add_right ..
  have last : v.operandFloor base ≤ v.operandStart base:=by
    apply le_trans _ (v.keep_before base)
    change v.operandFloor base ≤ v.setup.endAddress (v.operandFloor base)
    rw [v.setup.affine]
    exact Nat.le_add_right ..
  obtain ⟨s,t⟩:=v.operand_order base
  exact ⟨(v.rankPort_after base).trans (rank.trans mid),first,last.trans (s.trans t)⟩

def controlInput (degree : ℕ) {w : ℕ} (m : Memory w) : Memory w :=
  v.renderMemory (v.renderFromRanks u base) base degree ((L).memory ((v.rankPortPhase base w).image m))

/-- The six-birth and node-operand suffix leaves the inputs to every control
lookup in place after the final node book has been written. -/
theorem after_control_words {w : ℕ} (s : v.OperandInputs) (degree : ℕ)
    (bank : v.setup.Sources) (laws : v.setup.Laws) (m : Memory w)
    (nodes : s.nodes=v.nodes) (slots : s.slots=v.argumentSlots)
    (placed : v.setup.Ready bank w (v.operandFloor base))
    (issued : v.OperandEarly s (v.renderFromRanks u base) w base) (room : v.finalEnd base < 2^w) :
    ∀z,z < v.operandFloor base → v.retainedMemory u s base degree bank laws m z=
      (v.controlPhase base bank w).image (v.controlInput u base degree m) z := by
  have widths : v.receiver.fields=v.nodeNames*v.nodes:=by simpa only [nodes,slots,nodeNames] using s.channels
  have input : v.operandDictionaryEnd base+(v.nodeNames*v.nodes)*DescentResetNodeBooks.rows v.receiver.hosts
      v.receiver.groups v.receiver.lanes ≤ v.scalarEnd base:=by
    change v.operandDictionaryEnd base+_ ≤ v.operandDictionaryEnd base+v.receiver.fields*_
    rw [widths]; rfl
  have after:=DescentResetNodeBooks.any (v.scalarEnd base) (v.operandDictionaryEnd base) v.nodeNames v.nodes
    v.receiver.hosts v.receiver.groups v.nodeBits v.receiver.lanes (v.rankedMemory u s base degree bank laws m) input room
  have keep:=v.wholeOperand_any s (v.renderFromRanks u base) base
    ((v.controlPhase base bank w).image (v.controlInput u base degree m)) bank laws placed issued
    ((v.final_ge base).trans_lt room)
  intro z hz
  exact (after.2 z (.inl (hz.trans_le (v.control_cuts u base).2.2))).trans (keep.2.1 z (.inl hz))

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty DescentSixParty.Chronology DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
set_option quotPrecheck false
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "q" => u.sectors
local notation "first" => (v).sheetsStart b
local notation "ranks" => (v).linkedRankInputs q first
local notation "actEnd" => (v).actorEnd b
local notation "head_" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "time_" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation "op" => (v).actor.actorBody u.actor ((v).middle.stop b) w
local notation "clock_" => (v).actor.actorTicks u.actor ((v).middle.stop b) w

def rankedInput (ok : u.Ready) (actorMem : Memory w) :=
  DescentResetCandidatePair.memory first (q).pageBits (v).receiver.hosts (v).receiver.groups
    (v).receiver.lanes (q).header (q).original (u.sheetsEntry ok actorMem)

def beforeControl (ok : u.Ready) (actorMem : Memory w) :=
  (v).controlInput ranks b u.degree (u.rankedInput ok actorMem)

/-- The final output and the embedded control scan agree throughout the control
shelves. At the input of that scan the original actor directory is still readable. -/
theorem control_frames (ok : u.Ready) (m actorMem : Memory w)
    (ran : ((head_).seq op).Exec m actorMem (time_+clock_)) (cheap : CheapCode ((head_).seq op)) :
    (∀z,z < (v).operandFloor b → u.sheetsResult ok actorMem z=
      ((v).controlPhase b u.bank w).image (u.beforeControl ok actorMem) z) ∧
    ∀z,z < actEnd → u.beforeControl ok actorMem z=actorMem z := by
  have spans:=(v).control_cuts ranks b
  have before : first ≤ (v).candidateEnd b:=by
    rw [←ok.matched]
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have length : actEnd ≤ first:=by
    obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=ok.ordered
    omega
  have roof := (spans.2.2.trans ((v).final_ge b)).trans_lt ok.full
  have scan:=(v).controlRegisters.any ((v).controlFloor b) ((v).actor.scene ((v).middle.stop b)) u.bank.count
    u.bank.inverse (u.beforeControl ok actorMem) ok.controls roof
  have tail:=(v).after_control_words ranks b u.operand u.degree u.bank u.laws (u.rankedInput ok actorMem) ok.nodes ok.slots ok.placed ok.fields ok.full
  have total:=(u.run_to_sheets_from_actors ok m actorMem ran cheap).2.2
  refine ⟨tail,?_⟩
  intro z hz
  have low:=hz.trans_le (length.trans (before.trans spans.1))
  exact ((scan.2 z (.inl low)).symm.trans (tail z (low.trans_le spans.2.1)).symm).trans (total z (.inl hz))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
