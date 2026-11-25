import OAI.Hierarchy.DescentResetSheetLookupTariff
import OAI.Hierarchy.DescentPhysicalResetDateTariff

namespace OAI
/-! Word and instruction invoices for the fixed return from the two original sheets through the node books. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentResetFieldAssembler DescentResetCandidatePair DescentResetRankedWindows
open DescentStaticWordColumn DescentSIMDLookup DescentOperandCandidateLookup DescentOrdinaryAtomFieldRAM
open ProtocolRAM ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable (v : ResetOutput)
local notation "A" => v.receiver
variable (q : v.Sectors) (start : ℕ) (s : v.OperandInputs) (base degree : ℕ)
variable (bank : v.setup.Sources) (laws : v.setup.Laws)
local notation "K" => CandidateSheet.size q.stems q.contacts q.privates
local notation "u" => v.linkedRankInputs q start
local notation "L" => v.rankBook u base
local notation "r" => v.renderFromRanks u base
local notation "R" => (A).hosts*chunks (A).groups (A).lanes

def finalWords :=(2*(A).candidates*2)*2^(bits (A).queryBits (A).signedBits (A).lanes)
def pointerBill (query kept : ℕ) :=4+10*v.finalWords+7*(15*(v.finalWords+1))+
  scanBill (A).fields R (visit query kept 7 (Layout.finalWork (A).candidates 7) (A).candidates)

theorem pointer_invoice (w query kept : ℕ) (get : ∀i,(s.query i).work≤query) (ret : ∀i,(s.kept i).work≤kept) :
    v.operandTicks s r base+7*names (v.operandProgram s r base w)≤v.pointerBill query kept:=by
  have «meta» (x j) : ((L).header x j).work≤7:=Nat.le_refl 7
  have prior (x j) : ((L).original x j).work≤7:=Nat.le_refl 7
  have sweep:=scan_bill (v.operandDictionaryEnd base) R R (A).fields w
    (visit query kept 7 (Layout.finalWork (A).candidates 7) (A).candidates) (v.terminalTerm s r base)
    (fun j hj=>v.terminal_work s r base query kept 7 (Layout.finalWork (A).candidates 7) j hj
       get ret «meta» ((L).final_work 7 «meta» prior))
  unfold operandProgram operandTicks terminalPasses ROM.mount pointerBill
  rw [names_seq,names_mount]
  change (4+10*v.finalWords+_)+7*(15*(v.finalWords+1)+_)≤_
  dsimp only
  omega

def portBill :=5000*(v.sheets.hosts+1)+
  116*(DescentScalarHaloPortROM.length v.sheets.hosts v.sheets.groups v.sheets.lanes 4+1)
def rowBill (header raw query kept : ℕ) :=
  scanBill ((A).blocks*K) R header+scanBill ((A).blocks*K) R raw+v.portBill+
    ((L).clockBudget 7+7*(L).textBudget 7)+
    ((L).tailClock (A).capacity 7+7*(L).tailText (A).capacity 7)+
    v.controlRegisters.fee+(4+10*v.keepWords+7*(15*(v.keepWords+1)))+v.pointerBill query kept+
    DescentResetNodeBooks.invoice v.nodeNames v.nodes (A).hosts (A).groups v.nodeBits (A).lanes

theorem sheets_invoice (w header raw query kept : ℕ) (hs : ∀x j,(q.header x j).work≤header)
    (ps : ∀x j,(q.original x j).work≤raw) (get : ∀i,(s.query i).work≤query) (ret : ∀i,(s.kept i).work≤kept)
    (oldLanes : 0<v.controlRegisters.dims.oldLanes) (lanes : 0<v.controlRegisters.dims.lanes)
    (cards : 0<v.controlRegisters.dims.blocks) :
    v.sheetsTime q start s base degree bank laws w+7*names (v.sheetsReturn q start s base degree bank laws w)≤
    v.rowBill q start base header raw query kept+(v.setup.code (v.operandFloor base) w bank laws).time+7*names (v.setup.code (v.operandFloor base) w bank laws).program:=by
  have first:=pair_bill start q.pageBits (A).hosts (A).groups (A).lanes w header raw _ _ hs ps
  have port:=v.rankPort_price base w
  have «meta» (x j) : ((L).header x j).work≤7:=Nat.le_refl 7
  have prev (x j) : ((L).original x j).work≤7:=Nat.le_refl 7
  have rank:=(L).invoice (w:=w) 7 «meta» prev
  have gather:=(L).tail_invoice (w:=w) 7 «meta» prev degree (A).capacity
  change v.renderTicks r base degree≤_ ∧ names (v.renderProgram r base degree w)≤_ at gather
  have control:=v.controlRegisters.billed (v.controlFloor base) (v.actor.scene (v.middle.stop base))
    bank.count bank.inverse w oldLanes lanes cards
  change (v.controlPhase base bank w).ticks+7*names (v.controlPhase base bank w).program≤_ at control
  have cast:=v.keep_names base w
  have elapsed : (v.keepBook base w).time=4+10*v.keepWords:=rfl
  have ptr:=v.pointer_invoice q start s base w query kept get ret
  have node:=DescentResetNodeBooks.billed (v.scalarEnd base) (v.operandDictionaryEnd base)
    v.nodeNames v.nodes (A).hosts (A).groups v.nodeBits (A).lanes w
  simp only [sheetsTime,sheetsReturn,retainedTime,retainedReturn,rankedTime,rankedReturn,
    wholeOperandTicks,wholeOperandProgram,wholeOperands,DescentResetOperandSetup.Code.join,names_seq]
  unfold rowBill portBill
  omega

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
