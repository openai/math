import OAI.Hierarchy.DescentPhysicalResetBooks
import OAI.Hierarchy.DescentRankPortPrefixRoom
import OAI.Hierarchy.DescentResetCandidatePair

namespace OAI
/-! # Feed the attained candidate and original-number sheets to the ranked reset return -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentPackedColony DescentSIMDLookup DescentResetFieldAssembler DescentResetCandidatePair
open ProtocolRAM ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable (v : ResetOutput)
local notation "A" => v.receiver

structure Sectors where
  stems : ℕ
  contacts : ℕ
  privates : ℕ
  pageBits : ℕ
  count : (A).candidates=CandidateSheet.size stems contacts privates
  ports : Ports 4
  before : ℕ→ℕ→Bool
  sourceSlot : Fin (A).candidates→ℕ→ℕ
  header : Inputs (A).blocks stems contacts privates
  original : Inputs (A).blocks stems contacts privates

variable (q : v.Sectors) (start : ℕ)
local notation "X" => (A).blocks
local notation "K" => CandidateSheet.size q.stems q.contacts q.privates
local notation "B" => q.pageBits
def linkedRankInputs : v.RankInputs where
  ports := q.ports
  before := q.before
  sourceSlot := q.sourceSlot
  header x j := .lookup (CandidateSheet.output start B x (j.cast q.count)) .row
  original x j := .lookup (CandidateSheet.output (originalBase start X K B) B x (j.cast q.count)) .row

variable (s : v.OperandInputs) (base degree : ℕ)
local notation "q₀" => v.linkedRankInputs q start
local notation "L" => v.rankBook q₀ base
local notation "r₀" => v.renderFromRanks q₀ base
local notation "stop₀" => DescentResetCandidatePair.endAddress start X K B
variable (bank : v.setup.Sources) (laws : v.setup.Laws)

def sheetsStart := v.sheets.originalEnd (v.remap base).endAddress

theorem sheets_boundary
    (blocks : v.sheets.blocks=(A).blocks) (counted : v.sheets.candidates=(A).candidates)
    (bits : q.pageBits=Nat.clog 2 v.sheets.rows) :
    DescentResetCandidatePair.endAddress (v.sheetsStart base) X K B=v.candidateEnd base := by
  unfold candidateEnd CandidateSheets.endAddress sheetsStart
  rw [blocks,counted,q.count,bits]

def sheetsReturn (w : ℕ) :=
  (DescentResetCandidatePair.program start B (A).hosts (A).groups (A).lanes w q.header q.original).seq
    (v.retainedReturn q₀ s base degree bank laws w)
def sheetsTime (w : ℕ) :=
  DescentResetCandidatePair.time start B (A).hosts (A).groups (A).lanes q.header q.original+v.retainedTime q₀ s base degree bank laws w
def sheetsMemory {w : ℕ} (m : Memory w) :=
  v.retainedMemory q₀ s base degree bank laws (DescentResetCandidatePair.memory start B (A).hosts (A).groups (A).lanes q.header q.original m)

theorem previous_from_shelves {w : ℕ} (matched : stop₀=v.candidateEnd base)
    (space : v.RankPortRoom base w) (hosts : (A).hosts=v.sheets.hosts)
    (groups : (A).groups=v.sheets.groups) (lanes : (A).lanes=v.sheets.lanes) : (L).Previous w :=by
  let H:=v.sheets.hosts
  let G:=v.sheets.groups
  let M:=v.sheets.lanes
  let head:=v.candidateEnd base
  let top:=v.rankPortEnd base
  let start₀:=DescentRankPortRoster.roof head H
  let rank:=DescentRankPortRoster.bank head H
  obtain ⟨ids,ofs,chunk,_⟩:=DescentScalarHaloPortROM.statics H G M 4 start₀ top rank
    (Nat.le_refl _) space.limit
  have after:=v.rankPort_after base
  have width:=after.trans_lt space.limit
  have rf:=DescentRankPortRoster.bank_fits space.roster
  have room:=DescentRankPortRoster.bank_size head H
  have earlier:=matched.le.trans after
  have le : originalBase start X K B≤ stop₀:=Nat.le_add_right ..
  refine ⟨?_,?_,fun i=>(ids i).1,?_,?_,?_,ofs.1,?_,chunk.1,?_⟩
  · intro x j
    have old:=bank_room (s:=q.stems) (c:=q.contacts) (p:=q.privates) start B x (j.cast q.count) (le.trans_lt (matched.symm ▸ width))
    exact ⟨⟨old.1,old.2.1,old.2.2.trans (le.trans earlier)⟩,trivial⟩
  · intro x j
    have old:=bank_room (s:=q.stems) (c:=q.contacts) (p:=q.privates) (originalBase start X K B) B x (j.cast q.count) (matched.symm ▸ width)
    exact ⟨⟨old.1,old.2.1,old.2.2.trans earlier⟩,trivial⟩
  · intro i
    simp only [rankBook,hosts,groups,lanes]
    exact (ids i).2
  · have span : start₀≤top:=by change start₀≤ start₀+_+_;omega
    exact ⟨rf.1,rf.2.1,rf.2.2.trans span⟩
  · simp only [rankBook,hosts]
    rw [Nat.mul_comm _ 4]
    exact room
  · simp only [rankBook,hosts]
    exact ofs.2
  · simp only [rankBook,hosts,groups,lanes]
    exact chunk.2

theorem sheets_any {w : ℕ} (m : Memory w) (matched : stop₀=v.candidateEnd base)
    (room : v.finalEnd base<2^w) (fitH : ∀x j,(q.header x j).Fits w start)
    (fitO : ∀x j,(q.original x j).Fits w start) (r : (A).hosts*chunks (A).groups (A).lanes≤2^B)
    (width : (A).signedBits=v.assemblerBits) (nodes : s.nodes=v.nodes) (slots : s.slots=v.argumentSlots)
    (portInputs : v.RankPortRoom base w) (prev : (L).Previous w) (controls : v.ControlRoom base bank w) (placed : v.setup.Ready bank w (v.operandFloor base)) («fields» : v.OperandEarly s r₀ w base) :
    (v.sheetsReturn q start s base degree bank laws w).Exec m (v.sheetsMemory q start s base degree bank laws m) (v.sheetsTime q start s base degree bank laws w) ∧
    (∀i,i<start ∨ v.finalEnd base≤ i → v.sheetsMemory q start s base degree bank laws m i=m i) ∧
    CheapCode (v.sheetsReturn q start s base degree bank laws w) := by
  have lo:start≤v.candidateEnd base:=by rw [←matched]; exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have rk:=(L).ordered
  have bound:v.candidateEnd base≤v.finalEnd base:=(v.rankPort_after base).trans <| (((rk.1.trans rk.2.1).trans rk.2.2.1).trans rk.2.2.2).trans
    ((v.earlier base).2.2.trans (v.final_ge base))
  have hs:=DescentResetCandidatePair.any start B (A).hosts (A).groups (A).lanes q.header q.original m fitH fitO r
    (by simpa only [matched] using bound.trans_lt room)
  let after:=DescentResetCandidatePair.memory start B (A).hosts (A).groups (A).lanes q.header q.original m
  have carry:=v.retained_any q₀ s base degree bank laws after width nodes slots portInputs prev controls placed «fields» room
  refine ⟨?_,?_,cheap_seq hs.2.2 carry.2.2⟩
  · exact Procedure.Exec.then (@hs.1) (@carry.1)
  rintro i (small|big)
  · exact (carry.2.1 i (.inl (small.trans_le lo))).trans (hs.2.1 i (.inl small))
  · exact (carry.2.1 i (.inr big)).trans (hs.2.1 i (.inr (by simpa only [matched] using bound.trans big)))

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
