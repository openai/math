import OAI.Hierarchy.DescentResetTrunkOperandCore
import OAI.Hierarchy.DescentResetTrunkGathered
import OAI.Hierarchy.DescentResetTrunkStemTables
import OAI.Hierarchy.DescentPhysicalTrunkHeader

namespace OAI
/-! # The dated trunk operand uses only the public dimensions and the original memory -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSIMDLookup ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "L" => 2^(S.groupWidth k tail i+k-B.terminals.commonDepth)
local notation "cap₁" => input.placement.cap
local notation "half₁" => L*(2*cap₁)

theorem trunk_incoming_address (rows out : ℕ) (x : Fin (2^k)) (j : Fin half₁) :
    incomingBank B rows out x j=DescentResetTrunkOperand.batch half₁ rows out x.val j.val:=by
  have addr : (DescentResetStemPackedIssue.ordinal L cap₁ (true,finProdFinEquiv.symm j)).val=j.val+half₁:=by
    change (finProdFinEquiv (finTwoEquiv.symm true,finProdFinEquiv (finProdFinEquiv.symm j))).val=_
    rw [Equiv.apply_symm_apply]
    change j.val+half₁*1=_
    rw [Nat.mul_one]
  have location : (finProdFinEquiv (x,DescentResetStemPackedIssue.ordinal L cap₁ (true,finProdFinEquiv.symm j))).val=
      j.val+half₁+2*half₁*x.val:=by
    change (DescentResetStemPackedIssue.ordinal L cap₁ (true,finProdFinEquiv.symm j)).val+2*half₁*x.val=_
    rw [addr]
  exact congrArg (fun t : ℕ=>(⟨out+t*rows,Nat.clog 2 rows⟩:Bank)) location

theorem trunk_operand_eq (H G M b base rowBase out scalar hdr : ℕ) (x : Fin (2^k)) :
    DescentResetTrunkIssue.issue base b M (DescentResetStemHeaders.body H G M (b*7) scalar hdr 0)
      (fun j : Fin half₁=>DescentResetTrunkGather.issue (H*chunks G M) rowBase (incomingBank B (H*chunks G M) out x j))=
      DescentResetTrunkOperand.issue H G M b half₁ base rowBase out scalar hdr x.val:=by
  unfold DescentResetTrunkOperand.issue
  apply congrArg (DescentResetTrunkIssue.issue base b M _)
  funext j
  rw [trunk_incoming_address]

theorem trunk_half : half₁=2^k*(2*cap₁):=by
  have same:=B.commonDepth
  rw [show S.groupWidth k tail i+k-B.terminals.commonDepth=k from by omega]
end
end Hierarchy.DescentSixParty.ClosedReset.Window

namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSIMDLookup
noncomputable section
variable (v : CandidateFront)
def trunkOperand (floor x : ℕ) := DescentResetTrunkOperand.issue v.newHosts v.peer.groups v.peer.lanes v.metaBits
  (v.signedQueries/2) (v.gathered floor) (DescentResetTrunkCompactGather.rows (v.mixed floor) v.newHosts v.peer.groups v.peer.lanes)
  (v.stemOutput floor) (v.peer.endAddress (v.peers floor)) (v.trunkHeader floor) x

theorem trunk_operand_work (floor x : ℕ) : (v.trunkOperand floor x).work≤37+28*(v.signedQueries/2) :=
  DescentResetTrunkOperand.price ..
end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
