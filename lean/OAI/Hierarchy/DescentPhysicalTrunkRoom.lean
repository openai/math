import OAI.Hierarchy.DescentResetTrunkOperand

namespace OAI
/-! # Address bounds for the actual trunk query on arbitrary tapes -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentDyadicSpan DescentSIMDLookup DescentResetStemHeaders DescentResetTrunkOperand ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable (v : CandidateFront) (floor : ℕ) {w : ℕ}
local notation "H" => v.newHosts
local notation "G" => v.peer.groups
local notation "M" => v.peer.lanes
local notation "b" => v.metaBits
local notation "n" => H*chunks G M
local notation "half" => v.signedQueries/2
local notation "rowBase" => DescentResetTrunkCompactGather.rows (v.mixed floor) H G M
local notation "headBase" => outputBase H G M (b*7) (v.trunkHeader floor)

theorem trunk_operand_room (x : Fin v.blocks)
    (queries : v.projectionCount=v.signedQueries*(v.peer.oldDegree+2))
    (digits : v.projectionBits=v.stemField) (room : v.trunkEnd floor<2^w) :
    (v.trunkOperand floor x.val).Fits w (v.trunkEnd floor) :=by
  obtain ⟨raw,headEnd,last⟩:=v.trunk_regions_of_format floor queries digits
  have bankEnd : rowBase+span n=v.gathered floor:=rfl
  have low : v.mixed floor≤rowBase:=by
    change _≤v.mixed floor+span H+DescentResetStemKeyReindex.size H H G M
    omega
  have gathered : v.gathered floor≤v.trunkEnd floor:=Nat.le_add_right ..
  have baseRoof : v.gathered floor<2^w:=gathered.trans_lt room
  have afterRows : v.mixed floor≤v.gathered floor:=low.trans ((Nat.le_add_right rowBase (span n)).trans bankEnd.le)
  have header : headBase+n<2^w:=(headEnd.trans afterRows).trans_lt baseRoof
  have head:=DescentResetStemHeaders.body_fits (K:=1) («H»:=H) («G»:=G) («M»:=M) («b»:=b*7)
    (raw:=v.peer.endAddress (v.peers floor)) (base:=v.trunkHeader floor) (by simpa using raw) (by simpa using header) (0:Fin 1)
  apply DescentResetTrunkIssue.issue_fits
  · exact ProtocolRAMGeneratedWrite.fits_mono _ (((Nat.le_add_right headBase n).trans headEnd).trans afterRows) head
  · intro j
    have pitch : 2*half≤v.signedQueries:=by omega
    have atBlock : j.val+half+2*half*x.val≤v.blocks*v.signedQueries:=by
      calc
        _≤2*half+2*half*x.val:=by omega
        _=(x.val+1)*(2*half):=by ring
        _≤v.blocks*v.signedQueries:=Nat.mul_le_mul x.isLt pitch
    have endRow : (batch half n (v.stemOutput floor) x.val j.val).base≤v.mixed floor:=by
      rw [←last]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right n atBlock) _
    have high : span n<2^w:=((Nat.le_add_left (span n) rowBase).trans bankEnd.le).trans_lt baseRoof
    have tab : (DescentResetTrunkGather.table rowBase n).Fits w (v.gathered floor):=⟨span_pos _,high,bankEnd.le⟩
    have old : (batch half n (v.stemOutput floor) x.val j.val).Fits w (v.gathered floor):=
      ⟨span_pos _,high,(Nat.add_le_add_right (endRow.trans low) (span n)).trans bankEnd.le⟩
    exact ⟨⟨tab,trivial⟩,trivial,trivial,old,tab,trivial⟩
  · exact room

theorem trunk_operand_fits (s : v.Scene) (x : Fin v.blocks) (room : v.trunkEnd floor<2^w) :
    (v.trunkOperand floor x.val).Fits w (v.trunkEnd floor) :=
  v.trunk_operand_room floor x s.stems.queries s.stems.digits room

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
