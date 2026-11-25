import OAI.Hierarchy.DescentResetFrontMenu
import OAI.Hierarchy.DescentDatedCandidateSheets

namespace OAI
/-! # Public shapes of all four original directed candidate families -/
namespace Hierarchy.DescentDatedAddressBook.CandidateSheets
open DescentCompiler DescentSixParty DescentResetLocalRoster
noncomputable section
set_option quotPrecheck false
variable {n d : ℕ} (S : AtomSchedule) (board : NonlinearExpanders.Graph n d)
    (k tail age D f g cap M : ℕ)

def fromBoard : CandidateSheets :=
  let ht:=GroupStage.depthBound D n f g
  let roots:=rootSlots k (2^n)
  let choices:=roots*(2^n+2^ht)
  let contacts:=2*choices
  let privates:=2*(roots*DescentResetCableSlots.cableCap board ht)
  let shapes:=(DescentDenseHostOrder.roster board k ht).card
  { blocks:=2^k
    hosts:=S.hostSize (age+1)
    groups:=S.groupCount (age+1)
    lanes:=M
    candidates:=publicSlots board ht k cap
    jobs:=2^k*(contacts+privates)
    contacts:=contacts
    privates:=privates
    metaBits:=CandidateFront.endpointWidth D shapes (2^g*cap)
    stemBits:=max (DescentSignedCableCodec.width D cap)
      (max (k+1) (Nat.clog 2 (2*(D+1)+2)))
    selectorBits:=Nat.clog 2 (choices+1)
    shortBits:=Nat.clog 2 (max choices (max (D+2) shapes)+1)
    zeroBits:=1
    haloBits:=Nat.clog 2 (D+2)
    argBits:=Nat.clog 2 (max 1 privates)
    stemDimension:=S.groupWidth k tail age+k,stemFine:=k,stemResidual:=k,
    stemSignedBits:=ResetMiddle.fieldWidth D cap n k ht
    sparseHosts:=S.hostSize age*shapes,donorSlots:=2^k*(2*cap) }

local notation "s" => fromBoard S board k tail age D f g cap M

theorem roster : (s).candidates=2*(2^k*(2*cap))+(1+((s).contacts+(s).privates)) :=rfl
theorem regional_jobs : (s).jobs=(s).blocks*((s).contacts+(s).privates) :=rfl
theorem stem_width : DescentSignedCableCodec.width D cap≤ (s).stemBits ∧
    2^k<2^(s).stemBits ∧ 2*(D+1)+1<2^(s).stemBits :=by
  let t:=Nat.clog 2 (2*(D+1)+2)
  have lo : k+1≤ (s).stemBits:=(Nat.le_max_left (k+1) t).trans (Nat.le_max_right ..)
  have hi : t≤ (s).stemBits:=(Nat.le_max_right (k+1) t).trans (Nat.le_max_right ..)
  exact ⟨Nat.le_max_left ..,(Nat.pow_lt_pow_right (by decide) (show k<(s).stemBits by omega)),
    (show 2*(D+1)+1<2*(D+1)+2 by omega).trans_le
      ((Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) hi))⟩
end
end Hierarchy.DescentDatedAddressBook.CandidateSheets

end OAI
