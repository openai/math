import OAI.Hierarchy.DescentDatedCanonicalFront
import OAI.Hierarchy.DescentPhysicalResetSceneInputs

namespace OAI
/-! # All fixed reset front expressions from the original physical source bank addresses -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSixParty DescentCompiler DescentDenseHostOrder DescentSIMDLookup DescentPackedColony
open DescentResetStemPackedIssue DescentFallbackPeriod DescentResetLocalRoster ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {n h : ℕ} (S : AtomSchedule) (board : NonlinearExpanders.Graph n h)
    (k tail age degree f g receiverBatch nextBatch rootField metaBits C packet : ℕ) (calendar : List ℕ)
local notation "A" => setupFront S board k tail age degree f g receiverBatch nextBatch rootField metaBits C packet calendar
local notation "evidence₀" => setupEvidence S board k tail age degree f g receiverBatch nextBatch rootField metaBits C packet calendar
local notation "L" => 2^k

/-- These are the preceding printed roots, signed window, published roster, counts and flags. -/
structure EarlierBanks (D k cap n : ℕ) where
  ports : Ports D
  window : Projected.Column (2^k) cap→Bank
  roots : Bool→Root k (2^n)→Bank
  actorStarts : Bank
  actorData : Bank
  oldRoster : Bank
  oldHub : Bank
  donor : DescentContactSenderDate.Prior D (2^k) cap n k

local notation "cap" => (calendar.take age).prod*256
variable (floor : ℕ) (early : EarlierBanks degree k ((calendar.take age).prod*256) n)
def calendarOriginals : (A).Originals floor where
  evidence:=evidence₀ early.ports early.window
  shape:=⟨rfl,rfl,le_rfl,rfl,rfl⟩
  pages:=early.roots
  actorStarts:=early.actorStarts
  actorData:=early.actorData
  oldRoster:=early.oldRoster
  oldHub:=early.oldHub
  sameBoard:=rfl
  originalDonors:=early.donor
  sameDonors:=rfl
  signs:=side L cap
  operands:=operands early.ports early.window (S.hostSize age)
  queries:=rfl
  field:=rfl

theorem original_code :
    let a:=calendarOriginals S board k tail age degree f g receiverBatch nextBatch rootField metaBits C packet
      calendar floor early
    a.evidence.source=a.operands ∧ a.evidence.sides=a.signs := ⟨rfl,rfl⟩

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
