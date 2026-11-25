import OAI.Hierarchy.DescentResetEvidenceScale
import OAI.Hierarchy.DescentResetReceivedSourcePrice
import OAI.Hierarchy.DescentScalarGrowth

namespace OAI
/-! A single polynomial in the original root control bounds both candidate-evidence
coefficients. Its coefficients depend only on the fixed rotor, halo depth and degree. -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentCompiler DescentSixParty DescentDenseHostOrder DescentResetGates DescentResetPeerUnionRAM
open DescentResetStemPackedIssue DescentScalarGrowth
noncomputable section
variable {n d : ℕ} (S : AtomSchedule) (board : NonlinearExpanders.Graph n d)
    (k tail age degree f g receiverBatch nextBatch field metaBits C packet : ℕ) (calendar : List ℕ)
local notation "v" => setupFront S board k tail age degree f g receiverBatch nextBatch field metaBits C packet calendar
local notation "cap" => List.prod (List.take age calendar)*256
local notation "height" => GroupStage.depthBound degree n f g

def rosterFactor (n d ht : ℕ) := 2*((2^n+1)+((2*d+4)*2^n+(2^n+1)*2^(ht+1)))

def publicEvidenceBound (n ht wires u : ℕ) :=
  let Y:=2^n
  let roots:=2*u+(2*u)*(Y+1)
  Axes.rows (2*(u*(2*u))) (2*(roots*(Y+2^ht))) (2*(roots*wires))

def evidenceCeiling (n d D ht wires u : ℕ) :=
  let shapes:=rosterFactor n d ht*(2*u)
  let work:=sourceLimit shapes (500+23*u+64)
  evidenceFactor D (2*(u*(2*u))) shapes wires work+
    peerFactor D shapes (publicEvidenceBound n ht wires u) work

theorem evidence_coefficient (dimension u : ℕ) (cells : 2^k ≤ u) (ports : cap ≤ u)
    (dim : dimension ≤ u) :
    (v).evidenceTrafficFactor (sourceLimit (v).peer.shapes (500+23*dimension+64)) ≤
      evidenceCeiling n d degree height (DescentResetCableSlots.cableCap board height) u := by
  let wires:=DescentResetCableSlots.cableCap board height
  have next:2^(k+1) ≤ 2*u:=by rw [pow_succ];omega
  have shapes: (roster board k height).card ≤ rosterFactor n d height*(2*u) :=
    (roster_bound board k height).trans (Nat.mul_le_mul_left _ next)
  have count:ClosedReset.Window.publicEvidenceRows board height k cap ≤ publicEvidenceBound n height wires u := by
    unfold ClosedReset.Window.publicEvidenceRows DescentResetLocalRoster.rootSlots publicEvidenceBound Axes.rows
    dsimp only
    gcongr
  have work:sourceLimit (roster board k height).card (500+23*dimension+64) ≤
      sourceLimit (rosterFactor n d height*(2*u)) (500+23*u+64) := by unfold sourceLimit;gcongr
  change evidenceFactor degree (2*(2^k*(2*cap))) (roster board k height).card wires _+
    peerFactor degree (roster board k height).card (ClosedReset.Window.publicEvidenceRows board height k cap) _ ≤ _
  dsimp only [evidenceCeiling,evidenceFactor,peerFactor,evidenceCost,peerCost,Program.sortWork,Candidates.count]
  gcongr <;> exact work

attribute [local fun_prop] DescentScalarGrowth.Polynomial poly_const poly_var poly_add poly_mul

theorem evidence_polynomial (n d D ht wires : ℕ) : Polynomial (evidenceCeiling n d D ht wires) := by
  change Polynomial (fun x=>evidenceCeiling n d D ht wires x)
  unfold evidenceCeiling evidenceFactor peerFactor evidenceCost peerCost Program.sortWork Candidates.count
  unfold publicEvidenceBound Axes.rows sourceLimit
  dsimp only
  simp only [pow_succ,pow_zero,Nat.one_mul]
  fun_prop

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
