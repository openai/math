import OAI.Hierarchy.DescentPurchasedRotorStage
import OAI.Hierarchy.DescentPurchasedFinalSiteArguments

namespace OAI
/-! # Fixed spectral rotors produce the original dyadic hosts

The account, circuit, and dates are public at each height. Each accepted binary ballot
recovers its role, arity and signed predecessor from the stored dated prefix and native
role dictionary. The finite stage estimate applies to that same computation. -/
namespace Hierarchy.DescentSixParty.EpochRotor

open DescentCompiler DescentCompiler.TerminalScale DescentResetInvoice SeedNamed Catalyst Filter
open Chronology DescentDatedAddressBook
noncomputable section
set_option quotPrecheck false

variable {F:Type} [Field F] {G:PoweredGadget F} (c:EpochRotor G)
variable (head dates billed last W τ β h m:ℕ) {cp pins:ℕ} (X:Approximation F cp pins)
variable (funds : OriginalWord G c.board c.spec c.rounds c.f c.g c.reset
    (cutRate c.rounds c.f c.g) c.hostDrift c.hostDegree c.branch
    head dates billed last W τ β h (c.hostDrift+1) (quota c.rounds))
variable (low : (2 : ℕ)^h ≤ 2^m) (upper : (2 : ℕ)^m ≤ (2^h)^2) (opens : 10*(X.size+1) ≤ 2^m)
  (geom : c.HostGeometry τ β h (2^m) X)
  (words :
    let depth := Nat.log 2 h/(2*β)
    let stage := stageNumbers G c.rounds depth c.f c.g c.reset (2^m) (tail τ depth)
    let bits := groupBits c.rounds depth stage.hostGain stage.capGain (cutRate c.rounds c.f c.g)
    HostWordRoom G stage bits (tail τ depth) (headGrain G stage bits h) (headChunk G stage) W h)

local notation "rot_" => RotorSpec.ofRates geom.reset
local notation "drift_" => max 1 (max geom.reset.bitsR (c.multiplicity*geom.reset.bitsR))
local notation "fuel_" => (show OriginalWord G geom.reset.board rot_ c.rounds c.f c.g c.reset (cutRate c.rounds c.f c.g)
  drift_ c.hostDegree geom.branch head dates billed last W τ β h (drift_+1) (quota c.rounds)
  from by simpa only [geom.board, geom.spec, geom.history, hostDrift] using funds)
local notation "fits_" => geom.fits (W*h) (by have hw:=words.wide;omega)

open Lean Meta Elab Term in
/-- The receipt fixes the 42 funded inputs to the site theorem. Its three host
parameters specialize that theorem to the observation required by the constructor. -/
local elab "fixedSiteReceipt% " words:term:arg dates:term:arg scalar:term:arg : term <= target => do
  let some receipt ← delta? (← instantiateMVars target).consumeMData (· == ``StageReceipts)
    | throwError "Expected this rotor's StageReceipts"
  unless receipt.isAppOfArity ``PurchasedStageReceipts 42 do throwError "Expected 42 funded site inputs"
  let fixed := receipt.getAppArgs
  let host ← #[words, dates, scalar].mapM fun arg => withoutErrToSorry <| elabTermAndSynthesize arg none
  let observed := mkAppN (mkConst ``SeedNamed.original_site_words) (fixed ++ host)
  return mkAppN (mkConst ``PurchasedStageReceipts.mk) (fixed.push observed)

/-- The fund's actual initial and dated programs supply the three recorded physical
values for every reached primitive. -/
theorem purchased_stage_receipts
    (terminal:TerminalRoomAt G c.spec c.rounds c.f c.g c.reset c.hostDrift W τ β h (2^m))
    (resources:StageDateResources G c.spec c.rounds c.f c.g c.reset c.hostDrift c.hostDegree
      c.nodesLog c.degree τ β h (2^m) (W*h)) :
    c.StageReceipts head dates billed last W τ β h m X funds low upper opens geom words :=by
  have adjusted : TerminalRoomAt G rot_ c.rounds c.f c.g c.reset drift_ W τ β h (2^m) := by
    simpa only [geom.spec, geom.bits, hostDrift] using terminal
  have actualDates : StageDateResources G rot_ c.rounds c.f c.g c.reset drift_ c.hostDegree
      c.nodesLog c.degree τ β h (2^m) (W*h) := by
    simpa only [geom.spec, geom.bits, hostDrift] using resources
  exact fixedSiteReceipt% words actualDates adjusted.arguments

/-- Every chosen fixed rotor produces the required true hosts at every sufficiently
large word ratio and tuning, with the same cost for all circuits at each tuning. -/
theorem produces_original_hosts : c.ProducesHosts c.hostDrift c.hostDegree :=by
  apply c.produces_of_original_reads
  intro head dates billed last W τ β h m cp pins X funds low upper opens geom terminal _purchase resources
  dsimp only
  intro words
  exact c.purchased_stage_receipts head dates billed last W τ β h m X funds low upper opens geom words
    terminal resources

end
end Hierarchy.DescentSixParty.EpochRotor

end OAI
