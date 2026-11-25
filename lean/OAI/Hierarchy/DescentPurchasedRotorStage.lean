import OAI.Hierarchy.DescentPurchasedStageInstance
import OAI.Hierarchy.DescentFixedHostOperator

namespace OAI
/-! # The original purchased stage on one fixed spectral rotor -/
namespace Hierarchy.DescentSixParty.EpochRotor

open DescentCompiler DescentCompiler.TerminalScale DescentResetInvoice SeedNamed Catalyst Filter
open Chronology DescentDatedAddressBook
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 16000
set_option maxHeartbeats 3200000
variable {F:Type} [Field F] {G:PoweredGadget F} (c:EpochRotor G)
def hostDrift := max 1 (max c.bits (c.multiplicity*c.bits))
def hostDegree := maximumDegree (c.rounds+1)

variable (head dates billed last W τ β h m:ℕ) {cp pins:ℕ} (X:Approximation F cp pins)
local notation "price_" => originalHostPrice G c.rounds c.f c.g c.reset c.nodesLog c.degree c.multiplicity W τ
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
local notation "sameDrift_" => (geom.history : drift_=c.hostDrift)
local notation "fuel_" => (show OriginalWord G geom.reset.board rot_ c.rounds c.f c.g c.reset (cutRate c.rounds c.f c.g)
  drift_ c.hostDegree geom.branch head dates billed last W τ β h (drift_+1) (quota c.rounds)
  from by simpa only [geom.board, geom.spec, geom.bits, hostDrift] using funds)
local notation "fits_" => geom.fits (W*h) (by have hw:=words.wide;omega)

/-- The remaining three values are read at every reached original paid node. -/
def StageReceipts : Prop :=
  PurchasedStageReceipts (X:=X) (G:=G) (rounds:=c.rounds) (restart:=c.reset) (τ:=τ) (β:=β)
    (siteCount:=(2^m)) (payloadBits:=h) (opened:=opens) (smaller:=upper) (low:=low)
    (dyadic:=⟨m,rfl⟩) (ordinary:=geom.ordinary) (reset:=geom.reset) (branch:=geom.branch)
    (positive:=geom.positive) (room:=geom.room) (shorten:=geom.shorten) (base:=geom.base)
    (width:=geom.width) (age:=geom.age) (wFit:=geom.wFit) (qFit:=geom.qFit) (qh:=geom.qh)
    (sitesPositive:=geom.sitesPositive) (ratio₀:=W) (fit:=fits_) (headRate_:=head)
    (datesRate_:=dates) (codeRate_:=billed) (lastRate_:=last) (slots_:=quota c.rounds) (funding:=fuel_)

theorem returned_of_receipts
    (terminal:TerminalRoomAt G c.spec c.rounds c.f c.g c.reset c.hostDrift W τ β h (2^m))
    (purchase:OriginalPurchaseAt G c.spec c.rounds c.f c.g c.reset c.nodesLog c.degree c.multiplicity
      c.hostDrift c.hostDegree W τ β h)
    (resources:StageDateResources G c.spec c.rounds c.f c.g c.reset c.hostDrift c.hostDegree
      c.nodesLog c.degree τ β h (2^m) (W*h))
    (isa:ISAFromInvoice G c.rounds c.f c.g c.reset τ β W price_ h (2^m) X)
    (reached : c.StageReceipts head dates billed last W τ β h m X funds low upper opens geom words) :
    c.ReturnedHost τ β h (2^m) price_ X :=by
  have adjusted : TerminalRoomAt G rot_ c.rounds c.f c.g c.reset drift_ W τ β h (2^m) := by
    simpa only [geom.spec, geom.bits, hostDrift] using terminal
  have actualDates : StageDateResources G rot_ c.rounds c.f c.g c.reset drift_ c.hostDegree
      c.nodesLog c.degree τ β h (2^m) (W*h) := by
    simpa only [geom.spec, geom.bits, hostDrift] using resources
  have actualPurchase : OriginalPurchaseAt G rot_ c.rounds c.f c.g c.reset c.nodesLog c.degree
      c.multiplicity drift_ c.hostDegree W τ β h := by
    simpa only [geom.spec, geom.bits, hostDrift] using purchase
  apply purchased_stage_instance (X:=X) (G:=G) (rounds:=c.rounds) (restart:=c.reset) (τ:=τ)
    (β:=β) (siteCount:=(2^m)) (payloadBits:=h) (opened:=opens) (smaller:=upper) (low:=low)
    (dyadic:=⟨m,rfl⟩) (ordinary:=geom.ordinary) (reset:=geom.reset) (branch:=geom.branch)
    (positive:=geom.positive) (room:=geom.room) (shorten:=geom.shorten) (base:=geom.base)
    (width:=geom.width) (age:=geom.age) (wFit:=geom.wFit) (qFit:=geom.qFit) (qh:=geom.qh)
    (sitesPositive:=geom.sitesPositive) (ratio₀:=W) (fit:=fits_) (headRate_:=head)
    (datesRate_:=dates) (codeRate_:=billed) (lastRate_:=last) (slots_:=quota c.rounds) (funding:=fuel_)
    (scalarRoom:=adjusted.arguments)
    (dates:=actualDates)
    (purchased:=actualPurchase)
    (words:=words) (isa:=isa) (receipts:=reached)

/-- The public account has fixed rate at each tuning and word ratio. The residual hypothesis
is the native three-field receipt on the selected ballot of this very rotor. -/
theorem produces_of_original_reads
    (readAt:∀head dates billed last W τ β h m:ℕ,∀{cp pins:ℕ} (X:Approximation F cp pins),
      ∀funds:OriginalWord G c.board c.spec c.rounds c.f c.g c.reset (cutRate c.rounds c.f c.g) c.hostDrift c.hostDegree
        c.branch head dates billed last W τ β h (c.hostDrift+1) (quota c.rounds),
      ∀low:2^h≤(2:ℕ)^m,∀upper:(2:ℕ)^m≤(2^h)^2,∀opens:10*(X.size+1)≤(2:ℕ)^m,
      ∀geom:c.HostGeometry τ β h (2^m) X,
        TerminalRoomAt G c.spec c.rounds c.f c.g c.reset c.hostDrift W τ β h (2^m) →
        OriginalPurchaseAt G c.spec c.rounds c.f c.g c.reset c.nodesLog c.degree c.multiplicity
          c.hostDrift c.hostDegree W τ β h →
        StageDateResources G c.spec c.rounds c.f c.g c.reset c.hostDrift c.hostDegree c.nodesLog c.degree
          τ β h (2^m) (W*h) →
        let depth:=Nat.log 2 h/(2*β)
        let S₀:=stageNumbers G c.rounds depth c.f c.g c.reset (2^m) (tail τ depth)
        let k₀:=groupBits c.rounds depth S₀.hostGain S₀.capGain (cutRate c.rounds c.f c.g)
        ∀words:HostWordRoom G S₀ k₀ (tail τ depth) (headGrain G S₀ k₀ h) (headChunk G S₀) W h,
        c.StageReceipts head dates billed last W τ β h m X funds low upper opens geom words) :
    c.ProducesHosts c.hostDrift c.hostDegree :=by
  apply c.produces_of_stage_returns
  intro head dates billed last
  refine ⟨9,?_⟩
  intro W _enough
  refine ⟨c.hostDrift+1,quota c.rounds,0,?_⟩
  intro τ _
  refine ⟨0,?_⟩
  intro β _
  refine ⟨originalHostPrice G c.rounds c.f c.g c.reset c.nodesLog c.degree c.multiplicity W τ,?_⟩
  filter_upwards [] with h
  intro funds
  dsimp only
  intro m low upper cp pins X opens geom terminal purchase words resources isa
  exact c.returned_of_receipts head dates billed last W τ β h m X funds low upper opens geom words
    terminal purchase resources isa (readAt head dates billed last W τ β h m X funds low upper opens geom terminal purchase resources words)

end
end Hierarchy.DescentSixParty.EpochRotor

end OAI
