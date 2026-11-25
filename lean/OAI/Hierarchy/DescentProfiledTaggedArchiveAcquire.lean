import OAI.Hierarchy.DescentProfiledAcquireTags
import OAI.Hierarchy.DescentProfiledOrdinaryAcquiredArchive
import OAI.Hierarchy.DescentProfiledOrdinaryHeaders
import OAI.Hierarchy.DescentProfiledSelfArchive

namespace OAI
/-! # The padded archive tags acquired from the actual ordinary and reset shelves on an earned cut -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F)
variable {n h C f g p cut tail : ℕ}
variable (t rate τ β siteCount payload : ℕ)
local notation "J₀" => Nat.log 2 payload/(2*β)
set_option quotPrecheck false
local notation "frozen" => DescentCompiler.TerminalScale.tail τ J₀
local notation "S" => stageNumbers G t J₀ f g rate siteCount frozen
local notation "k" => groupBits t J₀ (hostRate t rate) (capRate G t g) (cutRate t f g)
variable (ordinary : OrdinaryRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) cut) (reset : ResetRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) (atRound (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).rounds) n h C f g cut (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β))))
variable (branch : G.b ≤ 2^(stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^(stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).rounds ≤ 1/2)
set_option quotPrecheck false
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => (S).firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*((S).epochPower^(S).priceExponent:ℝ)):ℝ)
local notation "fee" => ((((S).initialSites*(S).copies:ℕ):ℝ)/(S).epochPower)
local notation "pins" => (Σ _ : Fin (S).copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler.TerminalScale
local notation "board" => reset.board
local notation "op" => RotorSpec.ofRates reset
variable
    (drift degree degreeMax lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial


set_option maxHeartbeats 6000000





local notation "geom" i => Geometry G S menu k w i (cursor i)

local notation "baseRate" => (NativePitch.FundedBase.public_rate G t f g rate).choose
variable {driftR ratio : ℕ}
local notation "funds" => 44*argumentDigitRate G t f g rate driftR baseRate


open DescentPackedEpochShelves
local notation "storage" => DescentPackedEpochShelves.grain (payload/2) G.C
local notation "family" => fun i H=>SignedStage.atDate G S g k i H

open DescentPackedProfileTape DescentPackedProfileInstall
local notation "cpu" => RegisterTimeline.instruction (w:=w) traces menu initial
local notation "walk₀" votes => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes

open DescentLocalArchiveOrder DescentPrimitivePalette DescentKernelHistory DescentBundleHistory
open private chosenClaim from OAI.Hierarchy.DescentNamedArchivePrefix
attribute [local irreducible] Origin.source Origin.archivePackage issued traceAt chosenClaim
local notation "claim" vote:arg => chosenClaim X G S ordinary reset branch positive room shorten w (walk₀ vote)
local notation "R₁" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "org" vote:arg => (trace (walk₀ vote)).origin
attribute [local semireducible] traceAt

theorem profiled_tagged_archive_acquire (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ scale J₀ driftR) (sites : siteCount≤(2^payload)^2)
    (input : p≤ payload) (coeff : degree≤ degreeMax) (original : (S).firstWidth G.b p≤ payload)
    (pre : Geometry G S menu k w 0 initial) (positiveK : 0< k)
    (headerFits : initial.floor≤2^(headRate*payload)) (machine : (t+1+max K headRate+2)*payload≤ w)
    (matcher:MatcherRoom G S k p payload)
    (signed:∀i H:ℕ,i≤(S).length→2*((family i H).unit)≤ payload)
    (palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (bin sockets:ℕ) (nonempty:0< sockets)
    (split:p=bin*(payload/(16*((sockets*(G.b^((S).rounds*(S).height)*G.b))*bin))))
    (beforeHeader:lo+extent storage (ch).layout≤ header) (oldHeader:header< initial.floor)
    (votes:(ch).Pin→Bool) (m:Memory w)
    (oldVotes:∀a∈shelves storage lo 0 (ch).layout,∀j:Fin (slots a.src.seats storage),
      m (a.base+j.val)=((packed a.src.pin votes storage j.val).val:Computability.VPVNP.BurstRAM.Word w))
    (observed:ObservationRoom G S payload w)
    (seedDegree:initial.ports.venue.degree=3) (degreeRoom:maximumDegree ((S).rounds+1)+1<2^w)
    (resetWords:SnapshotWordRoom S n h k frozen p f g payload w)
    (seedRoles : initial.ports.RoleRows ∧ 0< initial.ports.roleLanes)
    (limit : R₁≤drift)
    (originSize : Fintype.card (org votes).source.V≤ initial.ports.operandHosts)
    (walks : DescentHaloWalkRAM.breadth (maximumDegree ((S).rounds+1))≤2^k)
    (i : ℕ) (e : (traces (walk₀ votes)).path.Event i) (cells : geom i)
    (old : e.incoming (cursor i) (DateCode.history cpu m i))
    (previous : e.previousClaim (claim votes) (cursor i) (DateCode.history cpu m i))
    (tags : (cursor i).ports.ArchiveTags (DateCode.history cpu m i))
    (earned : e.required ((ch).rows votes).length ((ch).read votes=some (walk₀ votes))) :
    e.nextClaim (claim votes) (cursor (i+1)) (DateCode.history cpu m (i+1)) ∧
      RegisterTimeline.TagInputs traces menu initial (walk₀ votes) m i e :=by
  have labels:=profiled_acquire_tags X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites input coeff
    original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader
    votes m oldVotes observed seedDegree degreeRoom resetWords seedRoles i e cells old previous tags earned
  refine ⟨?_,labels⟩
  cases e with
  | ordinary before ticket after located=>
    have heads:=profiled_ordinary_headers X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites input coeff
      original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader
      votes m oldVotes observed seedRoles limit ticket before after located cells old earned previous tags originSize walks
    exact profiled_ordinary_archive_from_headers X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites input coeff
      original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader
      votes m oldVotes observed seedRoles limit ticket before after located cells old earned previous tags originSize heads
  | reset before closed after located=>
    have bus:payload≤w:=(Nat.le_mul_of_pos_left _ (show 0<t+1+max K headRate+2 by omega)).trans machine
    have placed (j:ℕ) (evt:RunTrace.Events traces j) :=
      (profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
        w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
        input coeff original pre positiveK headerFits machine j evt).1
    exact profiled_self_archive X G S ordinary reset branch positive room shorten w fit drift degree payload
      lo header initial bus seedDegree degreeRoom (walk₀ votes) m before closed after located pre placed old resetWords previous limit

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
