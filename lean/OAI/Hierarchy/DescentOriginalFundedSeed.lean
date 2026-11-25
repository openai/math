import OAI.Hierarchy.DescentOriginalHeaderPlacement
import OAI.Hierarchy.DescentStageDateResources
import OAI.Hierarchy.DescentWideSeedTokenInput

namespace OAI
/-! # The physical seed and date operands of the original funded host -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentTerminalFixedSlices
open DescentInitialHost DescentSeedRoot DescentDatedSeedStartup DescentPackedEpochShelves DescentWideSeedFlags
open DescentTerminalEpochChart DescentTerminalEpochDecoder DescentMixedRouter DescentResetInvoice Chronology RegisterTimeline
open DescentPackedProfileInstall DescentExterior DescentExteriorShelf Catalyst CatalystSubstitution CorrectionBatch
open Computability.BorderVNP.Crossing ThreeFlat.Routing
open DescentTerminalCompiledPrefix DescentTerminalPreflightSpace DescentTerminalLocalPortBook
open DescentTerminalLast DescentDatedAddressBook.PhysicalReset ProtocolRAM
open DescentTerminalCompiledPrefix.AddressPlan
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1500000
set_option maxRecDepth 12000
attribute [local irreducible] normalizedPackedChart issued
set_option quotPrecheck false
variable {F:Type} [Field F] (G:PoweredGadget F) {n d:ℕ} (board:NonlinearExpanders.Graph n d)
  (op:RotorSpec) (t f g rate cut drift limit τ β h:ℕ) (x:ShellSource F h)
  (branch:G.b≤2^(capRate G t g)) (head dates billed last W slots:ℕ)
local notation "J" => Nat.log 2 h/(2*β)
local notation "tb" => tail τ J
local notation "S" => stageNumbers G t J f g rate x.sites tb
local notation "k" => groupBits t J (hostRate t rate) (capRate G t g) (cutRate t f g)
local notation "p" => headGrain G S k h
local notation "s" => (S).firstWidth G.b p
local notation "W₀" => NativeBranch.binLimit («k»:=k) S
local notation "q" => headArity G S
local notation "w" => W*h
variable (ordinary:OrdinaryRates G (stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β)))) (groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) cut) (reset:ResetRates G (stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β)))) (groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) (atRound t) n d op.C f g cut (tail τ (Nat.log 2 h/(2*β))))
  (positive:0<(headGrain G (stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β)))) (groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) h)) (shorten:reentryRate d op.C*(1-(2-G.rate)/4)^t≤1/2) (fit:(((stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β))))).firstWidth G.b (headGrain G (stageNumbers G t (Nat.log 2 h/(2*β)) f g rate x.sites (tail τ (Nat.log 2 h/(2*β)))) (groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) h))<2^(W*h))
  (H degree wire hist:ℕ)
local notation "trace" => traceAt x.X G S ordinary reset branch positive x.opened shorten
local notation "chart" => normalizedPackedChart x.X G S ordinary reset branch positive x.opened shorten w fit
local notation "ss" => (chart).layout
local notation "bins" => terminalBinCount x.X G S p q W₀ n d op.C f g+1
local notation "raw" => terminalRawRows x.X G S p q n d op.C f g
local notation "V" => originalSeedHead G op drift x.X ss S k tb h H degree wire hist bins raw
local notation "origin" => (V).position G op t f g drift h
local notation "lo" => selectorBase x.X (S).copies s h (ss).length
local notation "header" => (V).base G h-1
local notation "menu" => fromProfiles G S board op k tb p f g drift degree h lo header ss
local notation "startup" => (V).layout G t f g drift h
local notation "seedEnd" => (DescentDatedSeedStartup.Input.nodeChart startup k H ((S).groupCount 0)).seedEnd
  (DescentDatedSeedStartup.endAddress x.X startup H ((S).groupCount 0) k)
local notation "Z₀" => (S).grainAt G.b p 0
local notation "pitch" => Primitive.paletteLanes G op s Z₀ h k
local notation "capture" => DescentWideSeedFlags.endInput x.X (S).copies s h+
  DescentPackedSeed.rows x.X (S).copies s h+1
local notation "dates_" => countDates 0 (kindCalendar (S).rounds (S).height)
local notation "publicBaseRate" => (NativePitch.FundedBase.public_rate G t f g rate).choose
local notation "spend_" => 44*argumentDigitRate G t f g rate (drift+1) publicBaseRate

structure OriginalFundedSeed : Prop where
  hosts : Fintype.card (Vertex x.X)≤H
  signed : DescentSignedCableCodec.width 3 256*(startup).packedLanes≤w
  «fields» : (startup).operandBits*(startup).operandLanes≤w
  low : header<(startup).base
  source : DescentPackedSeed.publicWords x.X+DescentDyadicSpan.span
    (DescentPackedSeed.Primitive.Source.jobs x.X (S).copies (startup).seedWidth h)≤ seedEnd
  live : 0<pitch
  embed : h≤w
  boot : (origin).floor<2^w
  grant : ProfiledRate.Covers G board op t f g rate τ drift limit β h dates
  old : ArgumentCalendar G op t f g rate τ β drift (drift+1) limit h
  returned : ReturnCalendar G t f g rate (drift+1) spend_ τ β W h
  receiver : ReceiverCalendar G board op t f g rate τ drift limit β h
  growth : drift+1≤ TerminalScale.scale J (drift+1)
  input : p≤h
  first : s≤h
  geometry : Geometry G S menu k w 0 origin
  groups : 0<k
  headerFits : (origin).floor≤2^(head*h)
  machine : (t+1+max dates head+2)*h≤w
  observations : ObservationRoom G S h w
  degree : (origin).ports.venue.degree=3
  paid : capture+(dates_).length≤(origin).floor

theorem original_funded_seed
    (funds:OriginalWord G board op t f g rate cut drift limit branch head dates billed last W τ β h (drift+1) slots)
    (low:2^h≤x.sites) (dyadic:∃a,x.sites=2^a) (host:x.sites≤H) (upper:H≤hostRows x.sites) :
    OriginalFundedSeed G board op t f g rate cut drift limit τ β h x branch head dates W ordinary reset
      positive shorten fit H degree wire hist :=by
  have seed:=funds.calendar.words.seed x.sites low x.upper dyadic x.X ordinary reset positive x.opened shorten
    w fit H degree wire hist host upper funds.calendar.words.seedFits
  have entries:=original_head_placement G board op t f g rate cut drift τ β h x branch W ordinary reset
    positive shorten fit H degree wire hist (terminalBinCount x.X G S p q W₀ n d op.C f g) (Nat.le_succ _)
  have hbase : header<(startup).base:= by
    change (V).base G h-1<(V).base G h
    exact Nat.lt_succ_self _
  have fc:=DescentDatedSeedStartup.fences x.X startup H ((S).groupCount 0) k
  have rEnd : (startup).base≤ seedEnd := (fc.1.trans (fc.2.1.trans fc.2.2)).trans
    ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have sourceBound:=Root.role_source_extent x.X (S).copies s h seed.digits
  have packedBound : DescentWideSeedFlags.endInput x.X (S).copies s h≤header :=
    (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans entries.captureBefore))
  have native : s≤h:=(S).split_first_width G.b h W₀ (2^headChunk G S) (Nat.two_pow_pos _)
  have card:=(DescentInitialHost.«initialize» x.X).2.1
  change Fintype.card (Vertex x.X)+Fintype.card (Cable x.X)+_≤10*(x.X.size+1) at card
  refine ⟨(by have := x.opened;omega),seed.signed,seed.fields,hbase,?_,seed.live,seed.machine,seed.space,
    funds.calendar.words.steps,funds.pitches.old,funds.pitches.returned,funds.receiver,?_,
    (S).grain_le_payload G.b p h G.base_pos native,native,seed.geometry,(by unfold groupBits; exact Nat.add_pos_left (Nat.add_pos_right _ (by decide : 0<8)) _),
    seed.head,funds.calendar.words.datesFit,funds.calendar.words.observations x.sites x.upper w le_rfl,
    rfl,entries.capturePaid⟩
  · exact sourceBound.trans (packedBound.trans (hbase.le.trans rEnd))
  · unfold TerminalScale.scale
    exact (Nat.le_mul_of_pos_right (drift+1) (Nat.succ_pos _)).trans Nat.lt_two_pow_self.le

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
