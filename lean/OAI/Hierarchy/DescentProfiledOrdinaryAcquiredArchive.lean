import OAI.Hierarchy.DescentProfiledOrdinaryArchivePlaces
import OAI.Hierarchy.DescentProfiledOrdinaryArchiveSpans
import OAI.Hierarchy.DescentProfiledOrdinaryBasicPrimitive

namespace OAI
/-! # The complete returned archive on an ordinary selected date -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open scoped Fin.CommRing
noncomputable section
open ProtocolRAM DescentOperandStateBanks DescentPrimitivePalette DescentLocalArchiveOrder DescentBundleHistory DescentKernelHistory
open private claimOnPath branchTrace branchClaim from OAI.Hierarchy.DescentNamedArchivePrefix
open private Origin.archiveOrder from OAI.Hierarchy.DescentNamedPrivateArchive
open private Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape
open private Palette.encodedOrigin from OAI.Hierarchy.DescentNamedPrimitivePalette
-- Place after the current namespace opens and before the paid section variables.
private theorem selectedNodesAtTarget
    {F P : Type} [Field F] {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i grain degree wire hist w p R : ℕ}
    {r : Reached W G q ε S k i grain degree wire hist} {B : BitDescription W}
    {number : DescentLocalArchiveOrder.Local B} {shape : DescentBundleHistory.WorldShape p R B}
    {p₀ p₁ : DatePorts} {m₀ m₁ : Memory w} {where₁ : DatePorts.RangeRoom p₁ r B}
    (ports : p₁ = p₀) (memory : m₁ = m₀)
    (physical : DatePorts.NodeRows r B number shape p₀ (ports ▸ where₁) m₀) :
    DatePorts.NodeRows r B number shape p₁ where₁ m₁ :=
  DatePorts.node_rows_at_cursor r B number shape ports memory (ports ▸ where₁) where₁ physical

section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P → ℕ} {d k wire hist i z D w : ℕ} {q ε : ℝ} {U : MarkedWorld F d P bits}
variable {final : ℕ}
private def fieldReturnOnPath
    {U V : MarkedWorld F d P bits} {z D z' D' : ℕ}
    (first : Reached U G q ε S k 0 z D wire hist)
    (last : Reached V G q ε S k final z' D' wire hist) (path : Path first last)
    {p R : ℕ} (hp : 0 < p) (hR : 1 ≤ R) (widths : ∀ y, p ∣ bits y)
    (op : RotorSpec) (menu : Runnable F op) (a : Archive U) (o : Local a.bit)
    (seedShape : WorldShape p R a.bit)
    (names : Encoding (Label G hist z op) (dictionary G op menu p) a.bit) (pin : P → ℕ)
    (claim : PrefixClaim (RunTrace.mk U V z D z' D' first last path) w) : Prop := ∀
    {W : MarkedWorld F d P bits} {j Z D₁ : ℕ} {r : Reached W G q ε S k j Z D₁ wire hist}
    (before : Path first r) (pos : RegisterTimeline.Position) (mem : Memory w)
    (whole : before.whole p) (aligned : before.aligned p R) (rotated : before.OnlyRotor op)
    , claim before pos mem ↔ ∃room : DatePorts.RangeRoom pos.ports r (before.archive p hp a whole).bit,
      DatePorts.ArchiveRead pos.ports r (before.archive p hp a whole).bit
      (trajectory p hp a o before whole) room (archiveShape hp hR widths a seedShape before whole aligned) op
      (encodePath op menu before hp whole rotated a names).atNode
      (Reached.argumentPointer r _ (trajectory p hp a o before whole)
        (archiveShape hp hR widths a seedShape before whole aligned) hp pin pos.ports.argumentsPerNode)
      (archiveFlag r _ (trajectory p hp a o before whole) pos.ports room) mem
omit [Fintype P] in
private theorem fieldReturnOnRealPath
    {U V : MarkedWorld F d P bits} {z D z' D' : ℕ}
    (first : Reached U G q ε S k 0 z D wire hist)
    (last : Reached V G q ε S k final z' D' wire hist) (path : Path first last)
    {p R : ℕ} (hp : 0 < p) (hR : 1 ≤ R) (widths : ∀ y, p ∣ bits y)
    (op : RotorSpec) (menu : Runnable F op) (a : Archive U) (o : Local a.bit)
    (seedShape : WorldShape p R a.bit)
    (names : Encoding (Label G hist z op) (dictionary G op menu p) a.bit) (pin : P → ℕ)
    : fieldReturnOnPath (w:=w) first last path hp hR widths op menu a o seedShape names pin
        (claimOnPath first last path hp hR widths op menu a o seedShape names pin) := by
  intro W j Z D₁ reached before pos mem whole aligned rotated
  dsimp only [claimOnPath, archiveClaim]
  constructor
  · intro saved
    exact saved whole aligned rotated
  · rintro ⟨room, evidence⟩ _ _ _
    exact ⟨room, evidence⟩
end
variable {F : Type} [Field F]
section
variable {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
local notation "wire₀" => S.epochPower^S.priceExponent
local notation "s₀" => S.firstWidth G.b p
local notation "q₀" => (1/((s₀:ℝ)*(wire₀:ℝ)):ℝ)
local notation "ε₀" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "units₀" => q₀*(wire₀:ℝ)
local notation "depthBound_" => GroupStage.depthBound (atRound S.rounds) n f g
local notation "pinSizes_" => (fun _ => dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b) 1)
local notation "widthDiv_" => dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b
private theorem fieldReturnOnBranch {he : 0≤ε₀} {hu : 0≤units₀} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (stride : 1 ≤ R) (op : RotorSpec) (menu : Runnable F op) (w : ℕ) : fieldReturnOnPath (w:=w) b.origin.source b.target b.path hp stride pinSizes_ op menu
        b.origin.archive (Origin.archiveOrder b.origin) (Origin.archiveShape b.origin p R hp stride widthDiv_)
        (Palette.encodedOrigin (p:=p) b.origin op menu) (fun y=>y.1.val)
        (branchClaim X G S (r:=r) (c:=c) b hp stride op menu w) := by
  exact fieldReturnOnRealPath b.origin.source b.target b.path hp stride pinSizes_ op menu
    b.origin.archive (Origin.archiveOrder b.origin) (Origin.archiveShape b.origin p R hp stride widthDiv_)
    (Palette.encodedOrigin (p:=p) b.origin op menu) (fun y=>y.1.val)
end

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


set_option maxRecDepth 12000
set_option cleanup.letToHave false
set_option maxHeartbeats 1600000





local notation "geom" i => Geometry G S menu k w i (cursor i)

local notation "baseRate" => (NativePitch.FundedBase.public_rate G t f g rate).choose
variable {driftR ratio : ℕ}
local notation "funds" => 44*argumentDigitRate G t f g rate driftR baseRate


open DescentPackedEpochShelves
local notation "storage" => DescentPackedEpochShelves.grain (payload/2) G.C
local notation "family" => fun i H=>SignedStage.atDate G S g k i H

open DescentPackedProfileTape DescentPackedProfileInstall
local notation "cpu" => RegisterTimeline.instruction (w:=w) traces menu initial
open private archiveWalk from OAI.Hierarchy.DescentProfiledOrdinaryArchivePlaces
local notation "walk₀" votes:arg => archiveWalk X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit votes

open DescentLocalArchiveOrder DescentPrimitivePalette DescentKernelHistory DescentBundleHistory
open private chosenClaim from OAI.Hierarchy.DescentNamedArchivePrefix
attribute [local irreducible] Origin.source Origin.archivePackage issued
local notation "claim" vote:arg => chosenClaim X G S ordinary reset branch positive room shorten w (walk₀ vote)
open private Origin.archiveOrder from OAI.Hierarchy.DescentNamedPrivateArchive
open private Palette.encodedOrigin from OAI.Hierarchy.DescentNamedPrimitivePalette
open DescentSIMDLookup DescentPackedColony
local notation "org" vote:arg => (trace (walk₀ vote)).origin
open private Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape
local notation "stride₁" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "fullBranch" vote:arg => trace (walk₀ vote)
local notation "pinDiv" => dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b
local notation "pinFactors" => (fun _ : pins=>dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b) 1)
private theorem selectedFieldReturn (votes : (ch).Pin → Bool) :
    fieldReturnOnPath (w:=w) (fullBranch votes).origin.source (fullBranch votes).target (fullBranch votes).path
      positive (le_max_left 1 _) pinFactors op reset.menu (fullBranch votes).origin.archive
      (Origin.archiveOrder (fullBranch votes).origin)
      (Origin.archiveShape (fullBranch votes).origin p stride₁ positive (le_max_left 1 _) pinDiv)
      (Palette.encodedOrigin (p:=p) (fullBranch votes).origin op reset.menu)
      (fun y:pins=>y.1.val) (claim votes) := by
  exact fieldReturnOnBranch X G S (r:=(cert).choose) (c:=walk₀ votes) (trace (walk₀ votes))
    positive (le_max_left 1 _) op reset.menu w

private def profiledArchiveComponents : Prop := ∀ (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ scale J₀ driftR) (sites : siteCount≤(2^payload)^2)
    (input : p≤ payload) (coeff : degree≤ degreeMax) (original : (S).firstWidth G.b p≤ payload)
    (pre : Geometry G S menu k w 0 initial) (positiveK : 0< k)
    (headerFits : initial.floor≤2^(headRate*payload)) (machine : (t+1+max K headRate+2)*payload≤ w)
    (_matcher:MatcherRoom G S k p payload)
    (_signed:∀i H:ℕ,i≤(S).length→2*((family i H).unit)≤ payload)
    (_palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (bin sockets:ℕ) (_nonempty:0< sockets)
    (_split:p=bin*(payload/(16*((sockets*(G.b^((S).rounds*(S).height)*G.b))*bin))))
    (_beforeHeader:lo+extent storage (ch).layout≤ header) (_oldHeader:header< initial.floor)
    (votes:(ch).Pin→Bool) (m:Memory w)
    (_oldVotes:∀a∈shelves storage lo 0 (ch).layout,∀j:Fin (slots a.src.seats storage),
      m (a.base+j.val)=((packed a.src.pin votes storage j.val).val:Computability.VPVNP.BurstRAM.Word w))
    (_observed:ObservationRoom G S payload w)
    (_seedRoles:initial.ports.RoleRows ∧ 0< initial.ports.roleLanes)
    (_limit:max 1 (max reset.bitsR (C*reset.bitsR))≤drift)
    {W:MarkedWorld F 0 pins widths} {i z D z' D':ℕ} {q:ℝ} {nonneg:0≤fee}
    {prior:Reached W G price fee S k i z D ((S).epochPower^(S).priceExponent) s}
    {T:StageInput W G q fee} {choice:(T.result nonneg).Choice} {norm:Normalize ((T.result nonneg).state choice)}
    {next:Reached norm.result G price fee S k (i+1) z' D' ((S).epochPower^(S).priceExponent) s}
    (ticket:OrdinaryLink prior nonneg T choice norm next)
    (before:Path (trace (walk₀ votes)).origin.source prior) (after:Path next (trace (walk₀ votes)).target)
    (located:(before.ordinary ticket).append after=(trace (walk₀ votes)).path)
    (cells:geom i)
    (_old:(cursor i).ports.held prior (cursor i).floor (DateCode.history cpu m i))
    (_accepted:before.selections.length+1<((ch).rows votes).length ∨ (ch).read votes=some (walk₀ votes))
    (_previous:(claim votes) before (cursor i) (DateCode.history cpu m i))
    (_tags:(cursor i).ports.ArchiveTags (DateCode.history cpu m i))
    (_originSize : Fintype.card (trace (walk₀ votes)).origin.source.V ≤ initial.ports.operandHosts),
    let pathFull := before.ordinary ticket
    let full := prefix_archive_witnesses X G S ordinary reset branch positive room shorten (walk₀ votes) pathFull after located
    let archived := pathFull.archive p positive (org votes).archive full.1
    let rankAt := trajectory p positive (org votes).archive (Origin.archiveOrder (org votes)) pathFull full.1
    let stride := max 1 (max reset.bitsR (C*reset.bitsR))
    let headWidth := dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b
    let factor := le_max_left 1 (max reset.bitsR (C*reset.bitsR))
    let shapeAt := archiveShape positive factor (fun _ : pins => dvd_mul_of_dvd_left headWidth 1) (org votes).archive
      (Origin.archiveShape (org votes) p stride positive factor headWidth) pathFull full.1 full.2.1
    let place := profiled_ordinary_archive_places X G t rate τ β siteCount payload ordinary reset branch
      positive room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver
      growth sites input coeff original pre positiveK headerFits machine votes (W:=W) (i:=i) (z:=z) (D:=D) (z':=z') (D':=D') (q:=q) (nonneg:=nonneg) (prior:=prior) (T:=T) (choice:=choice) (next:=next) ticket before after located cells full.1
    let portsAt := (cursor (i+1)).ports
    let pointer := Reached.argumentPointer next archived.bit rankAt shapeAt positive (fun y:pins=>y.1.val) portsAt.argumentsPerNode
    let state := DateCode.history cpu m (i+1)
    let lab := (encodePath op reset.menu pathFull positive full.1 full.2.2 (org votes).archive (Palette.encodedOrigin (p:=p) (org votes) op reset.menu)).atNode
    DatePorts.HeaderRows portsAt next archived.bit rankAt place shapeAt pointer state →
    DatePorts.SpanRows portsAt next archived.bit rankAt place shapeAt state →
    DatePorts.NodeRows next archived.bit rankAt shapeAt portsAt place state →
    (∀x:Fin (2^portsAt.venue.k),Reads (portsAt.archive.roles.bank x.val)
       (fun actor group=>DescentSIMDLookup.encode (printedBits G s ((S).grainAt G.b p 0) op) portsAt.nodes (fun j=>
       (DatePorts.slotAt portsAt next archived.bit rankAt place x j actor group).elim 0 (fun y=> token G s ((S).grainAt G.b p 0) op (lab y)))) portsAt.roleLanes state) →
      (claim votes) pathFull (cursor (i+1)) (DateCode.history cpu m (i+1))
private theorem profiled_ordinary_components_to_claim :
    profiledArchiveComponents (driftR:=driftR) (ratio:=ratio) X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit drift degree degreeMax lo header initial := by
  intro K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes observed seedRoles limit W i z D z₁ D₁ q nonneg prior T choice norm next ticket before after located cells old accepted previous tags originSize
  dsimp only
  intro headers spans metadata roles
  have structural := prefix_archive_witnesses X G S ordinary reset branch positive room shorten (walk₀ votes) (before.ordinary ticket) after located
  have result := selectedFieldReturn X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit votes (W:=norm.result) (j:=i+1) (Z:=z₁) (D₁:=D₁) (r:=next) (before.ordinary ticket) (cursor (i+1)) (DateCode.history cpu m (i+1)) structural.1 structural.2.1 structural.2.2
  apply result.mpr
  exact ⟨_,headers,spans,metadata.1,metadata.2,roles⟩

private abbrev profiledArchivePendingRows : Prop := ∀ (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ scale J₀ driftR) (sites : siteCount≤(2^payload)^2)
    (input : p≤ payload) (coeff : degree≤ degreeMax) (original : (S).firstWidth G.b p≤ payload)
    (pre : Geometry G S menu k w 0 initial) (positiveK : 0< k)
    (headerFits : initial.floor≤2^(headRate*payload)) (machine : (t+1+max K headRate+2)*payload≤ w)
    (_matcher:MatcherRoom G S k p payload)
    (_signed:∀i H:ℕ,i≤(S).length→2*((family i H).unit)≤ payload)
    (_palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (bin sockets:ℕ) (_nonempty:0< sockets)
    (_split:p=bin*(payload/(16*((sockets*(G.b^((S).rounds*(S).height)*G.b))*bin))))
    (_beforeHeader:lo+extent storage (ch).layout≤ header) (_oldHeader:header< initial.floor)
    (votes:(ch).Pin→Bool) (m:Memory w)
    (_oldVotes:∀a∈shelves storage lo 0 (ch).layout,∀j:Fin (slots a.src.seats storage),
      m (a.base+j.val)=((packed a.src.pin votes storage j.val).val:Computability.VPVNP.BurstRAM.Word w))
    (_observed:ObservationRoom G S payload w)
    (_seedRoles:initial.ports.RoleRows ∧ 0< initial.ports.roleLanes)
    (_limit:max 1 (max reset.bitsR (C*reset.bitsR))≤drift)
    {W:MarkedWorld F 0 pins widths} {i z D z' D':ℕ} {q:ℝ} {nonneg:0≤fee}
    {prior:Reached W G price fee S k i z D ((S).epochPower^(S).priceExponent) s}
    {T:StageInput W G q fee} {choice:(T.result nonneg).Choice} {norm:Normalize ((T.result nonneg).state choice)}
    {next:Reached norm.result G price fee S k (i+1) z' D' ((S).epochPower^(S).priceExponent) s}
    (ticket:OrdinaryLink prior nonneg T choice norm next)
    (before:Path (trace (walk₀ votes)).origin.source prior) (after:Path next (trace (walk₀ votes)).target)
    (located:(before.ordinary ticket).append after=(trace (walk₀ votes)).path)
    (cells:geom i)
    (_old:(cursor i).ports.held prior (cursor i).floor (DateCode.history cpu m i))
    (_accepted:before.selections.length+1<((ch).rows votes).length ∨ (ch).read votes=some (walk₀ votes))
    (_previous:(claim votes) before (cursor i) (DateCode.history cpu m i))
    (_tags:(cursor i).ports.ArchiveTags (DateCode.history cpu m i))
    (_originSize : Fintype.card (trace (walk₀ votes)).origin.source.V ≤ initial.ports.operandHosts),
    let pathFull := before.ordinary ticket
    let full := prefix_archive_witnesses X G S ordinary reset branch positive room shorten (walk₀ votes) pathFull after located
    let archived := pathFull.archive p positive (org votes).archive full.1
    let rankAt := trajectory p positive (org votes).archive (Origin.archiveOrder (org votes)) pathFull full.1
    let stride := max 1 (max reset.bitsR (C*reset.bitsR))
    let headWidth := dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b
    let factor := le_max_left 1 (max reset.bitsR (C*reset.bitsR))
    let shapeAt := archiveShape positive factor (fun _ : pins => dvd_mul_of_dvd_left headWidth 1) (org votes).archive
      (Origin.archiveShape (org votes) p stride positive factor headWidth) pathFull full.1 full.2.1
    let place := profiled_ordinary_archive_places X G t rate τ β siteCount payload ordinary reset branch
      positive room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver
      growth sites input coeff original pre positiveK headerFits machine votes (W:=W) (i:=i) (z:=z) (D:=D) (z':=z') (D':=D') (q:=q) (nonneg:=nonneg) (prior:=prior) (T:=T) (choice:=choice) (next:=next) ticket before after located cells full.1
    let portsAt := (cursor (i+1)).ports
    let pointer := Reached.argumentPointer next archived.bit rankAt shapeAt positive (fun y:pins=>y.1.val) portsAt.argumentsPerNode
    let state := DateCode.history cpu m (i+1)
    DatePorts.HeaderRows portsAt next archived.bit rankAt place shapeAt pointer state →
    DatePorts.SpanRows portsAt next archived.bit rankAt place shapeAt state →
    DatePorts.NodeRows next archived.bit rankAt shapeAt portsAt place state →
      (claim votes) pathFull (cursor (i+1)) (DateCode.history cpu m (i+1))
private theorem profiled_ordinary_archive_from_range_and_metadata :
    profiledArchivePendingRows (driftR:=driftR) (ratio:=ratio) X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit drift degree degreeMax lo header initial := by
  intro K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes observed seedRoles limit W i z D z₁ D₁ q nonneg prior T choice norm next ticket before after located cells old accepted previous tags originSize
  dsimp only
  intro headers spans metadata
  have structural := prefix_archive_witnesses X G S ordinary reset branch positive room shorten (walk₀ votes) (before.ordinary ticket) after located
  have place := profiled_ordinary_archive_places X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine votes ticket before after located cells structural.1
  let beforeOn : Path (traces (((normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes))).first prior := by
    dsimp only [traceAt]
    exact before
  let afterOn : Path next (traces (((normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes))).last := by
    dsimp only [traceAt]
    exact after
  have locatedOn : (beforeOn.ordinary ticket).append afterOn = (traces (((normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes))).path := by
    dsimp only [traceAt, beforeOn, afterOn, id]
    exact located
  have roles := profiled_ordinary_basic_primitive X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes observed seedRoles ticket beforeOn afterOn locatedOn cells old accepted previous tags structural.1 structural.2.2 place
  exact profiled_ordinary_components_to_claim X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes observed seedRoles limit ticket before after located cells old accepted previous tags originSize headers spans metadata roles

private abbrev profiledAcquiredContract : Prop := ∀ (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ scale J₀ driftR) (sites : siteCount≤(2^payload)^2)
    (input : p≤ payload) (coeff : degree≤ degreeMax) (original : (S).firstWidth G.b p≤ payload)
    (pre : Geometry G S menu k w 0 initial) (positiveK : 0< k)
    (headerFits : initial.floor≤2^(headRate*payload)) (machine : (t+1+max K headRate+2)*payload≤ w)
    (_matcher:MatcherRoom G S k p payload)
    (_signed:∀i H:ℕ,i≤(S).length→2*((family i H).unit)≤ payload)
    (_palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (bin sockets:ℕ) (_nonempty:0< sockets)
    (_split:p=bin*(payload/(16*((sockets*(G.b^((S).rounds*(S).height)*G.b))*bin))))
    (_beforeHeader:lo+extent storage (ch).layout≤ header) (_oldHeader:header< initial.floor)
    (votes:(ch).Pin→Bool) (m:Memory w)
    (_oldVotes:∀a∈shelves storage lo 0 (ch).layout,∀j:Fin (slots a.src.seats storage),
      m (a.base+j.val)=((packed a.src.pin votes storage j.val).val:Computability.VPVNP.BurstRAM.Word w))
    (_observed:ObservationRoom G S payload w)
    (_seedRoles:initial.ports.RoleRows ∧ 0< initial.ports.roleLanes)
    (_limit:max 1 (max reset.bitsR (C*reset.bitsR))≤drift)
    {W:MarkedWorld F 0 pins widths} {i z D z' D':ℕ} {q:ℝ} {nonneg:0≤fee}
    {prior:Reached W G price fee S k i z D ((S).epochPower^(S).priceExponent) s}
    {T:StageInput W G q fee} {choice:(T.result nonneg).Choice} {norm:Normalize ((T.result nonneg).state choice)}
    {next:Reached norm.result G price fee S k (i+1) z' D' ((S).epochPower^(S).priceExponent) s}
    (ticket:OrdinaryLink prior nonneg T choice norm next)
    (before:Path (trace (walk₀ votes)).origin.source prior) (after:Path next (trace (walk₀ votes)).target)
    (located:(before.ordinary ticket).append after=(trace (walk₀ votes)).path)
    (cells:geom i)
    (_old:(cursor i).ports.held prior (cursor i).floor (DateCode.history cpu m i))
    (_accepted:before.selections.length+1<((ch).rows votes).length ∨ (ch).read votes=some (walk₀ votes))
    (_previous:(claim votes) before (cursor i) (DateCode.history cpu m i))
    (_tags:(cursor i).ports.ArchiveTags (DateCode.history cpu m i))
    (_originSize : Fintype.card (trace (walk₀ votes)).origin.source.V ≤ initial.ports.operandHosts),
    let pathFull := before.ordinary ticket
    let full := prefix_archive_witnesses X G S ordinary reset branch positive room shorten (walk₀ votes) pathFull after located
    let archived := pathFull.archive p positive (org votes).archive full.1
    let rankAt := trajectory p positive (org votes).archive (Origin.archiveOrder (org votes)) pathFull full.1
    let stride := max 1 (max reset.bitsR (C*reset.bitsR))
    let headWidth := dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b
    let factor := le_max_left 1 (max reset.bitsR (C*reset.bitsR))
    let shapeAt := archiveShape positive factor (fun _ : pins => dvd_mul_of_dvd_left headWidth 1) (org votes).archive
      (Origin.archiveShape (org votes) p stride positive factor headWidth) pathFull full.1 full.2.1
    let place := profiled_ordinary_archive_places X G t rate τ β siteCount payload ordinary reset branch
      positive room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver
      growth sites input coeff original pre positiveK headerFits machine votes (W:=W) (i:=i) (z:=z) (D:=D) (z':=z') (D':=D') (q:=q) (nonneg:=nonneg) (prior:=prior) (T:=T) (choice:=choice) (next:=next) ticket before after located cells full.1
    let portsAt := (cursor (i+1)).ports
    let pointer := Reached.argumentPointer next archived.bit rankAt shapeAt positive (fun y:pins=>y.1.val) portsAt.argumentsPerNode
    DatePorts.HeaderRows portsAt next archived.bit rankAt place shapeAt pointer (DateCode.history cpu m (i+1)) →
      (claim votes) pathFull (cursor (i+1)) (DateCode.history cpu m (i+1))

open Lean Elab Term in
local elab "finishArchive% " f:term:arg h:term:arg ranges:term:arg nodes:term:arg : term => do
  return mkApp3 (← elabTerm f none) (← elabTerm h none) (← elabTerm ranges none) (← elabTerm nodes none)
set_option maxHeartbeats 3800000
set_option maxRecDepth 32768
set_option cleanup.letToHave false
theorem profiled_ordinary_archive_from_headers :
    profiledAcquiredContract (driftR:=driftR) (ratio:=ratio) X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit drift degree degreeMax lo header initial := by
  intro K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes observed seedRoles limit W i z D z₁ D₁ q nonneg prior T choice norm next ticket before after located cells old accepted previous tags originSize
  dsimp only
  intro headers
  let beforeOn : Path (traces (((normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes))).first prior := by
    dsimp only [traceAt]
    exact before
  let afterOn : Path next (traces (((normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes))).last := by
    dsimp only [traceAt]
    exact after
  have locatedOn : (beforeOn.ordinary ticket).append afterOn = (traces (((normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes))).path := by
    dsimp only [traceAt, beforeOn, afterOn, id]
    exact located
  let previousOn : chosenClaim X G S ordinary reset branch positive room shorten w (((normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes)) beforeOn (cursor i) (DateCode.history cpu m i) := by
    dsimp only [beforeOn, id]
    simpa only [archiveWalk] using previous
  have spans := profiled_ordinary_archive_spans X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes observed seedRoles limit ticket beforeOn afterOn locatedOn cells old accepted previousOn tags originSize
  have measured := profiled_header_node_rows X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes observed seedRoles limit ticket beforeOn afterOn locatedOn cells old accepted previousOn tags originSize
  let completed := profiled_ordinary_archive_from_range_and_metadata X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes observed seedRoles limit ticket before after located cells old accepted previous tags originSize
  apply completed headers spans
  let evt : RunTrace.Events traces i := ⟨((normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes), .ordinary beforeOn ticket afterOn locatedOn⟩
  have cv := profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
    input coeff original pre positiveK headerFits machine i evt
  have bounds := (cv.2 cells).1
  have word : payload ≤ w := (Nat.le_mul_of_pos_left _ (by omega : 0<t+1+max K headRate+2)).trans machine
  have live : i < (S).length := ticket.hubRows.choose
  let entry := (cursor i).ports
  let floor_ := (cursor i).floor
  let seats := (menu).seats i
  let out := DatePorts.ordinaryPorts entry ticket op g frozen p f drift degree payload seats floor_ (menu).ordinary
  let model := DatePorts.ordinaryModel entry ticket op g frozen p f drift degree payload seats floor_ (menu).ordinary
  have code := Branch.registered_geometry_fits X G S (trace (((normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes))) ticket beforeOn afterOn locatedOn op frozen drift
    degree payload floor_ entry (menu).ordinary board (menu).seats (menu).profile header w live word
    cells cells.degree ⟨rfl,rfl⟩ bounds.1 bounds.2
  let calibrated := profiled_calibrated_execution X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
    input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader
    oldHeader i evt cells
  have fixed := all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl i (cursor i)
  let program := DatePorts.ordinaryDate entry ticket op g frozen p f drift degree payload seats floor_ (menu).ordinary
    w ((menu).profile i) header positiveK code
  let move : RegisterTimeline.Move w := ⟨program, ⟨out,model.fullEnd floor_⟩⟩
  have issuedAt : RegisterTimeline.issued traces menu i evt (cursor i) move := ⟨positiveK,code,rfl⟩
  have posted := RegisterTimeline.ordinary_posted_cut traces menu initial (((normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes)) m beforeOn ticket afterOn locatedOn
    positiveK code (calibrated code) (fun ev act seen => fixed ev evt act move seen issuedAt)
  apply selectedNodesAtTarget posted.2.1 posted.2.2
  exact measured.2

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
