import OAI.Hierarchy.DescentProfiledOriginalCourse
import OAI.Hierarchy.DescentProfiledOrdinaryArgumentTables
import OAI.Hierarchy.DescentProfiledResetTagSource
import OAI.Hierarchy.DescentOriginalTaggedArchivePrefix
import OAI.Hierarchy.DescentBoughtRoleRegister

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
open ProtocolRAM DescentOperandStateBanks DescentPrimitivePalette DescentLocalArchiveOrder DescentBundleHistory DescentKernelHistory
open private claimOnPath branchTrace branchClaim from OAI.Hierarchy.DescentNamedArchivePrefix
open private Origin.archiveOrder from OAI.Hierarchy.DescentNamedPrivateArchive
open private Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape
open private Palette.encodedOrigin from OAI.Hierarchy.DescentNamedPrimitivePalette
section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P → ℕ} {d k wire hist i z D w : ℕ} {q ε : ℝ} {U : MarkedWorld F d P bits}
private def archiveRowsAt (r : Reached U G q ε S k i z D wire hist) (p R Z : ℕ) (op : RotorSpec)
    (pos : RegisterTimeline.Position) (mem : Memory w) : Prop :=
  ∃ (desc : BitDescription U) (order : Local desc) (bounds : DatePorts.RangeRoom pos.ports r desc)
    (shape : WorldShape p R desc) (label : NodeOrder.All desc → Label G hist Z op)
    (pointer : NodeOrder.All desc → ℕ → Pointer)
    (flags : Fin (2^pos.ports.venue.k) → Fin pos.ports.nodes → Fin pos.ports.operandHosts → Fin pos.ports.venue.groups → ℕ),
    DatePorts.ArchiveRead pos.ports r desc order bounds shape op label pointer flags mem
private def readClaim {len : ℕ} (t : RunTrace G q ε S k wire hist len bits d)
    (p R Z : ℕ) (op : RotorSpec) : PrefixClaim t w :=
  fun {_} {_} {_} {_} {r} _ pos mem => archiveRowsAt r p R Z op pos mem

private def readsAtTrace {len : ℕ} (t : RunTrace G q ε S k wire hist len bits d)
    (p R Z : ℕ) (op : RotorSpec) (claim : PrefixClaim t w) : Prop :=
  ∀{W : MarkedWorld F d P bits} {j z D : ℕ} {r : Reached W G q ε S k j z D wire hist}
    (before : Path t.first r) (pos : RegisterTimeline.Position) (m : Memory w),
    before.whole p → before.aligned p R → before.OnlyRotor op → claim before pos m → archiveRowsAt r p R Z op pos m

variable {final : ℕ}
omit [Fintype P] in
private theorem readOnOwnPath
    {U V : MarkedWorld F d P bits} {z D z' D' : ℕ}
    (first : Reached U G q ε S k 0 z D wire hist)
    (last : Reached V G q ε S k final z' D' wire hist) (path : Path first last)
    {p R : ℕ} (hp : 0 < p) (hR : 1 ≤ R) (widths : ∀ y, p ∣ bits y)
    (op : RotorSpec) (menu : Runnable F op) (a : Archive U) (o : Local a.bit)
    (shape : WorldShape p R a.bit)
    (names : Encoding (Label G hist z op) (dictionary G op menu p) a.bit) (pin : P → ℕ) :
    readsAtTrace (RunTrace.mk U V z D z' D' first last path) p R z op
      (claimOnPath (w:=w) first last path hp hR widths op menu a o shape names pin) := by
  intro W i b E u before pos mem whole aligned chosen fields_
  obtain ⟨bounds,read⟩ := fields_ whole aligned chosen
  exact ⟨_,_,bounds,_,_,_,_,read⟩

end
open private register_cap_calendar from OAI.Hierarchy.DescentNamedPrefixState
open private traceAt_kinds from OAI.Hierarchy.DescentNamedBranchMachine
section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
  {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {A : Type*}
  (traces : A → RunTrace G q ε S k wire hist final bits d) {n δ : ℕ} (b : RegisterTimeline.Menu n δ)
  (initial : RegisterTimeline.Position) (c : A)
private def roleOnTrace : Prop :=
  ∀ {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (before : Path (traces c).first r) (after_ : Path r (traces c).last),
    before.append after_ = (traces c).path →
    (RegisterTimeline.calendar (w:=w) traces b initial i).ports.RoleRows ∧
    0 < (RegisterTimeline.calendar (w:=w) traces b initial i).ports.roleLanes
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
private theorem branchReads {he : 0≤ε₀} {hu : 0≤units₀} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (stride : 1 ≤ R) (op : RotorSpec) (menu : Runnable F op) (w : ℕ) :
    readsAtTrace (branchTrace X G S (r:=r) (c:=c) b) p R (S.grainAt G.b p 0) op
      (branchClaim X G S (r:=r) (c:=c) b hp stride op menu w) :=
  readOnOwnPath b.origin.source b.target b.path hp stride pinSizes_ op menu
    b.origin.archive (Origin.archiveOrder b.origin) (Origin.archiveShape b.origin p R hp stride widthDiv_)
    (Palette.encodedOrigin (p:=p) b.origin op menu) (fun y => y.1.val)
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


set_option maxHeartbeats 1800000





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
attribute [local irreducible] Origin.source Origin.archivePackage issued
local notation "claim" vote:arg => chosenClaim X G S ordinary reset branch positive room shorten w (walk₀ vote)
local notation "stride₁" => max 1 (max reset.bitsR (C*reset.bitsR))
private theorem selectedRows (votes : (ch).Pin → Bool) :
    readsAtTrace (traces (walk₀ votes)) p stride₁ ((S).grainAt G.b p 0) op (claim votes) := by
  exact branchReads X G S (r:=(cert).choose) (c:=walk₀ votes) (trace (walk₀ votes))
    positive (le_max_left 1 _) op reset.menu w
attribute [local irreducible] traceAt chosenClaim
private theorem profiledRowsOnTrace (votes : (ch).Pin → Bool)
    {U : MarkedWorld F 0 pins widths} {i Z D : ℕ}
    {r : Reached U G price fee S k i Z D ((S).epochPower^(S).priceExponent) s}
    (before : Path (traces (walk₀ votes)).first r) (after_ : Path r (traces (walk₀ votes)).last)
    (together : before.append after_ = (traces (walk₀ votes)).path)
    (pos : RegisterTimeline.Position) (mem : Memory w) (recorded : (claim votes) before pos mem) :
    archiveRowsAt r p stride₁ ((S).grainAt G.b p 0) op pos mem := by
  obtain ⟨whole,aligned,rotated⟩ := prefix_archive_witnesses X G S ordinary reset branch positive room shorten
    (walk₀ votes) before after_ together
  exact selectedRows X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit votes
    before pos mem whole aligned rotated recorded
private theorem profiledRoleOnTrace
    (votes : (ch).Pin → Bool)
    (placed : ∀ i (e : RunTrace.Events traces i), RegisterTimeline.fitsAt traces menu initial (w:=w) i e)
    (seed : Geometry G S menu k w 0 initial)
    (prior : initial.ports.RoleRows ∧ 0 < initial.ports.roleLanes)
    (palette : OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (input : p ≤ payload) (original : (S).firstWidth G.b p ≤ payload) :
    roleOnTrace (w:=w) traces menu initial (walk₀ votes) := by
  have ample := OrdinaryBooks.PrimitiveCalendar.role_unit G op t f g rate τ β drift degreeMax driftR payload siteCount p
    palette initial.ports (DatePorts.ArchiveWidths.node_bound G S op seed.room.archive) input original
  have moves := all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl
  intro U i z D r before after_ joined
  exact RegisterTimeline.bought_role_registers traces menu initial
    (fun j a b x y => moves j (cursor j) a b x y) placed
    (register_cap_calendar X G S ordinary reset branch positive room shorten menu rfl)
    (traceAt_kinds X G S ordinary reset branch positive room shorten)
    seed (walk₀ votes) prior ample before after_ joined

private theorem profiledReadOnEvent (votes : (ch).Pin → Bool) (i : ℕ)
    (e : (traces (walk₀ votes)).path.Event i) (pos : RegisterTimeline.Position) (mem : Memory w)
    (prior : e.previousClaim (claim votes) pos mem) :
    e.previousClaim (readClaim (traces (walk₀ votes)) p stride₁ ((S).grainAt G.b p 0) op) pos mem := by
  cases e with
  | ordinary before ticket after_ cut =>
    exact profiledRowsOnTrace X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit
      votes before ((Path.here.ordinary ticket).append after_)
      ((Path.append_cut_assoc before (Path.here.ordinary ticket) after_).symm.trans cut) pos mem prior
  | reset before closed after_ cut =>
    exact profiledRowsOnTrace X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit
      votes before ((Path.here.reset closed).append after_)
      ((Path.append_cut_assoc before (Path.here.reset closed) after_).symm.trans cut) pos mem prior

private theorem profiledRolesOnEvent (votes : (ch).Pin → Bool)
    (placed : ∀ i (e : RunTrace.Events traces i), RegisterTimeline.fitsAt traces menu initial (w:=w) i e)
    (seed : Geometry G S menu k w 0 initial)
    (prior : initial.ports.RoleRows ∧ 0 < initial.ports.roleLanes)
    (palette : OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (input : p ≤ payload) (original : (S).firstWidth G.b p ≤ payload)
    (i : ℕ) (e : (traces (walk₀ votes)).path.Event i) :
    (cursor i).ports.RoleRows ∧ 0 < (cursor i).ports.roleLanes := by
  cases e with
  | ordinary before ticket after_ cut =>
    exact profiledRoleOnTrace X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit drift degree degreeMax lo header initial votes placed seed prior palette input original before ((Path.here.ordinary ticket).append after_)
      ((Path.append_cut_assoc before (Path.here.ordinary ticket) after_).symm.trans cut)
  | reset before closed after_ cut =>
    exact profiledRoleOnTrace X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit drift degree degreeMax lo header initial votes placed seed prior palette input original before ((Path.here.reset closed).append after_)
      ((Path.append_cut_assoc before (Path.here.reset closed) after_).symm.trans cut)
attribute [local semireducible] traceAt

private theorem acquiredCutData (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ scale J₀ driftR) (sites : siteCount≤(2^payload)^2)
    (input : p≤ payload) (coeff : degree≤ degreeMax) (original : (S).firstWidth G.b p≤ payload)
    (pre : Geometry G S menu k w 0 initial) (positiveK : 0< k)
    (headerFits : initial.floor≤2^(headRate*payload)) (machine : (t+1+max K headRate+2)*payload≤ w)
    (palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (votes:(ch).Pin→Bool) (m:Memory w)
    (seedRoles : initial.ports.RoleRows ∧ 0< initial.ports.roleLanes)
    (i : ℕ) (e : (traces (walk₀ votes)).path.Event i)
    (previous : e.previousClaim (claim votes) (cursor i) (DateCode.history cpu m i)) :
    e.previousClaim (readClaim (traces (walk₀ votes)) p stride₁ ((S).grainAt G.b p 0) op) (cursor i) (DateCode.history cpu m i) ∧
    (cursor i).ports.RoleRows ∧ 0 < (cursor i).ports.roleLanes ∧ payload ≤ w ∧
    ∀ j (evt : RunTrace.Events traces j), fitsAt traces menu initial (w:=w) j evt := by
  have placed (j : ℕ) (cutEvt : RunTrace.Events traces j) :=
    (profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
      input coeff original pre positiveK headerFits machine j cutEvt).1
  have bus : payload ≤ w :=
    (Nat.le_mul_of_pos_left _ (show 0 < t+1+max K headRate+2 by omega)).trans machine
  have rows := profiledReadOnEvent X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit
    votes i e (cursor i) (DateCode.history cpu m i) previous
  have roles := profiledRolesOnEvent X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit
    drift degree degreeMax lo header initial votes placed pre seedRoles palette input original i e
  exact ⟨rows,roles.1,roles.2,bus,placed⟩


theorem profiled_acquire_tags (K headRate : ℕ)
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
    (i : ℕ) (e : (traces (walk₀ votes)).path.Event i) (cells : geom i)
    (old : e.incoming (cursor i) (DateCode.history cpu m i))
    (previous : e.previousClaim (claim votes) (cursor i) (DateCode.history cpu m i))
    (tags : (cursor i).ports.ArchiveTags (DateCode.history cpu m i))
    (earned : e.required ((ch).rows votes).length ((ch).read votes=some (walk₀ votes))) :
    RegisterTimeline.TagInputs traces menu initial (walk₀ votes) m i e := by
  obtain ⟨rows, roles, live, bus, placed⟩ :=
    acquiredCutData X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit
      drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites input coeff
      original pre positiveK headerFits machine palette votes m seedRoles i e previous
  cases e with
  | ordinary before ticket after_ cutAt =>
    obtain ⟨desc, rank, bounds, shape, label, pointer, flags, read⟩ := rows
    exact profiled_ordinary_tag_sources X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver
      growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets
      nonempty split beforeHeader oldHeader votes m oldVotes ticket before after_ cutAt cells observed old earned
      desc rank bounds shape label pointer flags read roles live tags
  | reset before closed after_ cutAt =>
    obtain ⟨desc, rank, bounds, shape, label, pointer, flags, read⟩ := rows
    exact profiled_reset_tag_sources X G S ordinary reset branch positive room shorten w fit drift degree payload
      lo header initial bus seedDegree degreeRoom (walk₀ votes) m before closed after_ cutAt rank bounds shape label
      pre placed old resetWords read

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
