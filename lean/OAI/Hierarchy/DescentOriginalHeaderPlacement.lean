import OAI.Hierarchy.DescentOriginalWordReplay
import OAI.Hierarchy.DescentSeedSmallerAppendix
import OAI.Hierarchy.DescentFixedHostShell
import OAI.Hierarchy.DescentNamedSelectorCapture

namespace OAI
/-! # The early header and paid public shelves on the original dated replay -/
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
attribute [local irreducible] Origin.source Origin.archivePackage normalizedPackedChart SeedNamed.issued
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
local notation "cursor" => calendar («w»:=w) trace menu origin
local notation "age" => (S).length-1
local notation "phase" => Phase.atPorts G S board k tb age p f g drift degree h (menu).ordinary op
  (cursor age).ports (cursor age).floor
local notation "pitch" => grain (h/2) G.C
local notation "snapshots" => SnapshotCalendar reset (kindCalendar (S).rounds (S).height)
  (capCalendar G.b (S).rounds g (S).height) (snapshotDirectory («w»:=w) trace menu origin)

local notation "z" => originalReplay G board op t f g rate cut drift τ β h x branch W ordinary reset positive
  shorten fit H degree wire hist

local notation "E₀" => ExteriorCount x.X
local notation "width₀" => DescentExteriorShelf.span (V).j (V).rest s E₀
local notation "front" => (z).compact+17*width₀
local notation "pubRows" => E₀*2^((V).j+(V).rest)
local notation "extra_" K:arg => DescentTerminalPublicIdentity.total K (V).appendix.binWidth
  (V).appendix.arity (V).appendix.piece (V).appendix.codes (V).appendix.raw pubRows
local notation "census₀" => censusScanBase G t f g rate τ β n d op.C op drift x z
local notation "role₀" => (z).roleBase G t f g rate β x
local notation "replay₀" => (z).replayStart G t f g rate β x
local notation "P₀" => earnedPreflight G t f g rate τ β n d op.C op drift x
local notation "captured" => (Chronology.countDates 0 (Chronology.kindCalendar (S).rounds (S).height)).length
local notation "capture" => DescentWideSeedFlags.endInput x.X (S).copies s h+
  DescentPackedSeed.rows x.X (S).copies s h+1

private theorem seedHeadBelowBase (v : SeedHeader.Input F) (height : ℕ) :
    v.base G height-1 < v.base G height := by
  dsimp only [SeedHeader.Input.base]
  omega

private theorem initialFloorLePosition {bits : ℕ} {Cut : ℕ → Type*}
    (issuedMove : ∀ i, Cut i → Position → Move bits → Prop) (start : Position) (i : ℕ) :
    start.floor ≤ (RegisterTimeline.position issuedMove start i).floor := by
  rw [RegisterTimeline.position_floor]
  exact DescentDatedAddressBook.floor_mono start.floor (RegisterTimeline.span issuedMove start) (Nat.zero_le i)

private theorem selectorLeCompact (baseAddress shelfSize clock wordSize : ℕ) :
    baseAddress ≤ end_ (baseAddress+shelfSize) clock wordSize :=
  (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))

private theorem replayLeEarly (schedule : AtomSchedule) (depth tailBits start : ℕ) :
    start ≤ DescentExteriorMatrixUpdate.Calendar.earlyAt schedule depth tailBits start := by
  unfold DescentExteriorMatrixUpdate.Calendar.earlyAt DescentExteriorMatrixUpdate.Calendar.stop
    DescentExteriorMatrixUpdate.Calendar.tableAt
  omega

structure OriginalHeadPlacement (K : ℕ) : Prop where
  headerBelow : header<census₀
  archiveEnd : front+extra_ K≤header
  afterVotes : finalAt (front+extra_ K) lo pitch ss<header
  reelData : front+extra_ K≤replay₀
  headLow : header<replay₀
  captureBefore : capture+captured≤header
  reelAbove : finalAt (front+extra_ K) lo pitch ss<
    DescentExteriorMatrixUpdate.Calendar.earlyAt S k tb replay₀
  preRole : (z).compact+32*width₀≤role₀
  roleEnd : role₀+DescentTerminalRoleTables.count (originalRoleBits G op S p drift)≤(P₀).cohortEnd census₀
  romTop : front+DescentTerminalChipBootWords.total K (V).appendix.binWidth (V).appendix.arity
    (V).appendix.piece (V).appendix.codes+
    DescentTerminalDenseHeaderBoot.extent (V).appendix.arity ((V).appendix.binWidth*(V).appendix.piece)
      ≤(P₀).literalBase census₀
  publicBeforeMask : front+extra_ K≤(P₀).maskBase census₀
  capturePaid : capture+captured≤(origin).floor
  below : (z).compact+32*width₀≤replay₀

/-- The physical host may use any prefix of the public bin shelf paid by the seed. -/
theorem original_head_placement (K : ℕ) (fitsBins : K≤bins) :
    OriginalHeadPlacement G board op t f g rate cut drift τ β h x branch W ordinary reset positive
      shorten fit H degree wire hist K := by
  have votes := (V).smaller_appendix_header G h K fitsBins
  have archive : front+extra_ K≤header:=votes.1
  have voted : finalAt (front+extra_ K) lo pitch ss<header:=votes.2
  have baseEarly : header<(V).base G h := seedHeadBelowBase G V h
  have seedBefore : header<(origin).floor:=baseEarly.trans_le ((V).base_le_floor G op t f g drift h)
  have elapsed : (origin).floor≤(z).cursor :=
    initialFloorLePosition (bits:=w) (RegisterTimeline.issued trace menu) origin (S).length
  have roleAfter : (z).cursor≤role₀:=le_max_left ..
  have below : (z).compact+32*width₀≤role₀:=le_max_right ..
  have replayAfter : role₀≤replay₀:=Nat.le_add_right ..
  have beforeReplay : header<replay₀:=seedBefore.trans_le (elapsed.trans (roleAfter.trans replayAfter))
  have scanAfter := (z).scan_after_role G t f g rate τ β n d op.C op drift x
  have headBefore : header<census₀:=beforeReplay.trans_le scanAfter
  have mounted:=(original_shell_rom (P₀) census₀ (front+extra_ K) K (V).appendix.binWidth
    (V).appendix.arity (V).appendix.piece (V).appendix.codes (V).appendix.raw pubRows front le_rfl
    (archive.trans headBefore.le))
  have countLength : captured=(ss).length:=scheduled_capture_length (X:=x.X) (G:=G) («S»:=S)
    (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=x.opened)
    (shorten:=shorten) (fit:=fit)
  have startLow : lo≤(z).compact := selectorLeCompact lo (extent pitch ss) G.C pitch
  have copyEnd : capture+captured=lo := congrArg (fun count : ℕ => capture + count) countLength
  have above := replayLeEarly S k tb replay₀
  have copyEarly : capture+captured≤header :=
    copyEnd.le.trans (startLow.trans ((Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans archive)))
  refine ⟨headBefore,archive,voted,archive.trans beforeReplay.le,beforeReplay,copyEarly,
    voted.trans (beforeReplay.trans_le above),below,?_,mounted.2.1,mounted.2.2,
    copyEarly.trans seedBefore.le,below.trans replayAfter⟩
  exact original_role_before_census G board op t f g rate cut drift τ β h x branch W ordinary
      reset positive shorten fit H degree wire hist

private theorem highBeforeTrailing (high keys stored pool choices bound : ℕ)
    (fits : trailingStop (trailingCut high keys) stored pool choices + 1 < bound) : high < bound := by
  unfold trailingStop trailingCut at fits
  omega

private theorem cohortBeforeMask (spec : Spec) (start : ℕ) : spec.cohortEnd start ≤ spec.maskBase start := by
  obtain ⟨a,b,c,d,e,f,g,h,j⟩ := spec.layers start
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans (g.trans (h.trans j)))))))

variable (funds:OriginalWord G board op t f g rate cut drift limit branch head dates billed last W τ β h (drift+1) slots)
  (low:2^h≤x.sites) (dyadic:∃a,x.sites=2^a) (host:x.sites≤H) (upper:H≤hostRows x.sites)
  (coeff:degree≤limit)

include funds low dyadic host upper coeff in
/-- All replay census banks lie before the last address of the same funded machine. -/
theorem original_mask_and_replay_room (history:drift=max 1 (max reset.bitsR (op.C*reset.bitsR)))
    (L:TerminalPlacement) (channels:DescentTerminalVertexFields.MaskAllocation.Channels (S).radix) :
    (P₀).maskBase census₀<2^w ∧
    (Branch.replayCalendar x.X S k tb (V).j (V).rest snapshots).stop census₀<2^w:=by
  let cfg:=earnedShell G t f g rate τ β n d op.C x L
  let I:=earnedInput G t f g rate τ β n d op.C op drift x L
  let maskStart:=(P₀).maskBase census₀
  let high:=AddressPlan.last (earnedFormat G op S q p drift) cfg I channels maskStart
  have purchased:=original_replay_word G board op t f g rate cut drift limit τ β h x branch head dates
    billed last W slots ordinary reset positive shorten fit H degree wire hist funds low dyadic host upper
    coeff history L channels
  have lastRoom : high<2^w := highBeforeTrailing high cfg.terminal.rows raw cfg.terminal.pool
    ((V).appendix.codes*2^(q*p)) (2^w) purchased.2
  have maskAfter:= (AddressPlan.readout_measures (earnedFormat G op S q p drift) cfg I channels maskStart).1
  refine ⟨maskAfter.trans_lt lastRoom,?_⟩
  change (P₀).cohortEnd census₀<2^w
  exact (cohortBeforeMask P₀ census₀).trans_lt (maskAfter.trans_lt lastRoom)

include funds low dyadic host upper coeff in
theorem original_replay_room (history:drift=max 1 (max reset.bitsR (op.C*reset.bitsR)))
    (L:TerminalPlacement) (channels:DescentTerminalVertexFields.MaskAllocation.Channels (S).radix) :
    (Branch.replayCalendar x.X S k tb (V).j (V).rest snapshots).stop census₀<2^w:= (original_mask_and_replay_room G board op t f g rate cut drift limit τ β h x branch head
    dates billed last W slots ordinary reset positive shorten fit H degree wire hist funds low dyadic host
    upper coeff history L channels).2

include funds low dyadic host upper coeff in
theorem original_replay_base_fits (history:drift=max 1 (max reset.bitsR (op.C*reset.bitsR)))
    (L:TerminalPlacement) (channels:DescentTerminalVertexFields.MaskAllocation.Channels (S).radix) :
    replay₀<2^w:=by
  have paid:=original_replay_room G board op t f g rate cut drift limit τ β h x branch head dates
    billed last W slots ordinary reset positive shorten fit H degree wire hist funds low dyadic host
    upper coeff history L channels
  have afterRoles:replay₀≤census₀:=(z).scan_after_role G t f g rate τ β n d op.C op drift x
  change (P₀).cohortEnd census₀<2^w at paid
  exact afterRoles.trans_lt (((P₀).cohort_le census₀).trans_lt paid)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
