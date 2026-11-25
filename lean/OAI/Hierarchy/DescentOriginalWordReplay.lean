import OAI.Hierarchy.DescentOriginalMachineRatio
import OAI.Hierarchy.DescentSeedHeaderPhysicalFloor
import OAI.Hierarchy.DescentRegisteredSnapshotDirectory
import OAI.Hierarchy.DescentIssuedLastReset
import OAI.Hierarchy.DescentChosenGrainRoom

namespace OAI
/-! # Last-date sources of the original paid census, including the private profile tape -/
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
set_option maxHeartbeats 3400000
set_option maxRecDepth 12000
set_option cleanup.letToHave false
attribute [local irreducible] normalizedPackedChart SeedNamed.issued
section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
variable (c : (Epochs.finish G _ _ (SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice) (height : 0<S.height)


private def issuedResetOnPath : Path.FinalReset p (issued X G S ordinary reset branch positive room shorten c).path := by
  exact ((issued X G S ordinary reset branch positive room shorten c).path).finalReset p (issued X G S ordinary reset branch positive room shorten c).recorded (by
    rw [(issued X G S ordinary reset branch positive room shorten c).kinds]
    exact kindCalendar_last S.rounds height)

end

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

open Lean Elab Term in
local elab "replayApply% " fn:term:arg "[" args:term,* "]" : term => do
  let e ← elabTerm fn none
  return mkAppN e (← args.getElems.mapM fun arg => elabTerm arg none)

def originalReplay : CensusReplay k where
  «cursor» := (cursor (S).length).floor
  «compact» := end_ (lo+extent pitch ss) G.C pitch
  «seedFloor» := (origin).floor
  «j» := (V).j
  «rest» := (V).rest
  «lanes» := s
  «slots» := (phase).output.argumentSlots
  «width» := (phase).digits
  «snapshots» := snapshots
  «roleBankBits» := originalRoleBits G op S p drift

local notation "z" => originalReplay G board op t f g rate cut drift τ β h x branch W ordinary reset positive
  shorten fit H degree wire hist
local notation "headRate" => t+1+max dates head+2
variable (funds:OriginalWord G board op t f g rate cut drift limit branch head dates billed last W τ β h (drift+1) slots)
  (low:2^h≤x.sites) (dyadic:∃a,x.sites=2^a) (host:x.sites≤H) (upper:H≤hostRows x.sites)
  (coeff:degree≤limit)

include funds low dyadic host upper coeff in
theorem original_replay_ready :
    (z).ReadyAt G t f g rate τ β headRate x :=by
  let source:=funds.calendar.words.seed x.sites low x.upper dyadic x.X ordinary reset positive x.opened shorten
    w fit H degree wire hist host upper funds.calendar.words.seedFits
  have native : s≤h:=(S).split_first_width G.b h W₀ (2^headChunk G S) (Nat.two_pow_pos _)
  have grainSize:p≤h:=(S).grain_le_payload G.b p h G.base_pos native
  have group : 0<k:=by
    unfold groupBits
    exact Nat.add_pos_left (Nat.add_pos_right _ (by decide : 0<8)) _
  have growing:drift+1 ≤ TerminalScale.scale J (drift+1):=by
    unfold TerminalScale.scale
    exact (Nat.le_mul_of_pos_right (drift+1) (Nat.succ_pos _)).trans Nat.lt_two_pow_self.le
  have finish:=profiled_last_floor_at_rate x.X G t rate τ β x.sites h ordinary reset branch positive x.opened shorten
    w fit board op drift degree limit lo header origin dates head funds.calendar.words.steps funds.pitches.old
    funds.pitches.returned funds.receiver growing x.upper grainSize coeff native source.geometry group source.head
    funds.calendar.words.datesFit
  have places:=profiled_calendar_at_rate x.X G t rate τ β x.sites h ordinary reset branch positive x.opened shorten
    w fit board op drift degree limit lo header origin dates head funds.calendar.words.steps funds.pitches.old
    funds.pitches.returned funds.receiver growing x.upper grainSize coeff native source.geometry group source.head
    funds.calendar.words.datesFit
  let walk:=(normalizedRoute x.X G S ordinary reset branch positive x.opened shorten w fit).follow (fun _=>false)
  have occupied (i : ℕ) (e : RunTrace.Events trace i) :
      RegisterTimeline.fitsAt trace menu origin («w»:=w) i e := (places i e).1
  have originalReceipt := replayApply% (@issuedResetOnPath) [F, (inferInstance : Field F), x.cp, x.ports, x.X, G, S,
    k, cut, tb, n, d, op.C, f, g, p, ordinary, reset, branch, positive, x.opened, shorten, walk, funds.started]
  have located := replayApply% (@original_last_lookup) [F, (inferInstance : Field F), x.cp, x.ports,
    x.X, G, n, d, op.C, f, g, p, cut, tb, t, rate, τ, β, x.sites, h, ordinary, reset,
    branch, positive, x.opened, shorten, w, fit, n, d, board, op, drift, degree, limit, lo,
    header, origin, x.upper, grainSize, coeff, source.geometry, occupied, walk, originalReceipt, funds.lookup]
  have small:head≤headRate:=by omega
  have endpoint:=(V).anchor_le_floor G op t f g drift h
  refine ⟨finish.le,source.head.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right h small)),?_,rfl,located.lookup,funds.roleTables x.sites⟩
  exact (Nat.le_add_right ..).trans endpoint

private theorem start_le_mask (P:Spec) (base:ℕ) : base≤P.maskBase base:=by
  have early:=P.cohort_le base
  obtain ⟨a,b,c,d,e,f,g,j,lastLayer⟩:=P.layers base
  omega

local notation "scanStart" => censusScanBase G t f g rate τ β n d op.C op drift x z
local notation "maskStart" => (earnedPreflight G t f g rate τ β n d op.C op drift x).maskBase scanStart
local notation "extra" => (V).appendix.words (ExteriorCount x.X*2^((V).j+(V).rest))

theorem original_role_before_census :
    (z).roleBase G t f g rate β x+DescentTerminalRoleTables.count (originalRoleBits G op S p drift)≤
      (earnedPreflight G t f g rate τ β n d op.C op drift x).cohortEnd scanStart :=
  ((z).scan_after_role G t f g rate τ β n d op.C op drift x).trans ((earnedPreflight G t f g rate τ β n d op.C op drift x).cohort_le scanStart)

theorem original_public_before_mask : extra≤ maskStart:=by
  have mounted:=(V).anchor_le_floor G op t f g drift h
  have initial : extra≤(origin).floor:=(Nat.le_add_left ..).trans mounted
  have past : (origin).floor≤(cursor (S).length).floor:=by
    rw [RegisterTimeline.position_floor]
    exact DescentDatedAddressBook.floor_mono _ _ (Nat.zero_le (S).length)
  have afterwards:=(z).scan_after_cursor G t f g rate τ β n d op.C op drift x
  exact initial.trans (past.trans (((le_max_left ..).trans afterwards).trans (start_le_mask _ _)))

include funds low dyadic host upper coeff in
/-- This is the final census for the actual initial paid table and terminal
register. Both the tagged profile area and the vote destination are accounted for. -/
theorem original_replay_word (history:drift=max 1 (max reset.bitsR (op.C*reset.bitsR)))
    (L:TerminalPlacement) (channels:DescentTerminalVertexFields.MaskAllocation.Channels (S).radix) :
    let cfg:=earnedShell G t f g rate τ β n d op.C x L
    let I:=earnedInput G t f g rate τ β n d op.C op drift x L
    let high:=AddressPlan.last (earnedFormat G op S q p drift) cfg I channels maskStart
    high≤2^(last*h) ∧
      trailingStop (trailingCut high cfg.terminal.rows) raw cfg.terminal.pool
        ((V).appendix.codes*2^(q*p))+1<2^w :=by
  intro cfg I high
  have issued_:=normalized_issued_preflight G t f g rate τ β h n d op.C x ordinary reset branch positive shorten
  rw [←history] at issued_
  have fit_:=original_replay_ready G board op t f g rate cut drift limit τ β h x branch head dates billed last
    W slots ordinary reset positive shorten fit H degree wire hist funds low dyadic host upper coeff
  have readout:=funds.census x (z) L channels issued_ fit_
  have placed:=original_public_before_mask G board op t f g rate cut drift τ β h x branch W ordinary reset
    positive shorten fit H degree wire hist
  exact ⟨readout.1,readout.2 bins (V).appendix.codes raw (ExteriorCount x.X*2^((V).j+(V).rest)) w placed funds.finalFits⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
