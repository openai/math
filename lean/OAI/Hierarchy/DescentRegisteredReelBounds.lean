import OAI.Hierarchy.DescentRegisteredReelAddresses
import OAI.Hierarchy.DescentOrdinaryReelCells
import OAI.Hierarchy.DescentResetReelCell
import OAI.Hierarchy.DescentNamedPrefixState
import OAI.Hierarchy.DescentRegisteredFinalEvent

namespace OAI
/-! # The two observed words lie inside the allocation of their own date -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentOrdinaryVenueIngress StageVenueTail
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
set_option hygiene false
set_option quotPrecheck false
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ fee} {hu : 0 ≤ u} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=Ht) (t:=S.rounds) S.height
      (initial X S.copies s (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 P bits} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G price fee S k i z D wire s} {T : StageInput W G rate fee}
    {nonneg : 0 ≤ fee} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' wire s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)

variable (op:RotorSpec) (frozen drift degree payload seats root:ℕ) (ports:DatePorts)
    (ordinary:ℕ→Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload seats ports
local notation "base" => (books).onTicket ticket g frozen p f payload seats ports.venue.lanes ports.io.roster ordinary
local notation "v" => DatePorts.ordinaryModel ports ticket op g frozen p f drift degree payload seats root ordinary
local notation "start" => PhysicalOrdinary.StaticCore.profileStart G S g k i p payload seats root

local notation "entry" => (base).registeredEntry ports start
local notation "core" => PhysicalOrdinary.StaticCore.atAge G S g k i p payload seats root ports.io.roster

include before tail cut in
private theorem registered_ordinary_reel_bounds (paths:(entry).clip.venue.paths=OrdinaryRaster.paths (v).area) :
    let assigned:=VenueProgram.Registered.atAge G S op g k i p frozen f drift degree payload seats root ports ordinary
    let turn:=(core).area.flagEnd ports.io.roster start+2^k
    root≤assigned.selector G ∧ assigned.selector G<(v).fullEnd root ∧ root≤turn ∧ turn<(v).fullEnd root := by
  intro assigned turn
  have ctrl:=registered_static_core X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  have arc:=congrArg PhysicalOrdinary.StaticCore.area ctrl
  have allPorts:=ordinary_ports_at X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary paths
  have countSeen : assigned.selector G = (v).countAddr root := allPorts.2.1.symm
  have turnSeen : turn = (v).area.flagEnd (v).old ((v).stageStart root)+2^(v).k :=
    congrArg (fun a : DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary => a.flagEnd ports.io.roster start+2^k) arc.symm
  rw [countSeen, turnSeen]
  exact (v).reel_cells root

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open SeedNamed RegisterTimeline DescentDatedAddressBook Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false
attribute [local irreducible] SeedNamed.issued RegisterTimeline.issued
local notation "cert" => SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
variable (w : ℕ)

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
variable {n₀ δ : ℕ} (b : RegisterTimeline.Menu n₀ δ) (initial : RegisterTimeline.Position)
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces b initial


variable (gain : b.gain=g) (grain : b.p=p) (arity : b.f=f)
variable (ready : Geometry G S b k w 0 initial)
variable (placed : ∀i (e : RunTrace.Events traces i),fitsAt traces b initial (w:=w) i e)

local notation "fixed" => all_registered_moves X G S ordinary reset branch positive room shorten w b gain grain arity

include gain grain arity ready placed in
set_option maxHeartbeats 1200000 in
theorem profiled_reel_bounds (walk : (last).Choice) (i : ℕ) (age : i<S.length) :
    let pos:=cursor i
    let stop:=(cursor (i+1)).floor
    pos.floor≤b.selectorAt G S k i pos ∧ b.selectorAt G S k i pos<stop ∧
      pos.floor≤b.rotationAt G S k i pos ∧ b.rotationAt G S k i pos<stop :=by
  let pos:=cursor i
  change pos.floor≤_ ∧ _<(cursor (i+1)).floor ∧ pos.floor≤_ ∧ _<(cursor (i+1)).floor
  obtain ⟨event⟩:=(traces walk).cut_in_prefix (traces walk).path .here rfl i age
  have caps : ∀c,(traces c).path.capFactors=capCalendar G.b S.rounds b.gain S.height:=by
    intro c
    rw [gain]
    dsimp only [SeedNamed.traceAt]
    exact (trace c).calendar
  have tags (c : (last).Choice) : (traces c).path.kinds=kindCalendar S.rounds S.height := by
    dsimp only [SeedNamed.traceAt]
    exact (trace c).kinds
  have sameMove := fun j (l r : RunTrace.Events traces j) (x y : Move w) =>
    fixed j (cursor j) l r x y
  have geometryAt : Geometry G S b k w i pos :=
    geometry_on_event (w:=w) traces b initial sameMove caps tags ready placed walk i event
  obtain ⟨move,hit,_⟩:=placed i ⟨walk,event⟩ geometryAt
  have selected:=(returned traces b initial i ⟨walk,event⟩ move hit
      (fun e a got=>fixed i pos e ⟨walk,event⟩ a move got hit)).2
  have tag : ((kindCalendar S.rounds S.height).drop i).head?=some event.isReset:=by
    exact (congrArg (fun ks : List Bool => (ks.drop i).head?) (tags walk)).symm.trans event.shown
  rw [selected]
  dsimp only [SeedNamed.traceAt] at event
  cases event with
  | reset before closed after path=>
    unfold RegisterTimeline.issued at hit
    obtain ⟨cap,space,rfl⟩:=hit
    let a:=PhysicalReset.scheduledAtPorts G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
      b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) pos.ports pos.floor
    change ((kindCalendar S.rounds S.height).drop i).head?=some true at tag
    have flag : Menu.resetFlag S i=true:=by simp [Menu.resetFlag,tag]
    have saved:=a.saved_between (F:=F) (Pin:=Unit)
    have sel : b.selectorAt G S k i pos=b.rotationAt G S k i pos:=by simp [Menu.selectorAt,flag]
    rw [sel,b.reset_rotation G S k i pos tag]
    exact ⟨saved.1,saved.2,saved.1,saved.2⟩
  | ordinary before ticket after path=>
    unfold RegisterTimeline.issued at hit
    obtain ⟨hk,ok,rfl⟩:=hit
    subst g
    subst p
    subst f
    let br:=trace walk
    change ((kindCalendar S.rounds S.height).drop i).head?=some false at tag
    have flag : Menu.resetFlag S i=false:=by simp [Menu.resetFlag,tag]
    simp only [Menu.selectorAt, Menu.rotationAt, flag, Bool.false_eq_true, ite_false]
    exact Branch.registered_ordinary_reel_bounds (h:=h) (C:=C) (k:=k) (p:=b.p) (g:=b.gain) (f:=b.f)
      X G S br ticket before after path b.op b.tail b.drift b.degreeLimit b.payload (b.seats i)
      pos.floor pos.ports b.ordinary ok.paths

include gain grain arity ready placed in
/-- A word issued at an earlier occupied date is above the initial allocation
and below each later cursor, including the final roof of the transcript. -/
theorem profiled_reel_range (walk : (last).Choice) (i : ℕ) (age : i<S.length) (word : ℕ)
    (cell : word=b.selectorAt G S k i (cursor i) ∨ word=b.rotationAt G S k i (cursor i)) :
    initial.floor≤word ∧ ∀j,i<j→word<(cursor j).floor :=by
  let steps:=RegisterTimeline.issued (w:=w) traces b
  have order : Monotone (fun j=>(cursor j).floor):=by
    intro a z le
    change (position steps initial a).floor ≤ (position steps initial z).floor
    rw [position_floor steps initial a,position_floor steps initial z]
    exact DescentDatedAddressBook.floor_mono initial.floor (span steps initial) le
  have all_:=profiled_reel_bounds X G S ordinary reset branch positive room shorten w b initial
    gain grain arity ready placed walk i age
  have inside : (cursor i).floor≤word ∧ word<(cursor (i+1)).floor:=by
    rcases cell with rfl|rfl
    · exact ⟨all_.1,all_.2.1⟩
    · exact all_.2.2
  exact ⟨(order (Nat.zero_le i)).trans inside.1,fun j later=>inside.2.trans_le (order later)⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
