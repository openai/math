import OAI.Hierarchy.DescentMatchedPublicOrigins
import OAI.Hierarchy.DescentNamedFreshPanelsAt

namespace OAI
/-! Registered prior operands and original public packets share one scheduled actor memory. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSixParty DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open DescentPackedColony DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
open DescentPackedZip DescentOrdinaryHostPad DescentRetainedRangeDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
open scoped Fin.CommRing
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z D n₁ h₁ C f₁ g₁ cut tail₁ wire hist : ℕ}
    {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n₁ h₁ C f₁ g₁ cut tail₁}
    {n h f g tail : ℕ} (board₀ : NonlinearExpanders.Graph n h) (op₀ : RotorSpec)
    (B : ClosedReset input ctl) (p drift degree payload w : ℕ) (ordinary : ℕ→Dated.Ordinary)
    (seats profile : ℕ→ℕ) (header : ℕ) (cursor : Position)
local notation "op" => op₀
local notation "s₀" => S.firstWidth G.b p
local notation "Z₀" => S.grainAt G.b p 0
local notation "board" => board₀
local notation "old" => cursor.ports.venue
local notation "io" => cursor.ports.io
local notation "cap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "oldExp" => NativePitch.resetCut S k tail p f payload age
local notation "nextM" => NativePitch.incoming S k tail p f payload ordinary (age+1)
local notation "oldL" => cursor.ports.operandLanes
local notation "roleL" => cursor.ports.roleLanes
local notation "token" => DescentPrimitivePalette.printedBits G s₀ Z₀ op
local notation "rcut" => receiverCut G S board k tail age p f g drift degree payload oldExp nextM (op).C (op).w
  oldL roleL token old
local notation "base" => cursor.ports.priorStart k cursor.floor
local notation "history" => (cursor.ports.afterPad k cursor.floor).archive
local notation "outer" => scheduledAtPorts G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor
local notation "a" => (outer).inner
local notation "v" => (a).successor
local notation "fits" => scheduled_cut_origin G S board k tail age p f g drift degree payload ordinary op s₀ Z₀ oldL roleL old
local notation "priorFits" => preceding_cut S k tail p f payload age
local notation "menu" => (⟨board,op,g,tail,p,f,drift,degree,payload,seats,ordinary,profile,header⟩ : Menu n h)
local notation "publisher" => priorArchivePhase G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w
variable (space : ScheduledCodeRoom G S board₀ k tail age p f g drift degree payload ordinary op₀
      (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports.operandLanes cursor.ports.roleLanes
      cursor.ports.venue cursor.ports.io (cursor.ports.priorStart k cursor.floor) w (cursor.ports.afterPad k cursor.floor).archive)
local notation "u" => DatePorts.resetInputs G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w space
local notation "ports" => cursor.ports
local notation "mem₁" m:arg => (publisher).image m
local notation "phase" => (a).ingress.phase base w (io).hubs (fun x=>(io).atoms x.val)
  (fun j=>(io).wire j.1.val j.2.val)
local notation "atMem" m:arg => (phase).image (mem₁ m)

include B in
abbrev MatchedFreshInputsAt (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (hb : HEq ctl.board board₀) (ho : RotorSpec.ofRates ctl=op₀) (ready : (u).Ready) (dst : Memory w) : Prop := by
  let q := rcut
  let previous := oldExp
  let pitch := nextM
  let printed := token
  have thisCut := fits
  have oldCut := priorFits
  subst n
  subst h
  subst f
  subst g
  subst tail
  cases (eq_of_heq hb : ctl.board=board₀)
  cases ho
  exact DateInputs.FreshInputsAt (B:=B) drift degree payload q previous (2^q) pitch oldL roleL printed old io base w
    thisCut thisCut oldCut (history).count (history).nodeBase (history).arguments (history).seed
    (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space) ready dst

variable {description : BitDescription W} {R : ℕ} (number : Local description)
  (bounds : DatePorts.RangeRoom cursor.ports input description) (shape : WorldShape p R description)
  (label : NodeOrder.All description→Label G (S.firstWidth G.b p) (S.grainAt G.b p 0) op₀)

variable (geo : Geometry G S (⟨board₀,op₀,g,tail,p,f,drift,degree,payload,seats,ordinary,profile,header⟩ : Menu n h) k w age cursor)
    (widths : DatePorts.ArchiveWidths G S op₀ cursor.ports k tail p drift degree payload age)

theorem matched_fresh_at_public_actor (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (hb : HEq ctl.board board₀) (ho : RotorSpec.ofRates ctl=op₀)
    (degreeAt : (old).degree=D) (ready : (u).Ready) (m : Memory w) (capAt : input.placement.cap=cap)
    (held : MatchedRegisteredOperandPanels board₀ op₀ B p drift degree payload w ordinary seats profile header cursor space
      number bounds shape label geo widths hn hh hf hg ht hb ho degreeAt ready m capAt)
    (dst : Memory w) (orig : MatchedPublicOriginsAt board₀ op₀ B p drift degree payload w ordinary cursor space
      hn hh hf hg ht hb ho degreeAt ready m capAt dst) :
    MatchedFreshInputsAt board₀ op₀ B p drift degree payload w ordinary cursor space hn hh hf hg ht hb ho ready dst ∧
      (u).throughOperandDate.Runs (atMem m) ((u).sheetsResult ready dst) := by
  let entry := (publisher).image m
  let q := rcut
  let previous := oldExp
  let pitch := nextM
  let printed := token
  have thisCut := fits
  have oldCut := priorFits
  subst n
  subst h
  subst f
  subst g
  subst tail
  cases (eq_of_heq hb : ctl.board=board₀)
  cases ho
  obtain ⟨data,roles,prior,panels⟩ := held
  obtain ⟨μ,measured,rows⟩ := orig
  exact DateInputs.fresh_at_public_actor (B:=B) drift degree payload q previous (2^q) pitch oldL roleL printed
    old io base w thisCut thisCut oldCut (history).count (history).nodeBase (history).arguments (history).seed
    (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space) degreeAt capAt ready entry _ μ measured dst panels rows

theorem matched_fresh_inputs_at_origins (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (hb : HEq ctl.board board₀) (ho : RotorSpec.ofRates ctl=op₀)
    (degreeAt : (old).degree=D) (ready : (u).Ready) (m : Memory w) (capAt : input.placement.cap=cap)
    (held : MatchedRegisteredOperandPanels board₀ op₀ B p drift degree payload w ordinary seats profile header cursor space
      number bounds shape label geo widths hn hh hf hg ht hb ho degreeAt ready m capAt)
    (orig : MatchedPublicOrigins board₀ op₀ B p drift degree payload w ordinary cursor space
      hn hh hf hg ht hb ho degreeAt ready m capAt) :
    ∃dst : Memory w, (u).ThroughActors (atMem m) dst ∧
      MatchedPublicOriginsAt board₀ op₀ B p drift degree payload w ordinary cursor space
        hn hh hf hg ht hb ho degreeAt ready m capAt dst ∧
      MatchedFreshInputsAt board₀ op₀ B p drift degree payload w ordinary cursor space hn hh hf hg ht hb ho ready dst ∧
      (u).throughOperandDate.Runs (atMem m) ((u).sheetsResult ready dst) := by
  obtain ⟨dst,reached,publicRows⟩ := orig
  exact ⟨dst,reached,publicRows,matched_fresh_at_public_actor board₀ op₀ B p drift degree payload w ordinary
    seats profile header cursor space number bounds shape label geo widths hn hh hf hg ht hb ho degreeAt ready
    m capAt held dst publicRows⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
