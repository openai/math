import OAI.Hierarchy.DescentMatchedPanelTags
import OAI.Hierarchy.DescentAllTaggedOrdinals

namespace OAI
/-! All seven physical operand words at the actor selected by the scheduled reset. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSixParty DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open DescentPackedColony DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
open DescentPackedZip DescentOrdinaryHostPad DescentRetainedRangeDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
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
local notation "oldL" => cursor.ports.operandLanes
local notation "roleL" => cursor.ports.roleLanes
local notation "base" => cursor.ports.priorStart k cursor.floor
local notation "history" => (cursor.ports.afterPad k cursor.floor).archive
local notation "outer" => scheduledAtPorts G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor
local notation "a" => (outer).inner
local notation "v" => (a).successor
local notation "menu" => (⟨board,op,g,tail,p,f,drift,degree,payload,seats,ordinary,profile,header⟩ : Menu n h)
local notation "publisher" => priorArchivePhase G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w
variable (capacity : cursor.ports.venue.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)
    (space : ScheduledCodeRoom G S board₀ k tail age p f g drift degree payload ordinary op₀
      (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports.operandLanes cursor.ports.roleLanes
      cursor.ports.venue cursor.ports.io (cursor.ports.priorStart k cursor.floor) w (cursor.ports.afterPad k cursor.floor).archive)
local notation "u" => DatePorts.resetInputs G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w space
local notation "ports" => cursor.ports
local notation "mem₁" m:arg => (publisher).image m
variable {description : BitDescription W} {R : ℕ} (number : Local description)
  (bounds : DatePorts.RangeRoom cursor.ports input description) (shape : WorldShape p R description)
  (label : NodeOrder.All description→Label G (S.firstWidth G.b p) (S.grainAt G.b p 0) op₀)

variable (geo : Geometry G S (⟨board₀,op₀,g,tail,p,f,drift,degree,payload,seats,ordinary,profile,header⟩ : Menu n h) k w age cursor)
    (widths : DatePorts.ArchiveWidths G S op₀ cursor.ports k tail p drift degree payload age)
local notation "phase" => (a).ingress.phase base w (io).hubs (fun x=>(io).atoms x.val)
  (fun j=>(io).wire j.1.val j.2.val)
local notation "atMem" m:arg => (phase).image (mem₁ m)

theorem matched_panel_seven (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (hb : HEq ctl.board board₀) (ho : RotorSpec.ofRates ctl=op₀) (degreeAt : (old).degree=D) (ready : (u).Ready)
    (m : Memory w) (capAt : input.placement.cap=cap)
    (held : MatchedRegisteredOperandPanels board₀ op₀ B p drift degree payload w ordinary seats profile header cursor space
      number bounds shape label geo widths hn hh hf hg ht hb ho degreeAt ready m capAt)
    (publicValues : MatchedPublicRows board₀ op₀ B p drift degree payload w ordinary cursor space
      hn hh hf hg ht hb ho ready m) (small : 2*(v).receiver.candidates<2^(v).receiver.queryBits) :
    ∃after : Memory w,(u).ThroughActors (atMem m) after ∧
      ∃read : ∀i,DatePorts.OrdinalRead (u) ready small after i,
        ∀j x n h gr, ((read ((v).operandOrdinal (u).operand 0 j x n)).amount h gr).val≤2:=by
  obtain ⟨after,exec,values⟩:=matched_panel_tags board₀ op₀ B p drift degree payload w ordinary seats profile header
    cursor space number bounds shape label geo widths hn hh hf hg ht hb ho degreeAt ready m capAt held publicValues small
  exact ⟨after,exec,(u).seven_amount_at_actor values⟩

/-- The same seven words at the snapshot used by a retained or fresh history. -/
theorem matched_seven_at_panel (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (hb : HEq ctl.board board₀) (ho : RotorSpec.ofRates ctl=op₀) (degreeAt : (old).degree=D) (ready : (u).Ready)
    (m : Memory w) (capAt : input.placement.cap=cap)
    (held : MatchedRegisteredOperandPanels board₀ op₀ B p drift degree payload w ordinary seats profile header cursor space
      number bounds shape label geo widths hn hh hf hg ht hb ho degreeAt ready m capAt)
    (publicValues : MatchedPublicRows board₀ op₀ B p drift degree payload w ordinary cursor space
      hn hh hf hg ht hb ho ready m) (small : 2*(v).receiver.candidates<2^(v).receiver.queryBits)
    (actorMem : Memory w) (issued : (u).ThroughActors (atMem m) actorMem) :
    ∃read : ∀i,DatePorts.OrdinalRead (u) ready small actorMem i,
      ∀j x n h gr, ((read ((v).operandOrdinal (u).operand 0 j x n)).amount h gr).val≤2:=by
  obtain ⟨after,exec,read⟩:=matched_panel_seven board₀ op₀ B p drift degree payload w ordinary seats profile header
    cursor space number bounds shape label geo widths hn hh hf hg ht hb ho degreeAt ready m capAt held publicValues small
  have same : after=actorMem:=ProtocolRAM.exec_unique _ _ _ _ exec issued
  exact same ▸ read

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
