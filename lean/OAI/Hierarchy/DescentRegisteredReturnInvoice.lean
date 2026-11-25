import OAI.Hierarchy.DescentFundedSignedReturn
import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentOrdinaryMarkIssuedRoom

namespace OAI
/-! # The first four literal terms of the registered date's paid instruction stream -/

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage DescentDatedAddressBook ProtocolRAM
noncomputable section
variable {F P : Type} [Field F]

def issuedPrefix (v : PhysicalOrdinary F P) (floor w : ℕ) (parts adj : Bank)
    (old : DescentOrdinaryVenueReturn.Sources) (input : Dated.Operands) (c : v.SignedChart) : NativePhase w :=
  let peers:=DescentOrdinaryVenueReturn.phase old (v.materialEnd floor) v.k v.area.H v.area.D v.venue.hosts v.venue.degree w
  (((v.beforeSignedMaterial floor parts adj w).seq peers).seq (v.mark floor input w)).seq (v.signedPhase floor c w)

theorem issuedPrefix_same {u v : PhysicalOrdinary F P} (eqn : u=v) (floor w : ℕ) (parts adj : Bank)
    (old : DescentOrdinaryVenueReturn.Sources) (input : Dated.Operands) (a : u.SignedChart) (c : v.SignedChart) :
    u.issuedPrefix floor w parts adj old input a=v.issuedPrefix floor w parts adj old input c :=by
  cases eqn
  rfl

variable (v : PhysicalOrdinary F P) (port : DatePorts) (installed : ℕ)
local notation "Y" => v.registeredFrom port installed

theorem registered_issued_signed (same : v.withIssuedSigned=v) : (Y).withIssuedSigned=Y:=by
  have selected:=congrArg (fun state : PhysicalOrdinary F P=>state.signed) same
  change v.signedLayout.format v.payload=v.signed at selected
  change {Y with signed:=v.signedLayout.format v.payload}=Y
  rw [selected]
  rfl

set_option maxHeartbeats 1200000 in
theorem registered_return_invoice (floor w : ℕ) (parts adj : Bank) (old : DescentOrdinaryVenueReturn.Sources)
    (input : Dated.Operands) (c : (Y).SignedChart) (same : v.withIssuedSigned=v) :
    let peers:=DescentOrdinaryVenueReturn.phase old ((Y).materialEnd floor) (Y).k (Y).area.H (Y).area.D (Y).venue.hosts (Y).venue.degree w
    ((Y).beforeSignedMaterial floor parts adj w).wordInvoice+peers.wordInvoice+
      ((Y).mark floor input w).wordInvoice+((Y).signed.phase ((Y).signedInput floor c) ((Y).markEnd floor) w).wordInvoice =
    (v.signedReturnPrefix floor w parts adj old input).wordInvoice :=by
  intro peers
  have fixed:=v.registered_issued_signed port installed same
  have one:=issuedPrefix_same fixed floor w parts adj old input (Y).issuedSignedChart c
  have actual : (Y).signedReturnPrefix floor w parts adj old input=v.signedReturnPrefix floor w parts adj old input:=by
    unfold signedReturnPrefix
    apply congrArg₂ NativePhase.seq
    · apply congrArg₂ NativePhase.seq
      · apply congrArg₂ NativePhase.seq
        · rfl
        · rfl
      · rfl
    · rfl
  change ((Y).withIssuedSigned.issuedPrefix floor w parts adj old input (Y).issuedSignedChart)=
    (Y).issuedPrefix floor w parts adj old input c at one
  calc
    _ = ((Y).issuedPrefix floor w parts adj old input c).wordInvoice :=by
      simp only [issuedPrefix, NativePhase.wordInvoice_seq]
      rfl
    _ = _ := (congrArg NativePhase.wordInvoice one.symm).trans (congrArg NativePhase.wordInvoice actual)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
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
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height




open Filter

include before tail cut in
theorem registered_return_funded (books : OrdinaryBooks) (frozen payload seats hostLanes : ℕ) (old : ProtocolRAM.Bank)
    (ordinary : ℕ→Ordinary) {t reset J M tailSize : ℕ}
    (cal : S=stageNumbers G t J f g reset M tailSize)
    (kfit : k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (floor w ratio : ℕ) (parts adj : ProtocolRAM.Bank) (oldSources : DescentOrdinaryVenueReturn.Sources)
    (input : Operands) (oldRoom : 2*scale J (donorRates G t f g reset).amount≤payload)
    (newRoom : 2*scale J (signedRates G t f g reset).amount≤payload)
    (bus : w≤ratio*payload) (calibrated : Funding G t f g reset ratio payload)
    (age : J≤Nat.log 2 payload) (size : 2^payload≤2*M) (port : DatePorts) (installed : ℕ) :
    let v:=books.onTicket ticket g frozen p f payload seats hostLanes old ordinary
    let Y:=v.registeredFrom port installed
    let peers:=DescentOrdinaryVenueReturn.phase oldSources (Y.materialEnd floor) Y.k Y.area.H Y.area.D Y.venue.hosts Y.venue.degree w
    let R:=ratio*scale J (Chronology.returnRate G t f g reset)
    ∀ (c : Y.SignedChart), Y.area.Space input w floor → Y.SignedRoom floor w →
      (Y.beforeSignedMaterial floor parts adj w).wordInvoice+peers.wordInvoice+
        (Y.mark floor input w).wordInvoice+(Y.signed.phase (Y.signedInput floor c) (Y.markEnd floor) w).wordInvoice ≤
        S.hostSize i*payload*(R+1)+S.hostSize i*(S.groupCount i*S.radix)*R :=by
  intro v Y peers R chart matcher signed
  have correct:=(issued_return_fields X G S br ticket before tail cut books frozen payload seats hostLanes old ordinary).2.2.2
  have room:=Y.mark_room_of_signed floor input matcher signed (v.registered_issued_signed port installed correct) radix
  have originalRoom : v.MarkRoom floor input w :=
    ⟨room.lanes,room.blocks,room.visited,room.rosterSize,room.wires,room.sourceSize,room.room⟩
  rw [v.registered_return_invoice port installed floor w parts adj oldSources input chart correct]
  exact named_return_funded X G S br ticket before tail cut books frozen payload seats hostLanes old ordinary
    cal kfit floor w ratio parts adj oldSources input oldRoom newRoom bus calibrated age size originalRoom

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
