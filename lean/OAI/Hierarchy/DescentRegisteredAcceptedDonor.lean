import OAI.Hierarchy.DescentOrdinaryHeldPrivate
import OAI.Hierarchy.DescentRegisteredOrdinaryMeterRoom
import OAI.Hierarchy.DescentNamedRegisteredObservation
import OAI.Hierarchy.DescentRegisteredDrawPins
import OAI.Hierarchy.DescentRegisteredSelectedBoard
import OAI.Hierarchy.DescentRegisteredSignedBeforeFull
import OAI.Hierarchy.DescentRegisteredMatcherGeometry

namespace OAI
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
open scoped Classical Fin.CommRing
set_option maxHeartbeats 1400000
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "s" => S.firstWidth G.b p
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook
variable {n₀ δ : ℕ} (board : NonlinearExpanders.Graph n₀ δ) (op : RotorSpec)
    (frozen drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial

open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall
local notation "pitch" => DescentPackedEpochShelves.grain (payload/2) G.C
local notation "issue" => RegisterTimeline.issued (w:=w) traces menu
local notation "cpu" => RegisterTimeline.instruction (w:=w) traces menu initial


open DescentCompiler.TerminalScale DescentGroupPeerOrder DescentStageEdgeReceipt
open DescentColonies DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentGroupPeerOrder DescentHaloWalkRAM
local notation "v₂" i:arg tick:arg => DatePorts.ordinaryModel (cursor i).ports tick op g frozen p f drift degree
  payload ((menu).seats i) (cursor i).floor (menu).ordinary
local notation "liveCPU" => DateCode.history cpu


local notation "walk₀" z => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow z

open Lean Elab Term in
local elab "applyDonorArguments% " f:term:arg "[" xs:term,* "]" : term => do
  let fn ← elabTerm f none
  return mkAppN fn (← xs.getElems.mapM fun x => elabTerm x none)

/-- A truthful accepted ordinary ballot produces the actual static donor bank
on the registered CPU, including every original matched pair and all padding. -/
theorem accepted_at_donor_and_meter (protected_ : ∀j,RegisterTimeline.Protected (cpu j) (cursor j).floor header)
    (beforeHeader : lo+extent pitch (ch).layout≤header) (lower : header< initial.floor)
    (votes : (ch).Pin→Bool) (m : Memory w)
    (original : ∀a∈shelves pitch lo 0 (ch).layout,∀j:Fin (slots a.src.seats pitch),
      m (a.base+j.val)=((packed a.src.pin votes pitch j.val).val:Word w))
    {W : MarkedWorld F 0 pins widths} {i z D z' D' : ℕ} {rate : ℝ} {nonneg : 0 ≤ fee}
    {prior : Reached W G price fee S k i z D (S.epochPower^S.priceExponent) s} {T : StageInput W G rate fee}
    {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' (S.epochPower^S.priceExponent) s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path (trace (walk₀ votes)).origin.source prior) (after : Path next (trace (walk₀ votes)).target)
    (located : (before.ordinary ticket).append after=(trace (walk₀ votes)).path)
    (accepted : before.selections.length+1<((ch).rows votes).length ∨ (ch).read votes=some (walk₀ votes))
    (codeRoom : DatePorts.OrdinaryCodeRoom (cursor i).ports ticket op g frozen p f drift degree payload
      ((menu).seats i) (cursor i).floor (menu).ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom (cursor i).ports ticket op g frozen p f drift degree payload
      ((menu).seats i) (cursor i).floor (menu).ordinary w ((menu).profile i) header codeRoom)
    (cells : RegisterTimeline.Geometry G S menu k w i (cursor i))
    (old : (cursor i).ports.held prior (cursor i).floor (liveCPU m i))
    (height : 0<S.height) (age : i<S.length) (floorFit : (cursor i).floor<2^w)
    (keys : S.groupCount i*hostRows (S.hostSize i)*S.radix<2^w)
    (counts : (S.groupCount i*hostRows (S.hostSize i)*S.radix)*2^(8+S.capGain*i)<2^w)
    (grainRoom : 2*DescentPackedEpochShelves.unit G.C≤payload/2)
    (layoutRoom : (menu).seats i*(G.C+8+8*G.k)<2^w) :
    let v:=v₂ i ticket
    let c:=(cursor i)
    let A:=(OrdinaryBooks.atDate G S op g k i p frozen drift degree payload ((menu).seats i) c.ports).onTicket
      ticket g frozen p f payload ((menu).seats i) c.ports.venue.lanes c.ports.io.roster (menu).ordinary
    let panel:=(A.registeredEntry c.ports (A.stageStart c.floor)).venue.panel
    let state:=DatePorts.ordinaryDonorMemory c.ports ticket op g frozen p f drift degree payload ((menu).seats i)
      c.floor (menu).ordinary w ((menu).profile i) header prior.placement.fieldBits codeRoom exec (liveCPU m i)
    ∃(wide:Fintype.card prior.V≤v.area.H) (pick:(prior.placement.stage.result nonneg).Choice),
      HEq choice pick ∧ Nonempty (v.SelectedBoard wide
        (hostRotor (GroupStage.plane v.hostNumbers wide)
          (hostRoster prior.placement ((GroupStage.plane v.hostNumbers wide).trans Fin.valEmbedding))) pick state panel) ∧ (before.Held header (liveCPU m i) →
        (before.ordinary ticket).Held header (DatePorts.ordinaryOutput c.ports ticket op g frozen p f drift degree
          payload ((menu).seats i) c.floor (menu).ordinary w ((menu).profile i) header prior.placement.fieldBits
          codeRoom exec (liveCPU m i))) :=by
  let walk:=walk₀ votes
  let V:=v₂ i ticket
  let point:=cursor i
  let date:=DonorDate.atDate G S g k i p
  let root:=point.floor
  let floor₁:=V.stageStart root
  let booked:= (menu).seats i
  let planned:=date.schedule payload booked (S.censusBits p)
  let rotation:=planned.rotationEnd point.ports.io.roster floor₁
  let physical := applyDonorArguments% (@registered_physical_report) [
    F, (inferInstance : Field F), cp, nP, X, G, S, k, cut, tail, n, h, C, f, g, p,
    ordinary, reset, branch, positive, room, shorten, w, fit, n₀, δ, board, op,
    frozen, drift, degree, payload, lo, header, initial, protected_, beforeHeader, lower,
    votes, m, original, walk, W, i, z, D, z', D', rate, nonneg, prior, T, choice, norm, next,
    ticket, before, after, located, codeRoom, exec, cells, old, height, age, floorFit, keys, counts, grainRoom]
  let e := physical.choose
  let wide := physical.choose_spec.choose
  let pick := physical.choose_spec.choose_spec.choose
  let ext := physical.choose_spec.choose_spec.choose_spec.choose
  have observed := physical.choose_spec.choose_spec.choose_spec.choose_spec
  have hit := observed.1
  have hp := observed.2.1
  have venue := observed.2.2.2.1
  have report := observed.2.2.2.2
  let draw := applyDonorArguments% (@DatePorts.registered_draw_pins) [
    F, (inferInstance : Field F), cp, nP, X, G, S, k, cut, tail, n, h, C, f, g, p,
    ordinary, reset, branch, positive, room, shorten, w, fit, votes, W, i, z, D, z', D',rate,
    nonneg, prior, T, choice, norm, next, ticket, before, after, located, accepted,
    point.ports, op, frozen, drift, degree, payload, booked, root, (menu).ordinary, e, hit, wide, ext]
  have same : draw.choose = pick := eq_of_heq (draw.choose_spec.1.symm.trans hp)
  let recordedPins := fun (selected : (prior.placement.stage.result nonneg).Choice) =>
    ∀ j,(DescentPackedProfileWide.wideCell e.pin votes V.area.shapeAt.digit ext j).val =
      DescentTerminalEpochDecoder.profileAt
        (DescentPacking.PackedMatch.Local.inputNumber nonneg prior.placement (Equiv.refl _).toEmbedding
          (GroupStage.plane V.hostNumbers wide))
        ((DescentKernelHistory.BitDescription.scannedRows nonneg prior.placement.stage).profile selected) j
  have pinsAt : recordedPins pick := Eq.mp (congrArg recordedPins same) draw.choose_spec.2
  let recorded := applyDonorArguments% (@profile_on_cpu) [
    F, (inferInstance : Field F), cp, nP, X, G, S, k, cut, tail, n, h, C, f, g, p,
    ordinary, reset, branch, positive, room, shorten, w, fit, n₀, δ, board, op,
    frozen, drift, degree, payload, lo, header, initial, protected_, beforeHeader, lower,
    votes, m, original, walk, W, i, z, D, z', D',rate, nonneg, prior, T, choice, norm, next,
    ticket, before, after, located, floorFit]
  have seatsEq := recorded.choose_spec.2.2.1
  have seated := recorded.choose_spec.2.2.2.2.1
  let name:=GroupStage.plane V.hostNumbers wide
  have originalNames:=(trace walk).origin.names_on_path before
  have named : name.trans Fin.valEmbedding=prior.vertex.trans Fin.valEmbedding:=by ext a;rfl
  have nt:=originalNames.1
  have placed : prior.placement.SiteNamed
      (groupRank ((Equiv.refl (Fin (S.groupCount i))).toEmbedding.trans Fin.valEmbedding) (name.trans Fin.valEmbedding)):=by
    rw [named];exact nt
  have dated:=Branch.donor_date_eq X G S (trace walk) ticket before after located
  have geometry:V.area=planned:=Branch.registered_matcher_shape X G S (trace walk) ticket before after located
    op frozen drift degree payload booked root point.ports (menu).ordinary
  have low:initial.floor≤root:=by
    change initial.floor≤(RegisterTimeline.position issue initial i).floor
    rw [RegisterTimeline.position_floor]
    exact DescentDatedAddressBook.floor_mono _ _ (Nat.zero_le i)
  have window:root≤floor₁:=by change root≤V.profileRepack.endAddress root;rw [V.profileRepack.translate];exact Nat.le_add_right ..
  have rotationLow:floor₁≤rotation:=by
    have h:=planned.rotation_add point.ports.io.roster 0 floor₁
    simp only [Nat.add_zero] at h
    rw [show rotation=planned.rotationEnd point.ports.io.roster floor₁ from rfl,h]
    exact Nat.le_add_right ..
  have positiveAmount:0<date.amount:=(Nat.succ_pos _).trans_le ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  have wordPos:0<payload:=by
    have h:=exec.matcher.laneWidth
    change 2*date.amount≤payload at h
    omega
  have span:ticket.wholeDonorEnd V.short V.profile V.area.H payload rotation=V.donorEnd floor₁:=by
    change ticket.wholeDonorEnd V.short V.profile V.area.H payload rotation=
      ticket.wholeDonorEnd V.short V.profile V.area.H payload (V.area.rotationEnd point.ports.io.roster floor₁)
    rw [geometry]
  have stops:=V.signed_stage_paid floor₁
  have signedPaid:V.donorEnd floor₁≤V.signedEnd floor₁:=stops.1.trans (stops.2.1.trans stops.2.2)
  have paid:=signedPaid.trans (V.signed_before_full root)
  have measured:=DatePorts.selected_meter_at_donor point.ports ticket op g frozen p f drift degree payload booked root
    (menu).ordinary w ((menu).profile i) header prior.placement.fieldBits codeRoom exec (liveCPU m i) pick e votes
    wide ext report pinsAt hp ⟨placed,originalNames.2⟩
    ((Nat.mul_le_mul_right _ (seated.trans_eq seatsEq)).trans_lt layoutRoom) venue dated geometry
    (lower.le.trans (low.trans (window.trans rotationLow))) positiveAmount (Nat.le_mul_of_pos_right w wordPos)
    (span.le.trans (paid.trans exec.limit.le)) (ticket.quantum.symm.trans (ticket.grain_on_cut before after located (trace walk).issuedGrains))
  refine ⟨wide,pick,hp,measured.1,?_⟩
  intro charged
  have roof:=Branch.ordinary_meter_roof X G S (trace walk) ticket before after located op frozen drift degree
    payload booked root point.ports (menu).ordinary header
  exact DatePorts.ordinary_held_of_rows point.ports ticket op g frozen p f drift degree payload booked root
    (menu).ordinary w ((menu).profile i) header prior.placement.fieldBits codeRoom exec (liveCPU m i) measured.2
    before charged (lower.trans_le low) (window.trans rotationLow) roof.2.2

theorem accepted_at_donor (protected_ : ∀j,RegisterTimeline.Protected (cpu j) (cursor j).floor header)
    (beforeHeader : lo+extent pitch (ch).layout≤header) (lower : header< initial.floor)
    (votes : (ch).Pin→Bool) (m : Memory w)
    (original : ∀a∈shelves pitch lo 0 (ch).layout,∀j:Fin (slots a.src.seats pitch),
      m (a.base+j.val)=((packed a.src.pin votes pitch j.val).val:Word w))
    {W : MarkedWorld F 0 pins widths} {i z D z' D' : ℕ} {rate : ℝ} {nonneg : 0 ≤ fee}
    {prior : Reached W G price fee S k i z D (S.epochPower^S.priceExponent) s} {T : StageInput W G rate fee}
    {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' (S.epochPower^S.priceExponent) s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path (trace (walk₀ votes)).origin.source prior) (after : Path next (trace (walk₀ votes)).target)
    (located : (before.ordinary ticket).append after=(trace (walk₀ votes)).path)
    (accepted : before.selections.length+1<((ch).rows votes).length ∨ (ch).read votes=some (walk₀ votes))
    (codeRoom : DatePorts.OrdinaryCodeRoom (cursor i).ports ticket op g frozen p f drift degree payload
      ((menu).seats i) (cursor i).floor (menu).ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom (cursor i).ports ticket op g frozen p f drift degree payload
      ((menu).seats i) (cursor i).floor (menu).ordinary w ((menu).profile i) header codeRoom)
    (cells : RegisterTimeline.Geometry G S menu k w i (cursor i))
    (old : (cursor i).ports.held prior (cursor i).floor (liveCPU m i))
    (height : 0<S.height) (age : i<S.length) (floorFit : (cursor i).floor<2^w)
    (keys : S.groupCount i*hostRows (S.hostSize i)*S.radix<2^w)
    (counts : (S.groupCount i*hostRows (S.hostSize i)*S.radix)*2^(8+S.capGain*i)<2^w)
    (grainRoom : 2*DescentPackedEpochShelves.unit G.C≤payload/2)
    (layoutRoom : (menu).seats i*(G.C+8+8*G.k)<2^w) :
    let v:=v₂ i ticket
    let c:=(cursor i)
    let A:=(OrdinaryBooks.atDate G S op g k i p frozen drift degree payload ((menu).seats i) c.ports).onTicket
      ticket g frozen p f payload ((menu).seats i) c.ports.venue.lanes c.ports.io.roster (menu).ordinary
    let panel:=(A.registeredEntry c.ports (A.stageStart c.floor)).venue.panel
    let state:=DatePorts.ordinaryDonorMemory c.ports ticket op g frozen p f drift degree payload ((menu).seats i)
      c.floor (menu).ordinary w ((menu).profile i) header prior.placement.fieldBits codeRoom exec (liveCPU m i)
    ∃(wide:Fintype.card prior.V≤v.area.H) (pick:(prior.placement.stage.result nonneg).Choice),
      HEq choice pick ∧ Nonempty (v.SelectedBoard wide
        (hostRotor (GroupStage.plane v.hostNumbers wide)
          (hostRoster prior.placement ((GroupStage.plane v.hostNumbers wide).trans Fin.valEmbedding))) pick state panel) :=by
  obtain ⟨wide,pick,hp,board,_⟩:=accepted_at_donor_and_meter X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial protected_ beforeHeader lower votes m original ticket before after located
    accepted codeRoom exec cells old height age floorFit keys counts grainRoom layoutRoom
  exact ⟨wide,pick,hp,board⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
