import OAI.Hierarchy.DescentPostedRetainedHeaders
import OAI.Hierarchy.DescentRegisteredRetainedArgumentFit
import OAI.Hierarchy.DescentScheduledPrimaryDonorRead
import OAI.Hierarchy.DescentMatchedFreshPanelsAt

namespace OAI
/-! Every retained formal argument in the reached chronological reset publication. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSixParty DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open DescentPackedColony DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
open DescentPackedZip DescentOrdinaryHostPad DescentRetainedRangeDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1300000
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
variable (oldA:Archive W) {R:ℕ} (number : Local oldA.bit)
  (bounds:DatePorts.RangeRoom cursor.ports input oldA.bit) (shape:WorldShape p R oldA.bit)
  (label:NodeOrder.All oldA.bit→Label G (S.firstWidth G.b p) (S.grainAt G.b p 0) op₀)

variable (geo : Geometry G S (⟨board₀,op₀,g,tail,p,f,drift,degree,payload,seats,ordinary,profile,header⟩ : Menu n h) k w age cursor)
    (widths : DatePorts.ArchiveWidths G S op₀ cursor.ports k tail p drift degree payload age)
local notation "phase" => (a).ingress.phase base w (io).hubs (fun x=>(io).atoms x.val)
  (fun j=>(io).wire j.1.val j.2.val)
local notation "atMem" m:arg => (phase).image (mem₁ m)


open DescentDatedPriorOperand DescentSixParty.ClosedReset.Window
variable [fintypePins : Fintype P] (paid:B.Recorded p) (hp:0<p) (one:1≤R) (unitPos:0<B.reset.unit)
    (whole:p∣B.reset.unit) (wide:max 1 (max B.reset.width (C*B.reset.width))≤R) (pin:P→ℕ)
local notation "nextB" => (resetArchive B p hp whole oldA).bit
local notation "nextShape" => reset_shape_at hp one B oldA shape unitPos whole wide
local notation "nextNum" => DescentLocalArchiveOrder.reset B p hp whole oldA number
local notation "ports₁" => DatePorts.reset a ((a).stageStart base) u
variable (places : DatePorts.RangeRoom
    (DatePorts.reset (scheduledAtPorts G S board₀ k tail age p f g drift degree payload ordinary op₀
      (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports cursor.floor).inner
      ((scheduledAtPorts G S board₀ k tail age p f g drift degree payload ordinary op₀
        (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports cursor.floor).inner.stageStart (cursor.ports.priorStart k cursor.floor))
      (DatePorts.resetInputs G S board₀ k tail age p f g drift degree payload ordinary op₀
        (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports cursor.floor w space))
    B.next (resetArchive B p hp whole oldA).bit)
    (oldArity:∀host z₀,((shape.sites host).recipe hp).arity z₀≤cursor.ports.argumentsPerNode)
    (newArity:∀host z₀,(((reset_shape_at hp one B oldA shape unitPos whole wide).sites host).recipe hp).arity z₀≤(DatePorts.reset (scheduledAtPorts G S board₀ k tail age p f g drift degree payload ordinary op₀
      (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports cursor.floor).inner
      ((scheduledAtPorts G S board₀ k tail age p f g drift degree payload ordinary op₀
        (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports cursor.floor).inner.stageStart (cursor.ports.priorStart k cursor.floor))
      (DatePorts.resetInputs G S board₀ k tail age p f g drift degree payload ordinary op₀
        (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports cursor.floor w space)).argumentsPerNode)
variable (height:0<S.height) (grain:z=S.grainAt G.b p (age+1)) (gain:G.b≤2^S.capGain)
    (sized:cursor.ports.RoleRows) (rolePos:0<cursor.ports.roleLanes) (wBig:payload≤w)
    (population:Fintype.card input.V≤cursor.ports.operandHosts)
    (flags:Fin (2^cursor.ports.venue.k)→Fin cursor.ports.nodes→Fin cursor.ports.operandHosts→Fin cursor.ports.venue.groups→ℕ)
local notation "ptr" => Reached.argumentPointer input oldA.bit number shape hp pin cursor.ports.argumentsPerNode
include fintypePins paid oldArity newArity height grain gain sized rolePos wBig population in
omit fintypePins in
theorem matched_retained_headers (hn:n₁=n) (hh:h₁=h) (hf:f₁=f) (hg:g₁=g) (ht:tail₁=tail)
    (hb:HEq ctl.board board₀) (ho:RotorSpec.ofRates ctl=op₀) (degreeAt:(old).degree=D)
    (ready:(u).Ready) (mem:Memory w) (capAt:input.placement.cap=cap)
    (actual:DatePorts.ArchiveRead ports input oldA.bit number bounds shape op label ptr flags mem)
    (held:MatchedRegisteredOperandPanels board₀ op₀ B p drift degree payload w ordinary seats profile header cursor space
      number bounds shape label geo widths hn hh hf hg ht hb ho degreeAt ready mem capAt)
    (actorMem:Memory w) (reached:(u).ThroughActors (atMem mem) actorMem)
    (orig:MatchedPublicOriginsAt board₀ op₀ B p drift degree payload w ordinary cursor space
      hn hh hf hg ht hb ho degreeAt ready mem capAt actorMem)
    (small:2*(v).receiver.candidates<2^(v).receiver.queryBits) (axes:(ports₁).rangeLayout=(v).rangeLayout)
    (choice:∀i,DatePorts.OrdinalRead u ready small actorMem i) :
    DatePorts.SevenOriginHeaders u B.next nextB nextNum places nextShape hp pin ready small axes actorMem choice
      (resetOrigin B hp whole oldA) Sum.inl:=by
  let qcut:=rcut
  let oldCut:=oldExp
  let nextLane:=nextM
  let bits₀:=token
  let entry:=(publisher).image mem
  have fitted:=fits
  have oldFits:=priorFits
  subst n
  subst h
  subst f
  subst g
  subst tail
  have sameBoard:ctl.board=board₀:=eq_of_heq hb
  subst board₀
  subst op₀
  obtain ⟨data,roles,stored,panels⟩:=held
  obtain ⟨μ,measured,origin⟩:=orig
  have rows:=DateInputs.public_rows_of_origins (B:=B) drift degree payload qcut oldCut (2^qcut) nextLane oldL roleL
    bits₀ old io base w fitted fitted oldFits (history).count (history).nodeBase (history).arguments (history).seed
    (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space) degreeAt ready entry capAt origin
  apply DateInputs.registered_retained_headers (accepted:=paid) (B:=B)
    (oldA:=oldA) (oldNum:=number) (shape:=shape) (hp:=hp) (one:=one) (unitPos:=unitPos) (whole:=whole)
    (widthBound:=wide) (pin:=pin) (ready:=ready) (actorMem:=actorMem) (small:=small) (axes:=axes) (choices:=choice)
    (places:=places) (previousCapacity:=fun u₀=>(bounds.capacity u₀).trans_eq widths.nodes)
    (previousArgs:=fun u₀ n₀=>(oldArity u₀ n₀).trans_eq geo.arguments) (arity:=newArity)
    (degreeAt:=degreeAt) (capAt:=capAt) (height:=height) («base»:=gain) (grainAt:=grain)
    (m:=entry) (held:=panels) (reached:=reached) (public_:=rows)
  intro geometry mat won
  have words:=PhysicalReset.scheduled_primary_donor_read (closed_:=B) (oldA:=oldA) (number:=number)
    (room:=bounds) (spec:=shape) (hp:=hp) (pin:=pin) (label:=label) (flags:=flags) (mem:=mem)
    (archive:=actual) (stored:=stored) (sized:=sized) (alphabet:=widths.token)
    (rolePos:=rolePos) (roleRoom:=by rw [widths.token];exact widths.roles.trans ((Nat.div_le_self ..).trans wBig))
    (width:=widths.operands.trans ((Nat.div_le_self ..).trans wBig)) (pop:=population)
    (positive:=by rw [widths.digits];exact lt_of_lt_of_le (by decide:0<2) ((DescentOperandWidth.wide ..).trans (Nat.le_max_left ..)))
    («fits»:=(widths.posted_arguments geo.arguments hp height gain).2)
  apply words
  exact won

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
