import OAI.Hierarchy.DescentPostedRetainedSpans
import OAI.Hierarchy.DescentScheduledPrimaryCensus
import OAI.Hierarchy.DescentNamedRangeAtPublicActor
import OAI.Hierarchy.DescentRegisteredSevenSpans
import OAI.Hierarchy.DescentNamedRangeFields
import OAI.Hierarchy.DescentRegisteredRetainedArgumentFit
import OAI.Hierarchy.DescentScheduledPrimaryDonorRead
import OAI.Hierarchy.DescentMatchedFreshPanelsAt

namespace OAI
/-! The preserved source words for the three chronological reset range fields. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSixParty DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open DescentPackedColony DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
open DescentPackedZip DescentOrdinaryHostPad DescentRetainedRangeDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 1200000
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
variable (capacity : (old).cap=cap)
    (space : ScheduledCodeRoom G S board k tail age p f g drift degree payload ordinary op s₀ Z₀ oldL roleL
      old io base w history)
local notation "u" => DatePorts.resetInputs G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w space
local notation "ports" => cursor.ports
local notation "mem₁" m:arg => (publisher).image m
variable (oldA:Archive W) {R:ℕ} (number : Local oldA.bit)
  (bounds:DatePorts.RangeRoom ports input oldA.bit) (shape:WorldShape p R oldA.bit)
  (label:NodeOrder.All oldA.bit→Label G s₀ Z₀ op)

variable (geo : Geometry G S menu k w age cursor)
    (widths : DatePorts.ArchiveWidths G S op ports k tail p drift degree payload age)
local notation "phase" => (a).ingress.phase base w (io).hubs (fun x=>(io).atoms x.val)
  (fun j=>(io).wire j.1.val j.2.val)
local notation "atMem" m:arg => (phase).image (mem₁ m)


open DescentDatedPriorOperand DescentSixParty.ClosedReset.Window
variable [Fintype P] (paid:B.Recorded p) (hp:0<p) (one:1≤R) (unitPos:0<B.reset.unit)
    (whole:p∣B.reset.unit) (wide:max 1 (max B.reset.width (C*B.reset.width))≤R) (pin:P→ℕ)
local notation "nextB" => (resetArchive B p hp whole oldA).bit
local notation "nextShape" => reset_shape_at hp one B oldA shape unitPos whole wide
local notation "nextNum" => DescentLocalArchiveOrder.reset B p hp whole oldA number
local notation "ports₁" => DatePorts.reset a ((a).stageStart base) u
variable (places:DatePorts.RangeRoom ports₁ B.next nextB)
    (oldArity:∀vertex z₀,((shape.sites vertex).recipe hp).arity z₀≤(ports).argumentsPerNode)
    (newArity:∀vertex z₀,(((nextShape).sites vertex).recipe hp).arity z₀≤(ports₁).argumentsPerNode)
variable (height:0<S.height) (grain:z=S.grainAt G.b p (age+1)) (gain:G.b≤2^S.capGain)
    (sized:(ports).RoleRows) (rolePos:0<(ports).roleLanes) (wBig:payload≤w)
    (population:Fintype.card input.V≤(ports).operandHosts)
    (flags:Fin (2^(old).k)→Fin (ports).nodes→Fin (ports).operandHosts→Fin (old).groups→ℕ)
local notation "ptr" => Reached.argumentPointer input oldA.bit number shape hp pin (ports).argumentsPerNode
include paid oldArity newArity height grain gain sized rolePos wBig population in
theorem matched_seven_spans (hn:n₁=n) (hh:h₁=h) (hf:f₁=f) (hg:g₁=g) (ht:tail₁=tail)
    (hb:HEq ctl.board board₀) (ho:RotorSpec.ofRates ctl=op₀) (degreeAt:(old).degree=D)
    (ready:(u).Ready) (mem:Memory w) (capAt:input.placement.cap=cap) (elapsed:0<age)
    (sorted:SourceSorted W input.order) (actual:DatePorts.ArchiveRead ports input oldA.bit number bounds shape op label ptr flags mem)
    (held:MatchedRegisteredOperandPanels board₀ op₀ B p drift degree payload w ordinary seats profile header cursor space
      number bounds shape label geo widths hn hh hf hg ht hb ho degreeAt ready mem capAt)
    (actorMem:Memory w) (reached:(u).ThroughActors (atMem mem) actorMem)
    (orig:MatchedPublicOriginsAt board₀ op₀ B p drift degree payload w ordinary cursor space
      hn hh hf hg ht hb ho degreeAt ready mem capAt actorMem)
    (earnedWidth:max 1 (max B.reset.width (C*B.reset.width))≤drift)
    (small:2*(v).receiver.candidates<2^(v).receiver.queryBits) (axes:(ports₁).rangeLayout=(v).rangeLayout)
    (choice:∀i,DatePorts.OrdinalRead u ready small actorMem i) :
    DatePorts.SevenSpans u B.next nextB nextNum places nextShape ready small axes actorMem choice ∧
      DatePorts.SevenVacant u B.next nextB nextNum places ready small axes actorMem choice:=by
  let C₀:=(v).setup
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
  have ranges:=DateInputs.range_at_public_actor (B:=B) drift degree payload qcut oldCut (2^qcut) nextLane
    oldL roleL bits₀ old io base w fitted fitted oldFits (history).count (history).nodeBase
    (history).arguments (history).seed (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space)
    degreeAt capAt ready entry _ μ measured actorMem panels origin
  let prior:=ResetOutput.Prior.atDate G S age p drift oldL roleL bits₀ old
  let total:=(S.previousGeometry G k tail₁ drift degree p age payload prior.nodes prior.arguments prior.operandLanes
    ctl.base ctl.radix B.age).1
  have cutEq:C₀.retained.cut=B.terminals.commonDepth:=B.commonDepth.symm
  have previousCapacity v₀:Fintype.card (oldA.bit.recipe v₀).Node≤C₀.retained.previousNodes:=
    (bounds.capacity v₀).trans_eq widths.nodes
  have previousArgs v₀ n₀:((shape.sites v₀).recipe hp).arity n₀≤C₀.retained.previousArgs:=
    (oldArity v₀ n₀).trans_eq geo.arguments
  have roleRoom:(ports).tokenBits*(ports).nodes*(ports).roleLanes≤w:=by
    rw [widths.token]
    exact widths.roles.trans ((Nat.div_le_self ..).trans wBig)
  have bus:(ports).operandBits*(ports).nodes*(ports).operandLanes≤w:=widths.operands.trans ((Nat.div_le_self ..).trans wBig)
  obtain ⟨argPos,argFits⟩:=widths.posted_arguments geo.arguments hp height gain
  have positive:0<(ports).operandBits:=by
    by_contra! zero
    have eqn:(ports).operandBits=0:=Nat.eq_zero_of_le_zero zero
    simp only [eqn,pow_zero] at argFits
    omega
  have original (geom:C₀.MovementShape) (mat:DescentGL.Layout (C₀.retained.high+C₀.retained.low))
      (won:HEq mat B.frame.basis):=
    PhysicalReset.scheduled_primary_donor_read (G:=G) (S:=S) («board»:=ctl.board) (k:=k)
      (tail:=tail₁) (age:=age) (p:=p) (f:=f₁) (gain:=g₁) (drift:=drift) (degree:=degree) (h:=payload)
      (ordinary:=ordinary) («op»:=RotorSpec.ofRates ctl) (s:=S.firstWidth G.b p) (Z:=S.grainAt G.b p 0)
      («ports»:=cursor.ports) (floor:=cursor.floor) (w:=w) (data:=data) (roles:=roles)
      (supportAt:=space) (homes:=geo.room.hosts) (blocks:=geo.format.width) (groups:=geo.room.population.groups)
      (widths:=widths) (args:=geo.arguments) (closed_:=B) (oldA:=oldA) (number:=number) (room:=bounds)
      (spec:=shape) (hp:=hp) (pin:=pin) (label:=label) (flags:=flags) (mem:=mem) (archive:=actual)
      (stored:=stored) (sized:=sized) (alphabet:=widths.token) (rolePos:=rolePos) (roleRoom:=roleRoom)
      (width:=bus) (pop:=population) (positive:=positive) («fits»:=argFits) total cutEq rfl rfl
      geom.size geom.cut input.valid.host previousCapacity previousArgs mat won
  have counts (geom:C₀.MovementShape) (mat:DescentGL.Layout (C₀.retained.high+C₀.retained.low)):=
    PhysicalReset.scheduled_root_counts (G:=G) (S:=S) («board»:=ctl.board) (k:=k)
      (tail:=tail₁) (age:=age) (p:=p) (f:=f₁) (gain:=g₁) (drift:=drift) (degree:=degree) (h:=payload)
      (ordinary:=ordinary) («op»:=RotorSpec.ofRates ctl) (s:=S.firstWidth G.b p) (Z:=S.grainAt G.b p 0)
      («ports»:=cursor.ports) (floor:=cursor.floor) (w:=w) (data:=data) (roles:=roles)
      (supportAt:=space) (homes:=geo.room.hosts) (blocks:=geo.format.width) (groups:=geo.room.population.groups)
      (widths:=widths) (args:=geo.arguments) (input:=input) (oldA:=oldA) (number:=number) (room:=bounds)
      (spec:=shape) (hp:=hp) (pin:=pin) (label:=label) (flags:=flags) (mem:=mem) (archive:=actual)
      (stored:=stored) (sized:=sized) (alphabet:=widths.token) (rolePos:=rolePos) (roleRoom:=roleRoom)
      (pop:=population) (positive:=positive) geom.size geom.cut mat input.valid.host rfl rfl
  exact DateInputs.named_range_fields (B:=B) (accepted:=paid) («base»:=gain) (grainAt:=grain) (oldA:=oldA) (oldNum:=number) (shape:=shape) (hp:=hp)
    (one:=one) (unitPos:=unitPos) (whole:=whole) (widthBound:=wide) (pin:=pin)
    (ready:=ready) (actorMem:=actorMem) (small:=small) (axes:=axes) (choices:=choice) (places:=places)
    (previousCapacity:=previousCapacity) (previousArgs:=previousArgs)
    (μ:=μ) (measured:=measured) (degreeAt:=degreeAt) (capAt:=capAt) (rangeRows:=ranges)
    (original:=origin) (elapsed:=elapsed) (sorted:=sorted) (earnedWidth:=earnedWidth)
    (previousRows:=original) (counts:=counts)

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
