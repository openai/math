import OAI.Hierarchy.DescentPackedChooserAny
import OAI.Hierarchy.DescentPackedMatchAny
import OAI.Hierarchy.DescentPackedCensusAny
import OAI.Hierarchy.DescentOrdinaryImageIssue
import OAI.Hierarchy.DescentPackedMatchPins
import OAI.Hierarchy.DescentPackedOrdinaryCPU
import OAI.Hierarchy.DescentPackedCensusReady

namespace OAI
/-! # Ordinary matching from the previous funded atoms, scalar host flags and signed cables -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentCompiler DescentSixParty DescentStageEdgeReceipt DescentKernelHistory.BitDescription
open DescentSIMDLookup DescentPackedColony DescentTerminalEpochDecoder DescentPackedProfileWindow
open DescentSixParty.Chronology DescentTerminalEpochChart DescentPackedProfileArchive DescentPackedProfileWide
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentSixParty.StarKeys
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k age L G ℓ w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : AtomSchedule) (ready : A.StateBounds S age)
  (he : 0≤ε) (groups : J≃Fin G) (hosts : V≃Fin L) (hv : L≤2^ℓ) (C : Chooser.Layout)
  (b payload unit ratio profile seats romBase : ℕ)
local notation "H" => 2^ℓ
local notation "M" => lanes payload unit
local notation "gid" => groups.toEmbedding
local notation "vid" => GroupStage.plane hosts hv
local notation "rank" => groupRank ((gid).trans Fin.valEmbedding) ((vid).trans Fin.valEmbedding)
local notation "rdx" => 2^k
local notation "cap2" => 2*A.cap
local notation "K" => 2^(k+1)
local notation "panelBits" => max (k+3) (Nat.clog 2 (A.degree+1))
local notation "s" => shape rdx A.degree cap2 profile
local notation "grain" => M*(s).pairs
variable (P₀ : Ports A.degree) (act : Bank) (wire : Fin (2^k)→Fin (2*A.cap)→Bank)
local notation "vals" => C.winners A.degree k b H G M
local notation "base" => Prepare.ROM.sortBase romBase k A.degree A.cap (k+3) M H G
local notation "bits_" => Prepare.bits H G M
local notation "outB" => Prepare.rosterBank base H A.degree
local notation "nextBase" => Prepare.next k H G M A.degree A.cap base
local notation "prep" => Prepare.ROM.chart romBase A.degree (k+3) M bits_ act vals wire
local notation "sort_" => Prepare.ROM.roster romBase k A.degree A.cap (k+3) M H G (Prepare.ROM.headBits H A.degree) P₀.roster
local notation "ps" => Prepare.passes prep sort_ base H G M A.degree
local notation "wins_" => Prepare.gatedBank (k:=k) base H G M A.degree bits_
local notation "marks_" => Prepare.markedBank (k:=k) (cap:=A.cap) base H G M A.degree bits_
local notation "field" => Gather.expr wins_ marks_ {P₀ with roster:=outB} H
local notation "donor" => Gather.ROM.donorExpr s panelBits rdx A.degree cap2 K H G M unit nextBase seats field
local notation "plan" => Gather.ROM.place s panelBits rdx A.degree cap2 K H G M unit nextBase seats
local notation "stamp" => Prepare.ROM.program w romBase k A.degree A.cap (k+3) panelBits M H G
local notation "matcher" => Gather.ROM.machine s panelBits rdx A.degree cap2 A.cap K H G M unit nextBase seats w field
local notation "warm" => (stamp).seq (ProtocolRAM.program w ps)
local notation "before" => C.program A.degree k b cap2 H G M w
local notation "time₀" => C.ticks A.degree k b cap2 H G M w
local notation "time₁" => ((4+10*Prepare.staticWords k A.degree A.cap (k+3) M H G)+ProtocolRAM.clock ps)+
  Gather.ROM.ticks s panelBits rdx A.degree cap2 K H G M unit nextBase seats field
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home

variable (origin : ℕ) (hubBank : Bank) (atom : Fin (2^k)→Expr)
local notation "liveRows" => H*chunks G M
local notation "col" => Census.order rdx A.cap
local notation "startSum" => Census.beginSum origin H G M
local notation "oldBits" => fun i=>(Census.width A.degree A.cap b ((col).symm i))
local notation "func" => fun i=>(Census.contribution A.degree A.cap b ((col).symm i))
local notation "src" => fun i=>(Census.expr (Census.Broadcast.result hubBank origin H G M) atom
  (fun x j=>Expr.lookup (wire x j) .row) ((col).symm i))
local notation "outBits" => (1+b+2*cap2)*rdx
local notation "header" => DescentStaticWordColumn.program w origin (Census.Broadcast.literal H G M) (2*liveRows)
local notation "sumCPU" => DescentPackedColumnSum.program w startSum C.source.base unit M outBits H G oldBits func src
local notation "initCPU" => (header).seq sumCPU
local notation "timeInit" => (4+10*(2*liveRows))+DescentPackedColumnSum.ticks startSum unit M H G oldBits src

/-- One physical return contains the elected multiplier and paint, the full matching
topology, the profile of each genuine pair and the frame of the original memory. -/
def GuardProfiles (ok : Option Prop) (result : Prop) : Prop :=
  match ok with
  | none=>result
  | some predicate=>predicate → result

def ObservedReport (ok : Option Prop) (choice : (A.stage.result he).Choice) (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree)
    (m : Memory w) (machine : Procedure w) (steps : ℕ) (protectedAt : ℕ→Prop) : Prop :=
    ∃out : Memory w,∃i : Fin (2^k-1),∃j : DescentAffineColors.Candidate k,∃hm : 0<M,
      let posted:=A.publishedTicket groups hosts rs i j
      let win:=fun h : J×V=>posted (vid h.2) (gid h.1)
      let terrain_:=terrain (short:=panelBits) A native S ready (cableNames k rank) win (rotor A rank)
      let keys:=topologyWords («M»:=M) s (Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap (spread gid vid terrain_)))
      machine.Exec m out steps ∧
      DescentColonies.seedAt k i=(scannedRows he A.stage).μ ∧
      j=DescentAffineColors.code (scannedRows he A.stage).α (scannedRows he A.stage).β ∧
      out (C.shelves A.degree k b M).mu=(i.val:Word w) ∧ out (C.shelves A.degree k b M).paint=(j.val:Word w) ∧
      (∀u,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (home u)).2+(color u).toNat) ∧
      Rails {P₀ with roster:=outB} wins_ marks_ (spread gid vid terrain_)
        (hostRotor vid (DescentGroupPeerOrder.hostRoster A ((vid).trans Fin.valEmbedding))) M nextBase out ∧
      Gather.ROM.DonorWord («M»:=M) donor (plan).source.base (spread gid vid terrain_) out ∧
      (∀q,out ((plan).layout.topology.base+q.val)=((keys q).val:Word w)) ∧
      GuardProfiles ok (∀c : ScanColonies he A.stage,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
        let ordinal:=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val
        let place:=slot he A gid vid hm c
        ∃v : Fin (s).pairs,v.val=ordinal ∧ digit (s).digit (finProdFinEquiv (place.2,v)).val
          (out ((plan).layout.out+place.1.val)).val=DescentTerminalEpochFlags.encode ((scannedRows he A.stage).profile choice ⟨c,e⟩)) ∧
      ∀x,protectedAt x → out x=m x
def OrdinaryReport (choice : (A.stage.result he).Choice) (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree)
    (m : Memory w) (machine : Procedure w) (steps : ℕ) (protectedAt : ℕ→Prop) : Prop :=
  ObservedReport A native S ready he groups hosts hv C b payload unit profile seats romBase P₀ none choice rs m machine steps protectedAt

local notation "receipt" => OrdinaryReport (A:=A) (native:=native) (S:=S) (ready:=ready) (he:=he)
  (groups:=groups) (hosts:=hosts) (hv:=hv) (C:=C) (b:=b) (payload:=payload) (unit:=unit)
  (profile:=profile) (seats:=seats) (romBase:=romBase) (P₀:=P₀)

def OrdinaryOutput (choice : (A.stage.result he).Choice) (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree)
    (m : Memory w) : Prop :=
    receipt choice rs m ((initCPU).seq ((before).seq ((warm).seq matcher)))
      (timeInit+(time₀+time₁)) (fun x=>x < origin ∨ (plan).endAddr ≤ x)

local notation "report" => OrdinaryOutput (A:=A) (native:=native) (S:=S) (ready:=ready) (he:=he)
  (groups:=groups) (hosts:=hosts) (hv:=hv) (C:=C) (b:=b) (payload:=payload) (unit:=unit)
  (profile:=profile) (seats:=seats) (romBase:=romBase) (P₀:=P₀) (act:=act) (wire:=wire)
  (origin:=origin) (hubBank:=hubBank) (atom:=atom)

theorem cpu_from_old_observed (choice : (A.stage.result he).Choice) (stream : ℕ→Cell (s).digit)
    (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree) (m : Memory w)
    (setup : Chooser.Setup (G:=G) A hosts hv C b cap2 payload unit ratio rs m)
    (apart : Chooser.Apart (G:=G) (ℓ:=ℓ) A C b cap2 payload unit origin)
    (named : A.SiteNamed rank) (prior : Accessible P₀ act H G M w origin)
    (oldPort : ∀x j,(wire x j).Fits w origin ∧ liveRows≤(wire x j).size)
    (raster : Reads act (Prepare.actors A gid vid) M m)
    (cables : ∀x j,Reads (wire x j) (fun h g=>DescentSignedCableCodec.encode (Prepare.signed A native S ready gid vid x j h g)) M m)
    (mounted : Mounted P₀ rs m G M)
    (inputs : max 1 (max b (DescentSignedCableCodec.width A.degree A.cap))≤unit)
    (flagFits : hubBank.Fits w origin) (hostsFit : H≤hubBank.size)
    (readHub : ∀h,m (hubBank.base+h.val)=((Census.hub A vid h).val:Word w))
    (atomFit : ∀x,(atom x).Fits w origin)
    (atomRead : ∀x,DescentPackedZip.Source (atom x) (fun h g=>Census.count A groups vid b h g x) M m)
    (allocated : DescentPackedColumnSum.finish startSum (Census.columns rdx A.cap) unit M≤C.source.base)
    (low : C.chart.weights.base≤romBase)
    (next : C.last A.degree k b H G M+2^(Nat.clog 2 (liveRows+1))≤romBase)
    (large : Gather.matchUnit s panelBits rdx A.degree cap2≤unit) (space : (plan).endAddr<2^w)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats)
    (raw : ∀j < (plan).raw.size,m ((plan).raw.base+j)=((DescentPackedProfileWindow.word (s).digit grain stream j).val:Word w)) :
    ObservedReport A native S ready he groups hosts hv C b payload unit profile seats romBase P₀
      (some (∀i,(stream i).val=profileAt (inputNumber he A gid vid) ((scannedRows he A.stage).profile choice) i)) choice rs m ((initCPU).seq ((before).seq ((warm).seq matcher)))
      (timeInit+(time₀+time₁)) (fun x=>x < origin ∨ (plan).endAddr ≤ x) := by
  have left : origin≤ startSum := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have added : startSum≤C.source.base := (Nat.le_add_right ..).trans allocated
  have prev : C.source.base+liveRows≤C.chart.weights.base :=
    (Nat.add_le_add_left setup.sourceRows _).trans setup.sourceFits.2.2
  have firstLow : origin≤C.chart.weights.base := left.trans (added.trans ((Nat.le_add_right ..).trans prev))
  have nextRaw : nextBase≤(plan).raw.base := by
    change nextBase≤((nextBase+_)+_)+_
    exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have allEnd : (plan).raw.base≤(plan).endAddr := by
    change (plan).raw.base≤(((((((plan).raw.base+_)+_)+_)+_)+_)+_)
    simp only [Nat.add_assoc]
    exact Nat.le_add_right ..
  have rb : romBase≤base := by
    simp only [Prepare.ROM.sortBase,Nat.add_assoc]
    exact Nat.le_add_right ..
  have front : base≤nextBase := (Nat.le_add_right base (outB).size).trans (le_max_right ..)
  have top : C.chart.weights.base≤(plan).raw.base := low.trans (rb.trans (front.trans nextRaw))
  let originIns:=DescentStaticWordColumn.image origin (Census.Broadcast.literal H G M) m (2*liveRows)
  let mid:=DescentPackedColumnSum.after startSum C.source.base unit M outBits H G oldBits func src originIns
  obtain ⟨intake,words,frame,_⟩:=Census.from_old A native S ready groups vid b origin C.source.base unit hubBank atom wire m
    inputs flagFits hostsFit readHub atomFit atomRead oldPort cables allocated ((prev.trans (top.trans allEnd)).trans_lt space)
  have readOld (x : ℕ) (hx : x<origin) : mid x=m x:=frame x (.inl hx)
  have start:=Chooser.Setup.accept A groups hosts hv C b cap2 payload unit ratio rs m mid origin setup apart frame
    (DescentSharedCableNames.Stage.signed A native S ready) words
  have unmodified (j : ℕ) (hj : j < (plan).raw.size) :=
    (frame ((plan).raw.base+j) (.inr (prev.trans (top.trans (Nat.le_add_right ..))))).trans (raw j hj)
  obtain ⟨out,i,j,hm,cpu,mu,paint,muWord,paintWord,actor,rails,donorWord,topWords,received,keep⟩:=ordinary_cpu_observed A native S ready he groups hosts hv C
    b cap2 payload unit ratio profile seats romBase P₀ act wire choice stream rs mid start named
    (Chooser.accessible_before P₀ act prior firstLow)
    (fun x a=>⟨Chooser.bank_before (oldPort x a).1 firstLow,(oldPort x a).2⟩)
    (Chooser.reads_before act _ m mid raster readOld prior.source prior.srcRoom)
    (fun x a=>Chooser.reads_before (wire x a) _ m mid (cables x a) readOld (oldPort x a).1 (oldPort x a).2)
    (Chooser.mounted_before P₀ act rs m mid mounted readOld prior) low next
    ((le_max_right ..).trans ((le_max_right ..).trans inputs)) large space cap unmodified
  refine ⟨out,i,j,hm,?_,mu,paint,muWord,paintWord,actor,rails,donorWord,topWords,received,?_⟩
  · exact intake.then cpu
  · intro x hx
    rcases hx with a|a
    · exact (keep x (.inl (a.trans_le firstLow))).trans (frame x (.inl a))
    · exact (keep x (.inr a)).trans (frame x (.inr (prev.trans (top.trans (allEnd.trans a)))))

theorem cpu_from_old (choice : (A.stage.result he).Choice) (stream : ℕ→Cell (s).digit)
    (pins : ∀i,(stream i).val=profileAt (inputNumber he A gid vid) ((scannedRows he A.stage).profile choice) i)
    (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree) (m : Memory w)
    (setup : Chooser.Setup (G:=G) A hosts hv C b cap2 payload unit ratio rs m)
    (apart : Chooser.Apart (G:=G) (ℓ:=ℓ) A C b cap2 payload unit origin)
    (named : A.SiteNamed rank) (prior : Accessible P₀ act H G M w origin)
    (oldPort : ∀x j,(wire x j).Fits w origin ∧ liveRows≤(wire x j).size)
    (raster : Reads act (Prepare.actors A gid vid) M m)
    (cables : ∀x j,Reads (wire x j) (fun h g=>DescentSignedCableCodec.encode (Prepare.signed A native S ready gid vid x j h g)) M m)
    (mounted : Mounted P₀ rs m G M)
    (inputs : max 1 (max b (DescentSignedCableCodec.width A.degree A.cap))≤unit)
    (flagFits : hubBank.Fits w origin) (hostsFit : H≤hubBank.size)
    (readHub : ∀h,m (hubBank.base+h.val)=((Census.hub A vid h).val:Word w))
    (atomFit : ∀x,(atom x).Fits w origin)
    (atomRead : ∀x,DescentPackedZip.Source (atom x) (fun h g=>Census.count A groups vid b h g x) M m)
    (allocated : DescentPackedColumnSum.finish startSum (Census.columns rdx A.cap) unit M≤C.source.base)
    (low : C.chart.weights.base≤romBase)
    (next : C.last A.degree k b H G M+2^(Nat.clog 2 (liveRows+1))≤romBase)
    (large : Gather.matchUnit s panelBits rdx A.degree cap2≤unit) (space : (plan).endAddr<2^w)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats)
    (raw : ∀j < (plan).raw.size,m ((plan).raw.base+j)=((DescentPackedProfileWindow.word (s).digit grain stream j).val:Word w)) :
    report choice rs m := by
  obtain ⟨out,i,j,hm,run_,mu,paint,muWord,paintWord,actors,rails,donors,top,rows,frame⟩:=
    cpu_from_old_observed A native S ready he groups hosts hv C b payload unit ratio profile seats romBase
      P₀ act wire origin hubBank atom choice stream rs m setup apart named prior oldPort raster cables mounted inputs
      flagFits hostsFit readHub atomFit atomRead allocated low next large space cap raw
  exact ⟨out,i,j,hm,run_,mu,paint,muWord,paintWord,actors,rails,donors,top,rows pins,frame⟩

/-- Read the selected path directly from its original dense selector shelf.
The statement includes both the physical execution and the exterior frame. -/
theorem cpu_from_archive {Pin : Type} (choice : (A.stage.result he).Choice)
    (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree) (m : Memory w)
    (setup : Chooser.Setup (G:=G) A hosts hv C b cap2 payload unit ratio rs m)
    (apart : Chooser.Apart (G:=G) (ℓ:=ℓ) A C b cap2 payload unit origin)
    (named : A.SiteNamed rank) (prior : Accessible P₀ act H G M w origin)
    (oldPort : ∀x j,(wire x j).Fits w origin ∧ liveRows≤(wire x j).size)
    (raster : Reads act (Prepare.actors A gid vid) M m)
    (cables : ∀x j,Reads (wire x j) (fun h g=>DescentSignedCableCodec.encode (Prepare.signed A native S ready gid vid x j h g)) M m)
    (mounted : Mounted P₀ rs m G M)
    (inputs : max 1 (max b (DescentSignedCableCodec.width A.degree A.cap))≤unit)
    (flagFits : hubBank.Fits w origin) (hostsFit : H≤hubBank.size)
    (readHub : ∀h,m (hubBank.base+h.val)=((Census.hub A vid h).val:Word w))
    (atomFit : ∀x,(atom x).Fits w origin)
    (atomRead : ∀x,DescentPackedZip.Source (atom x) (fun h g=>Census.count A groups vid b h g x) M m)
    (allocated : DescentPackedColumnSum.finish startSum (Census.columns rdx A.cap) unit M≤C.source.base)
    (low : C.chart.weights.base≤romBase)
    (next : C.last A.degree k b H G M+2^(Nat.clog 2 (liveRows+1))≤romBase)
    (large : Gather.matchUnit s panelBits rdx A.degree cap2≤unit) (space : (plan).endAddr<2^w)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats)
    (norm : Normalize ((A.stage.result he).state choice))
    (headers : List (Source Pin)) (path : List (RankedSelection F P d bits gadget ε))
    (z : Pin→Bool) (truth : headers.map (rawAt z)=path.map (issuedProfile gadget))
    (epoch : ℕ) (entry : Source Pin) (selected : headers[epoch]?=some entry)
    (indexed : path[epoch]?=some (Prepared.ranked A he gid vid choice norm))
    (extend : DescentTerminalEpochBits.width entry.C≤(s).digit) (initial : Memory w)
    (issued : Stored entry (s).digit grain extend (plan).raw z initial)
    (preserved : ∀j < (plan).raw.size,m ((plan).raw.base+j)=initial ((plan).raw.base+j)) :
    report choice rs m := by
  obtain ⟨pins,raw⟩:=Prepared.old_pins A he gid vid choice norm headers path z truth epoch entry
    selected indexed (s).digit grain extend (plan).raw initial m issued preserved
  exact cpu_from_old A native S ready he groups hosts hv C b payload unit ratio profile seats romBase P₀
    act wire origin hubBank atom choice (wideCell entry.pin z (s).digit extend) pins rs m setup apart
    named prior oldPort raster cables mounted inputs flagFits hostsFit readHub atomFit atomRead allocated low next
    large space cap raw


local notation "CI" => Phase.CensusTables.image (w:=w) C.origin ((1+b+2*cap2)*rdx) (b*rdx) M H G
  (fun fl=>PackedCensus.lookup fl b cap2 k A.wire 256 (A.z*gadget.b) A.hist)
local notation "PI" => Phase.Arena.image (w:=w) C.chart A.fieldBits A.degree H G b
  (2*Phase.unit k b*M) (DescentHostDegree.gap A.degree)
  (2^DescentHostDegree.packExponent 20 A.degree*((A.wire*(A.z*gadget.b))*A.cap))
local notation "publish" => (CI).program.seq (PI).program

/-- Install both numerical chooser tables, build the census from the old rows,
and issue the chosen profile at every reached pair on that same execution. -/
theorem cpu_installed_observed {Pin : Type} (choice : (A.stage.result he).Choice)
    (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree) (m : Memory w)
    (setup : Chooser.Geometry (G:=G) (w:=w) A hosts hv C b cap2 payload unit ratio rs)
    (floor : ℕ) (entryRoom : floor≤origin)
    (oldC : floor≤(CI).low) (oldP : floor≤(PI).low)
    (printed : (CI).stop≤(PI).low ∨ (PI).stop≤(CI).low)
    (ceilingC : (CI).low+(CI).length≤(plan).raw.base) (ceilingP : (PI).low+(PI).length≤(plan).raw.base)
    (rosterBase : C.chart.roster.base=P₀.roster.base)
    (apart : Chooser.Apart (G:=G) (ℓ:=ℓ) A C b cap2 payload unit origin)
    (named : A.SiteNamed rank) (prior : Accessible P₀ act H G M w floor)
    (oldPort : ∀x j,(wire x j).Fits w floor ∧ liveRows≤(wire x j).size)
    (raster : Reads act (Prepare.actors A gid vid) M m)
    (cables : ∀x j,Reads (wire x j) (fun h g=>DescentSignedCableCodec.encode (Prepare.signed A native S ready gid vid x j h g)) M m)
    (mounted : Mounted P₀ rs m G M)
    (inputs : max 1 (max b (DescentSignedCableCodec.width A.degree A.cap))≤unit)
    (flagFits : hubBank.Fits w floor) (hostsFit : H≤hubBank.size)
    (readHub : ∀h,m (hubBank.base+h.val)=((Census.hub A vid h).val:Word w))
    (atomFit : ∀x,(atom x).Fits w floor)
    (atomRead : ∀x,DescentPackedZip.Source (atom x) (fun h g=>Census.count A groups vid b h g x) M m)
    (allocated : DescentPackedColumnSum.finish startSum (Census.columns rdx A.cap) unit M≤C.source.base)
    (low : C.chart.weights.base≤romBase)
    (next : C.last A.degree k b H G M+2^(Nat.clog 2 (liveRows+1))≤romBase)
    (large : Gather.matchUnit s panelBits rdx A.degree cap2≤unit) (space : (plan).endAddr<2^w)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats)
    (entry : Source Pin) (z : Pin→Bool)
    (extend : DescentTerminalEpochBits.width entry.C≤(s).digit) (initial : Memory w)
    (issued : Stored entry (s).digit grain extend (plan).raw z initial)
    (preserved : ∀j < (plan).raw.size,m ((plan).raw.base+j)=initial ((plan).raw.base+j)) :
    ObservedReport A native S ready he groups hosts hv C b payload unit profile seats romBase P₀
      (some (∀q,(wideCell entry.pin z (s).digit extend q).val=profileAt (inputNumber he A gid vid) ((scannedRows he A.stage).profile choice) q)) choice rs m ((publish).seq ((initCPU).seq ((before).seq ((warm).seq matcher))))
      ((8+10*((CI).length+(PI).length))+(timeInit+(time₀+time₁))) (fun x=>x<floor ∨ (plan).endAddr≤x) := by
  let mid:=(PI).output ((CI).output m)
  have last : (plan).raw.base≤(plan).endAddr := by
    change (plan).raw.base≤(((((((plan).raw.base+_)+_)+_)+_)+_)+_)
    simp only [Nat.add_assoc]
    exact Nat.le_add_right ..
  have pure : (CI).stop≤(plan).raw.base ∧ (PI).stop≤(plan).raw.base := by
    unfold Phase.Arena.Image.length at ceilingC ceilingP
    constructor <;> omega
  have top : C.chart.roster.base+H*A.degree≤floor := by
    rw [rosterBase]
    exact (Nat.add_le_add_left prior.rosterRoom _).trans prior.roster.2.2
  have previous (v : Fin H) (i : Fin A.degree) : m (C.chart.roster.base+(v.val*A.degree+i.val))=(((rs v i).elim H Fin.val : ℕ):Word w) := by
    rw [rosterBase];exact mounted.roster v i
  obtain ⟨headerRun,tables,frame,_,_⟩:=Chooser.Geometry.install A hosts hv C b cap2 payload unit ratio rs m
    setup printed (ceilingC.trans_lt (last.trans_lt space)) (ceilingP.trans_lt (last.trans_lt space))
    (top.trans oldC) (top.trans oldP) previous
  have same (x : ℕ) (hx : x<floor) : mid x=m x:=
    frame x (.inl (hx.trans_le oldC)) (.inl (hx.trans_le oldP))
  have fixed (x : ℕ) (hx : (plan).raw.base≤x) : mid x=m x:=
    frame x (.inr (pure.1.trans hx)) (.inr (pure.2.trans hx))
  have flags (h : Fin H) : mid (hubBank.base+h.val)=((Census.hub A vid h).val:Word w) :=
    (same _ ((Nat.add_lt_add_left (h.isLt.trans_le hostsFit) _).trans_le flagFits.2.2)).trans (readHub h)
  have atoms (x : Fin rdx) : DescentPackedZip.Source (atom x) (fun h g=>Census.count A groups vid b h g x) M mid :=
    fun y=>(eval_below (atom x) _ m mid (atomFit x) same).trans (atomRead x y)
  obtain ⟨out,i,j,hm,cpu,mu,paint,muWord,paintWord,actors,rails,donorWord,counts,profiles,keep⟩:=
    cpu_from_old_observed A native S ready he groups hosts hv C b payload unit ratio profile seats romBase P₀ act wire
      origin hubBank atom choice (wideCell entry.pin z (s).digit extend) rs mid tables apart named (Chooser.accessible_before P₀ act prior entryRoom)
      (fun x j=>⟨Chooser.bank_before (oldPort x j).1 entryRoom,(oldPort x j).2⟩)
      (Chooser.reads_before act _ m mid raster same prior.source prior.srcRoom)
      (fun x j=>Chooser.reads_before (wire x j) _ m mid (cables x j) same (oldPort x j).1 (oldPort x j).2)
      (Chooser.mounted_before P₀ act rs m mid mounted same prior) inputs (Chooser.bank_before flagFits entryRoom)
      hostsFit flags (fun x=>ProtocolRAMGeneratedWrite.fits_mono _ entryRoom (atomFit x)) atoms allocated
      low next large space cap
      (fun j hj=>(fixed _ (Nat.le_add_right ..)).trans ((preserved j hj).trans (issued j hj)))
  refine ⟨out,i,j,hm,Procedure.Exec.then headerRun cpu,mu,paint,muWord,paintWord,actors,rails,donorWord,counts,profiles,?_⟩
  intro x hx
  rcases hx with lo|hi
  · exact (keep x (.inl (lo.trans_le entryRoom))).trans (same x lo)
  · exact (keep x (.inr hi)).trans (fixed x (last.trans hi))

theorem cpu_installed {Pin : Type} (choice : (A.stage.result he).Choice)
    (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree) (m : Memory w)
    (setup : Chooser.Geometry (G:=G) (w:=w) A hosts hv C b cap2 payload unit ratio rs)
    (floor : ℕ) (entryRoom : floor≤origin)
    (oldC : floor≤(CI).low) (oldP : floor≤(PI).low)
    (printed : (CI).stop≤(PI).low ∨ (PI).stop≤(CI).low)
    (ceilingC : (CI).low+(CI).length≤(plan).raw.base) (ceilingP : (PI).low+(PI).length≤(plan).raw.base)
    (rosterBase : C.chart.roster.base=P₀.roster.base)
    (apart : Chooser.Apart (G:=G) (ℓ:=ℓ) A C b cap2 payload unit origin)
    (named : A.SiteNamed rank) (prior : Accessible P₀ act H G M w floor)
    (oldPort : ∀x j,(wire x j).Fits w floor ∧ liveRows≤(wire x j).size)
    (raster : Reads act (Prepare.actors A gid vid) M m)
    (cables : ∀x j,Reads (wire x j) (fun h g=>DescentSignedCableCodec.encode (Prepare.signed A native S ready gid vid x j h g)) M m)
    (mounted : Mounted P₀ rs m G M)
    (inputs : max 1 (max b (DescentSignedCableCodec.width A.degree A.cap))≤unit)
    (flagFits : hubBank.Fits w floor) (hostsFit : H≤hubBank.size)
    (readHub : ∀h,m (hubBank.base+h.val)=((Census.hub A vid h).val:Word w))
    (atomFit : ∀x,(atom x).Fits w floor)
    (atomRead : ∀x,DescentPackedZip.Source (atom x) (fun h g=>Census.count A groups vid b h g x) M m)
    (allocated : DescentPackedColumnSum.finish startSum (Census.columns rdx A.cap) unit M≤C.source.base)
    (low : C.chart.weights.base≤romBase)
    (next : C.last A.degree k b H G M+2^(Nat.clog 2 (liveRows+1))≤romBase)
    (large : Gather.matchUnit s panelBits rdx A.degree cap2≤unit) (space : (plan).endAddr<2^w)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats)
    (norm : Normalize ((A.stage.result he).state choice))
    (headers : List (Source Pin)) (path : List (RankedSelection F P d bits gadget ε))
    (z : Pin→Bool) (truth : headers.map (rawAt z)=path.map (issuedProfile gadget))
    (epoch : ℕ) (entry : Source Pin) (selected : headers[epoch]?=some entry)
    (indexed : path[epoch]?=some (Prepared.ranked A he gid vid choice norm))
    (extend : DescentTerminalEpochBits.width entry.C≤(s).digit) (initial : Memory w)
    (issued : Stored entry (s).digit grain extend (plan).raw z initial)
    (preserved : ∀j < (plan).raw.size,m ((plan).raw.base+j)=initial ((plan).raw.base+j)) :
    receipt choice rs m ((publish).seq ((initCPU).seq ((before).seq ((warm).seq matcher))))
      ((8+10*((CI).length+(PI).length))+(timeInit+(time₀+time₁))) (fun x=>x<floor ∨ (plan).endAddr≤x) := by
  obtain ⟨out,i,j,hm,run_,mu,paint,muWord,paintWord,actors,rails,donors,top,rows,frame⟩:=
    cpu_installed_observed A native S ready he groups hosts hv C b payload unit ratio profile seats romBase
      P₀ act wire origin hubBank atom choice rs m setup floor entryRoom oldC oldP printed ceilingC ceilingP
      rosterBase apart named prior oldPort raster cables mounted inputs flagFits hostsFit readHub atomFit
      atomRead allocated low next large space cap entry z extend initial issued preserved
  have correct:=(Prepared.old_pins A he gid vid choice norm headers path z truth epoch entry selected indexed
    (s).digit grain extend (plan).raw initial m issued preserved).1
  exact ⟨out,i,j,hm,run_,mu,paint,muWord,paintWord,actors,rails,donors,top,rows correct,frame⟩

/-- The identical instruction text halts on every memory, including malformed
profiles, masks and previous numeric rows. This uses only the address geometry. -/
theorem cpu_installed_any (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree)
    (setup : Chooser.Geometry (G:=G) (w:=w) A hosts hv C b cap2 payload unit ratio rs)
    (floor : ℕ) (entry : floor≤origin) (prior : Accessible P₀ act H G M w floor)
    (oldPort : ∀x j,(wire x j).Fits w floor ∧ liveRows≤(wire x j).size)
    (inputs : max 1 (max b (DescentSignedCableCodec.width A.degree A.cap))≤unit)
    (flagFits : hubBank.Fits w floor) (atomFit : ∀x,(atom x).Fits w floor)
    (allocated : DescentPackedColumnSum.finish startSum (Census.columns rdx A.cap) unit M≤C.source.base)
    (low : C.chart.weights.base≤romBase)
    (next : C.last A.degree k b H G M+2^(Nat.clog 2 (liveRows+1))≤romBase)
    (large : Gather.matchUnit s panelBits rdx A.degree cap2≤unit) (space : (plan).endAddr<2^w)
    (ceilingC : (CI).low+(CI).length≤(plan).raw.base) (ceilingP : (PI).low+(PI).length≤(plan).raw.base)
    (m : Memory w) :
    ∃out,((publish).seq ((initCPU).seq ((before).seq ((warm).seq matcher)))).Exec m out
      ((8+10*((CI).length+(PI).length))+(timeInit+(time₀+time₁))) := by
  let mid:=(PI).output ((CI).output m)
  have rawRoom : (plan).raw.base<2^w := by
    apply LE.le.trans_lt _ space
    change (plan).raw.base≤(((((((plan).raw.base+_)+_)+_)+_)+_)+_)
    simp only [Nat.add_assoc]
    exact Nat.le_add_right ..
  have first : (CI).program.Exec m ((CI).output m) (4+10*(CI).length) :=
    ((CI).issue m (ceilingC.trans_lt rawRoom)).1
  have second : (PI).program.Exec ((CI).output m) mid (4+10*(PI).length) :=
    ((PI).issue ((CI).output m) (ceilingP.trans_lt rawRoom)).1
  have fixed : (publish).Exec m mid (8+10*((CI).length+(PI).length)) := by
    have totalTime (x y : ℕ) : 8+10*(x+y) = (4+10*x)+(4+10*y) := by omega
    rw [totalTime]
    exact @Procedure.Exec.then w (CI).program (PI).program m ((CI).output m) mid _ _ @first @second
  have cut : startSum≤C.source.base := (Nat.le_add_right ..).trans allocated
  have seedFloor : origin≤ startSum := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have words : C.source.base+liveRows≤C.chart.weights.base :=
    (Nat.add_le_add_left setup.sourceRows _).trans setup.sourceFits.2.2
  have initial : floor≤romBase :=
    entry.trans (seedFloor.trans (cut.trans ((Nat.le_add_right ..).trans (words.trans low))))
  have rem : romBase<2^w := by
    apply LE.le.trans_lt _ rawRoom
    have old : romBase≤base := by
      simp only [Prepare.ROM.sortBase,Nat.add_assoc]
      exact Nat.le_add_right ..
    have left : base≤nextBase := (Nat.le_add_right base (outB).size).trans (le_max_right ..)
    exact old.trans (left.trans (by
      change nextBase≤((nextBase+_)+_)+_
      exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))))
  let history:=DescentStaticWordColumn.image origin (Census.Broadcast.literal H G M) mid (2*liveRows)
  let observed:=DescentPackedColumnSum.after startSum C.source.base unit M outBits H G oldBits func src history
  have fresh : (initCPU).Exec mid observed timeInit := Census.any k A.degree A.cap b unit M H G origin C.source.base hubBank atom wire mid inputs
    (Chooser.bank_before flagFits entry) (fun x=>ProtocolRAMGeneratedWrite.fits_mono _ entry (atomFit x))
    (fun x j=>Chooser.bank_before (oldPort x j).1 entry) allocated (words.trans_lt (low.trans_lt rem))
  obtain ⟨v,elect⟩:=Chooser.Geometry.any A hosts hv C b cap2 payload unit ratio rs setup observed
  have access:=Chooser.accessible_before P₀ act prior initial
  have banks : Prepare.ROM.OldRoom act vals wire P₀.roster H G A.degree M w romBase :=
    ⟨⟨access.source,access.srcRoom⟩,Chooser.winners_before C k b A.degree H G M w romBase next rem,
      fun x j=>⟨Chooser.bank_before (oldPort x j).1 initial,(oldPort x j).2⟩,⟨access.roster,access.rosterRoom⟩⟩
  have digit : panelBits≤unit := (Nat.le_add_left panelBits _).trans ((le_max_left ..).trans large)
  have signed : DescentSignedCableCodec.width A.degree A.cap≤unit :=
    (le_max_right ..).trans ((le_max_right ..).trans inputs)
  have fitPayload : unit*M≤payload/2 := by simpa only [Nat.mul_comm unit] using lanes_fit payload unit
  have bitsFit : unit*M≤w/2 := fitPayload.trans (Nat.div_le_div_right setup.embed)
  have key : M*max (DescentSignedCableCodec.width A.degree A.cap) panelBits≤w/2 :=
    (Nat.mul_le_mul_left M (max_le signed digit)).trans (by simpa only [Nat.mul_comm M unit] using bitsFit)
  have degree : A.degree≤H*A.degree := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right A.degree (Nat.two_pow_pos ℓ)
  have range : max H A.degree<2^w := max_lt (prior.offRoom.trans_lt prior.offsets.2.1)
    ((degree.trans prior.rosterRoom).trans_lt prior.roster.2.1)
  let staged := Prepare.ROM.after romBase k A.degree A.cap (k+3) panelBits M H G v
  let completed := Gather.ROM.after s panelBits rdx A.degree cap2 A.cap K H G M unit nextBase seats field (ProtocolRAM.result ps staged)
  have end_ : ((warm).seq matcher).Exec v completed time₁ := Prepared.any (a:=k+3) (short:=panelBits) s K A.cap unit romBase seats P₀ act vals wire
    banks access key large bitsFit range space v
  exact ⟨_,fixed.then (fresh.then (elect.then end_))⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
