import OAI.Hierarchy.DescentPackedOrdinaryFromRows
import OAI.Hierarchy.DescentPackedLayoutFinish
import OAI.Hierarchy.DescentPackedMatchStageReturn

namespace OAI
/-! # The common layout and six births of the native ordinary matcher -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentCompiler DescentSixParty DescentStageEdgeReceipt DescentKernelHistory.BitDescription
open DescentSIMDLookup DescentPackedColony DescentTerminalEpochDecoder DescentPackedProfileWindow
open DescentSixParty.Chronology DescentTerminalEpochChart DescentPackedProfileArchive DescentPackedProfileWide
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentSixParty.StarKeys
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 3000000

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

local notation "CI" => Phase.CensusTables.image (w:=w) C.origin ((1+b+2*cap2)*rdx) (b*rdx) M H G
  (fun fl=>PackedCensus.lookup fl b cap2 k A.wire 256 (A.z*gadget.b) A.hist)
local notation "PI" => Phase.Arena.image (w:=w) C.chart A.fieldBits A.degree H G b
  (2*Phase.unit k b*M) (DescentHostDegree.gap A.degree)
  (2^DescentHostDegree.packExponent 20 A.degree*((A.wire*(A.z*gadget.b))*A.cap))
local notation "publish" => (CI).program.seq (PI).program

local notation "N" => (K*H)*chunks G M
local notation "top" => (plan).layout.topology
local notation "profiles" => (plan).layout.out
local notation "ft" => LayoutSum.Finish.first top profiles N
local notation "B" => LayoutSum.Finish.chart s M top profiles N
local notation "births" => LayoutSum.Finish.births s M top profiles N
local notation "doneAt" => LayoutSum.Finish.stop s M top profiles N
local notation "suffix" => LayoutSum.Finish.program s M top profiles N gadget w
local notation "tock" => LayoutSum.Finish.ticks s M N
local notation "sh" => C.shelves A.degree k b M
local notation "receipt" => OrdinaryReport (A:=A) (native:=native) (S:=S) (ready:=ready) (he:=he)
  (groups:=groups) (hosts:=hosts) (hv:=hv) (C:=C) (b:=b) (payload:=payload) (unit:=unit)
  (profile:=profile) (seats:=seats) (romBase:=romBase) (P₀:=P₀)
local notation "number" => (fun c : ScanColonies he A.stage=>pairNumber (DescentPacking.amount (live T))
  (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions)
local notation "pairProfile" choice => (scannedRows he A.stage).profile choice
local notation "truthFlag" choice => bestLayout (branchWidth gadget (fun _=>A.z) (pairProfile choice))

/-- The common layout bit, six records for each selected pair, original match
topology, and oriented affine choices all occur on a single native memory. -/
def LayoutReportAt (choice : (A.stage.result he).Choice) (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree)
    (m : Memory w) (code : Procedure w) (time : ℕ) (protectedAt : ℕ→Prop) (done : Memory w) : Prop :=
  ∃i : Fin (2^k-1),∃j : DescentAffineColors.Candidate k,∃hm : 0<M,
    let pub:=A.publishedTicket groups hosts rs i j
    let win:=fun h : J×V=>pub (vid h.2) (gid h.1)
    let panel:=terrain (short:=panelBits) A native S ready (cableNames k rank) win (rotor A rank)
    let keys:=topologyWords («M»:=M) s (Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap (spread gid vid panel)))
    code.Exec m done time ∧
    done (B).out=(if truthFlag choice then (1:Word w) else 0) ∧
    done (sh).mu=(i.val:Word w) ∧ DescentColonies.seedAt k i=(scannedRows he A.stage).μ ∧
    done (sh).paint=(j.val:Word w) ∧ j=DescentAffineColors.code (scannedRows he A.stage).α (scannedRows he A.stage).β ∧
    (∀u,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (home u)).2+(color u).toNat) ∧
    Rails {P₀ with roster:=outB} wins_ marks_ (spread gid vid panel)
        (hostRotor vid (DescentGroupPeerOrder.hostRoster A ((vid).trans Fin.valEmbedding))) M nextBase done ∧
    Gather.ROM.DonorWord («M»:=M) donor (plan).source.base (spread gid vid panel) done ∧
    (∀q : Fin N,done ((top).base+q.val)=((keys q).val:Word w)) ∧
    (∀c e,∃v : Fin (s).pairs,v.val=(number c e).val ∧
      let p:=slot he A gid vid hm c
      let tag:=DescentTerminalEpochFlags.encode ((pairProfile choice) ⟨c,e⟩)
      digit (s).digit (finProdFinEquiv (p.2,v)).val (done (profiles+p.1.val)).val=tag ∧
      ∀q : Fin 6,SixBirths.atom A.z
        (digit ((s).digit+1) (SixBirths.slot p.2 v q).val (done (births+p.1.val)).val)
        (SixBirths.slot p.2 v q).val=some (A.z,tag,q.val)) ∧
    (∀ (i : Fin N) (a : Fin M) (j : Fin (s).pairs),(laneCounts s M (keys i) a).val≤j.val→
      ∀q : Fin 6,digit ((s).digit+1) (SixBirths.slot a j q).val (done (births+i.val)).val=0) ∧
    ∀x,protectedAt x → done x=m x

def LayoutReport (choice : (A.stage.result he).Choice) (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree)
    (m : Memory w) (code : Procedure w) (time : ℕ) (protectedAt : ℕ→Prop) : Prop :=
  ∃done,LayoutReportAt A native S ready he groups hosts hv C b payload unit profile seats romBase P₀ choice rs m code time protectedAt done

local notation "complete" => LayoutReport (A:=A) (native:=native) (S:=S) (ready:=ready) (he:=he)
  (groups:=groups) (hosts:=hosts) (hv:=hv) (C:=C) (b:=b) (payload:=payload) (unit:=unit)
  (profile:=profile) (seats:=seats) (romBase:=romBase) (P₀:=P₀)

theorem OrdinaryReport.layout (choice : (A.stage.result he).Choice) (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree)
    (m : Memory w) (code : Procedure w) (time : ℕ) (protectedAt : ℕ→Prop)
    (old : receipt choice rs m code time protectedAt) (named : A.SiteNamed rank)
    (earlier : max (sh).mu (sh).paint<ft) (width : SixBirths.width s M≤w)
    (ends : doneAt<2^w) (budget : Fintype.card (NativePair W.graph W.core home color A.cap)*(gadget.C+8+8*gadget.k)<2^w) :
    complete choice rs m (code.seq suffix) (time+tock) (fun x=>protectedAt x ∧ (x<ft ∨ doneAt≤x)) := by
  obtain ⟨mid,i,j,hm,first,mu,paint,storedMu,storedPaint,winning,rails,donorWord,posted,accepted,save⟩:=old
  let pub:=A.publishedTicket groups hosts rs i j
  let win (h : J×V):=pub (vid h.2) (gid h.1)
  let panel:=terrain (short:=panelBits) A native S ready (cableNames k rank) win (rotor A rank)
  let keys:=topologyWords («M»:=M) s (Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap (spread gid vid panel)))
  have short_ (u : W.graph.Site) : (win (A.pos u) (A.block u)).val<2^panelBits :=
    (win (A.pos u) (A.block u)).isLt.trans_le (Nat.pow_le_pow_right (by decide) (le_max_left ..))
  have degree : A.degree<2^panelBits :=
    (Nat.lt_succ_self _).trans_le ((Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) (le_max_right ..)))
  have counts:=measured A native S ready rank win he gid vid hm ready.coordinates named short_ winning degree profile
  have nt : N≤(top).size := Gather.ROM.column_size _ _
  have cells : ∀q : Fin N,(top).base+q.val<ft := fun q=>
    (Nat.add_lt_add_left (q.isLt.trans_le nt) _).trans_le (le_max_left ..)
  have pads : N≤(SixBirths.tapeBank profiles N).size := Nat.le_pow_clog (by decide) _
  have rawCells : ∀q : Fin N,profiles+q.val<ft := fun q=>
    (Nat.add_lt_add_left (q.isLt.trans_le pads) _).trans_le (le_max_right ..)
  obtain ⟨done,issue,flag,hold,digits⟩:=LayoutSum.Finish.run s M top profiles N gadget A.z A.unitPos (pairProfile choice)
    (slot he A gid vid hm) number keys counts mid nt width ends budget posted accepted
  have lower : nextBase≤(plan).raw.base := by
    change nextBase≤((nextBase+_)+_)+_
    exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have extended : (plan).raw.base≤(plan).endAddr := by
    change (plan).raw.base≤(((((((plan).raw.base+_)+_)+_)+_)+_)+_)
    simp only [Nat.add_assoc]
    exact Nat.le_add_right ..
  have beforeFinish : nextBase≤ft := lower.trans (extended.trans ((Nat.add_le_add_left pads _).trans (le_max_right ..)))
  have retained:=rails.moved (o:=done) ⟨0,Nat.two_pow_pos k⟩ (fun a h=>hold a (.inl (h.trans_le beforeFinish)))
  have refEnd : (plan).source.base+(plan).source.size=(top).base:=rfl
  have dictEnd : (plan).source.base≤ft := (Nat.le_add_right ..).trans (refEnd.le.trans
    ((Nat.le_add_right ..).trans (le_max_left ..)))
  have packed:=donorWord.moved (o:=done) (fun a h=>hold a (.inl (h.trans_le dictEnd)))
  refine ⟨done,i,j,hm,first.then issue,flag,(hold _ (.inl ((le_max_left ..).trans_lt earlier))).trans storedMu,mu,
    (hold _ (.inl ((le_max_right ..).trans_lt earlier))).trans storedPaint,paint,winning,retained,packed,
    fun q=>(hold _ (.inl (cells q))).trans (posted q),?_,?_,?_⟩
  · intro c e
    obtain ⟨v,eqv,prof⟩:=accepted c e
    let p:=slot he A gid vid hm c
    have on_ : v.val<(laneCounts s M (keys p.1) p.2).val := by
      rw [eqv,counts.live c];exact (number c e).isLt
    refine ⟨v,eqv,?_,?_⟩
    · rw [hold _ (.inl (rawCells p.1))]
      exact prof
    · intro q
      rw [digits,ite_eq_left on_,prof]
      simp [SixBirths.atom,SixBirths.role]
  · intro idx lane j off q
    rw [digits,ite_eq_right (Nat.not_lt.mpr off)]
  · intro x hx
    exact (hold x (hx.2.imp_right (fun hi=>show (B).out<x from hi))).trans (save x hx.1)

private theorem first_le_layout_stop : ft≤doneAt := by
  have toBirths : ft≤births := Nat.le_add_right ..
  have toBase : births≤LayoutSum.Finish.base s M top profiles N := Nat.le_add_right ..
  apply toBirths.trans (toBase.trans ?_)
  change _ ≤ LayoutSum.Finish.base s M top profiles N+2*_+4*N+2+1
  exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans
    ((Nat.le_add_right ..).trans (Nat.le_add_right ..)))

/-- Install and execute the chooser, matcher, six births and the layout comparison. -/
theorem cpu_installed_layout {Pin : Type} (choice : (A.stage.result he).Choice)
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
    (large : Gather.matchUnit s panelBits rdx A.degree cap2≤unit)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats)
    (norm : Normalize ((A.stage.result he).state choice))
    (headers : List (Source Pin)) (path : List (RankedSelection F P d bits gadget ε))
    (z : Pin→Bool) (truth : headers.map (rawAt z)=path.map (issuedProfile gadget))
    (epoch : ℕ) (entry : Source Pin) (selected : headers[epoch]?=some entry)
    (indexed : path[epoch]?=some (Prepared.ranked A he gid vid choice norm))
    (extend : DescentTerminalEpochBits.width entry.C≤(s).digit) (initial : Memory w)
    (issued : Stored entry (s).digit grain extend (plan).raw z initial)
    (preserved : ∀j < (plan).raw.size,m ((plan).raw.base+j)=initial ((plan).raw.base+j))
    (birthUnit : SixBirths.unit s≤unit) (endRoom : doneAt<2^w)
    (budget : seats*(gadget.C+8+8*gadget.k)<2^w) :
    complete choice rs m
      (((publish).seq ((initCPU).seq ((before).seq ((warm).seq matcher)))).seq suffix)
      (((8+10*((CI).length+(PI).length))+(timeInit+(time₀+time₁)))+tock)
      (fun x=>x<floor ∨ doneAt≤x) := by
  have pads : N≤(SixBirths.tapeBank profiles N).size := Nat.le_pow_clog (by decide) _
  have beginEnd : (plan).endAddr≤ft :=
    (Nat.add_le_add_left pads _).trans (le_max_right ..)
  have last : ft≤doneAt := by apply first_le_layout_stop
  have saved:=cpu_installed A native S ready he groups hosts hv C b payload unit ratio profile seats romBase P₀ act wire
    origin hubBank atom choice rs m setup floor entryRoom oldC oldP printed ceilingC ceilingP rosterBase apart
    named prior oldPort raster cables mounted inputs flagFits hostsFit readHub atomFit atomRead allocated low next large
    ((beginEnd.trans last).trans_lt endRoom) cap norm headers path z truth epoch entry selected indexed extend initial issued preserved
  have laneFit : unit*M≤payload/2 := by
    simpa only [Nat.mul_comm unit] using lanes_fit payload unit
  have width : SixBirths.width s M≤w :=
    (LayoutSum.Finish.width_le s M unit payload birthUnit laneFit).trans ((Nat.div_le_self ..).trans setup.embed)
  have banks:=(Phase.Arena.space C.chart C.marked A.fieldBits H G setup.room).final
  have past : (sh).output≤romBase := (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans next)
  have rb : romBase≤base := by
    simp only [Prepare.ROM.sortBase,Nat.add_assoc]
    exact Nat.le_add_right ..
  have front : base≤nextBase := (Nat.le_add_right base (outB).size).trans (le_max_right ..)
  have lower : nextBase≤(plan).raw.base := by
    change nextBase≤((nextBase+_)+_)+_
    exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have extended : (plan).raw.base≤(plan).endAddr := by
    change (plan).raw.base≤(((((((plan).raw.base+_)+_)+_)+_)+_)+_)
    simp only [Nat.add_assoc]
    exact Nat.le_add_right ..
  have mark : romBase≤ft := rb.trans (front.trans (lower.trans (extended.trans beginEnd)))
  have early := (max_lt banks.seed banks.paint).trans_le (past.trans mark)
  have priced := (Nat.mul_le_mul_right _ cap).trans_lt budget
  obtain ⟨done,i,j,hm,exec,flag,mu,seed,paint,color_,actors,rails,packed,keys,rows,holes,keep⟩:=
    OrdinaryReport.layout A native S ready he groups hosts hv C b payload unit profile seats romBase P₀ choice rs m _ _ _
      saved named early width endRoom priced
  have oldFloor : floor≤ft := entryRoom.trans (by
    have begin_ : origin≤ startSum := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
    have entries_ : startSum≤C.source.base := (Nat.le_add_right ..).trans allocated
    exact begin_.trans (entries_.trans ((Nat.le_add_right C.source.base C.source.size).trans
      (setup.sourceFits.2.2.trans (low.trans mark)))))
  refine ⟨done,i,j,hm,exec,flag,mu,seed,paint,color_,actors,rails,packed,keys,rows,holes,?_⟩
  intro x where_
  rcases where_ with lo|hi
  · exact keep x ⟨.inl lo,.inl (lo.trans_le oldFloor)⟩
  · exact keep x ⟨.inr ((beginEnd.trans last).trans hi),.inr hi⟩

theorem cpu_installed_layout_any (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree)
    (setup : Chooser.Geometry (G:=G) (w:=w) A hosts hv C b cap2 payload unit ratio rs)
    (floor : ℕ) (entry : floor≤origin) (prior : Accessible P₀ act H G M w floor)
    (oldPort : ∀x j,(wire x j).Fits w floor ∧ liveRows≤(wire x j).size)
    (inputs : max 1 (max b (DescentSignedCableCodec.width A.degree A.cap))≤unit)
    (flagFits : hubBank.Fits w floor) (atomFit : ∀x,(atom x).Fits w floor)
    (allocated : DescentPackedColumnSum.finish startSum (Census.columns rdx A.cap) unit M≤C.source.base)
    (low : C.chart.weights.base≤romBase)
    (next : C.last A.degree k b H G M+2^(Nat.clog 2 (liveRows+1))≤romBase)
    (large : Gather.matchUnit s panelBits rdx A.degree cap2≤unit)
    (ceilingC : (CI).low+(CI).length≤(plan).raw.base) (ceilingP : (PI).low+(PI).length≤(plan).raw.base)
    (birthUnit : SixBirths.unit s≤unit) (endRoom : doneAt<2^w) (m : Memory w) :
    ∃out,(((publish).seq ((initCPU).seq ((before).seq ((warm).seq matcher)))).seq suffix).Exec m out
      (((8+10*((CI).length+(PI).length))+(timeInit+(time₀+time₁)))+tock) := by
  have pads : N≤(SixBirths.tapeBank profiles N).size := Nat.le_pow_clog (by decide) _
  have prefix_ : (plan).endAddr≤ft := (Nat.add_le_add_left pads _).trans (le_max_right ..)
  have last : ft≤doneAt := by apply first_le_layout_stop
  have end_ : (plan).endAddr<2^w := (prefix_.trans last).trans_lt endRoom
  obtain ⟨mid,run⟩:=cpu_installed_any A hosts hv C b payload unit ratio profile seats romBase P₀ act wire origin hubBank atom rs
    setup floor entry prior oldPort inputs flagFits atomFit allocated low next large end_ ceilingC ceilingP m
  have digitRoom:=LayoutSum.Finish.width_le s M unit payload birthUnit (by simpa only [Nat.mul_comm unit] using lanes_fit payload unit)
  obtain ⟨out,issue,_⟩:=LayoutSum.Finish.any s M top profiles N gadget mid (Gather.ROM.column_size _ _)
    (digitRoom.trans ((Nat.div_le_self ..).trans setup.embed)) endRoom
  exact ⟨out,run.then issue⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
