import OAI.Hierarchy.DescentPackedOrdinaryLayout
import OAI.Hierarchy.DescentExteriorRotationWord

namespace OAI
/-! # Store the selected ordinary exterior rotation beside the common layout bit -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentCompiler DescentSixParty DescentStageEdgeReceipt DescentKernelHistory.BitDescription
open DescentSIMDLookup DescentPackedColony DescentTerminalEpochDecoder DescentPackedProfileWindow
open DescentSixParty.Chronology DescentTerminalEpochChart DescentPackedProfileArchive DescentPackedProfileWide
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentSixParty.StarKeys
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
attribute [local irreducible] Gather.ROM.after Gather.ROM.machine Gather.ROM.ticks Prepare.ROM.after ProtocolRAM.result Chooser.Layout.program Chooser.Layout.ticks

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
local notation "dataAt" => LayoutReportAt A native S ready he groups hosts hv C b payload unit profile seats romBase P₀
local notation "complete" => LayoutReport A native S ready he groups hosts hv C b payload unit profile seats romBase P₀
local notation "sheet" => DescentExteriorRotationWord.sheet (w:=w) A.fieldBits doneAt
local notation "rotOut" => doneAt+2^k
local notation "rotEnd" => rotOut+1
local notation "expr" => DescentExteriorRotationWord.ordinary (sh).mu ⟨doneAt,k⟩
local notation "writeRot" => (sheet).program.seq (scan w rotOut 1 expr)
local notation "rotTime" => (4+10*(2^k-1))+30
local notation "matrix" => DescentExterior.matrixCode (DescentColonies.multiplier A.fieldBits ((scannedRows he A.stage).μ))

private theorem next_before_topology : nextBase≤(top).base := by
  have lower : nextBase≤(plan).raw.base := by
    change nextBase≤((nextBase+_)+_)+_
    exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have sourceStart : (plan).raw.base≤(plan).source.base := Nat.le_add_right _ (plan).raw.size
  have topStart : (plan).source.base≤(top).base := Nat.le_add_right _ (plan).source.size
  exact lower.trans (sourceStart.trans topStart)

private theorem rom_before_rotation : romBase≤doneAt := by
  have rb : romBase≤base := by
    simp only [Prepare.ROM.sortBase,Nat.add_assoc]
    exact Nat.le_add_right ..
  have front : base≤nextBase := (Nat.le_add_right base (outB).size).trans (le_max_right ..)
  have topFirst : (top).base≤ft := (Nat.le_add_right _ (top).size).trans (le_max_left ..)
  have ht : ft≤births := Nat.le_add_right ..
  have hb : births≤LayoutSum.Finish.base s M top profiles N := Nat.le_add_right ..
  have last : LayoutSum.Finish.base s M top profiles N≤doneAt := by
    change _ ≤ LayoutSum.Finish.base s M top profiles N+2*_+4*N+2+1
    exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans
      ((Nat.le_add_right ..).trans (Nat.le_add_right ..)))
  exact rb.trans (front.trans ((show nextBase≤(top).base by apply next_before_topology).trans
    (topFirst.trans (ht.trans (hb.trans last)))))

/-- The rotation pass reads the elected ordinal in the same memory that holds the
six-party records. Both the layout comparison and the emitted records survive. -/
theorem LayoutReport.rotation (choice : (A.stage.result he).Choice) (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree)
    (m : Memory w) (code : Procedure w) (time : ℕ) (keep : ℕ→Prop)
    (layout : complete choice rs m code time keep) (early : max (sh).mu (sh).paint<doneAt) (room : rotEnd<2^w) :
    ∃done,dataAt choice rs m (code.seq writeRot) (time+rotTime)
      (fun x=>keep x ∧ (x<doneAt ∨ rotEnd≤x)) done ∧ done rotOut=((matrix).val:Word w) := by
  obtain ⟨prev,i,j,hm,run,flag,mu,seed,paint,sign,wins,rails,packed,keys,real,holes,held⟩:=layout
  obtain ⟨post,_,chosen,frame⟩:=DescentExteriorRotationWord.ordinary_fresh A.fieldBits (sh).mu doneAt prev
    ((le_max_left ..).trans_lt early) room
  have nt : N≤(top).size := Gather.ROM.column_size _ _
  have np : N≤(SixBirths.tapeBank profiles N).size := Nat.le_pow_clog (by decide) _
  have first : ft≤births := Nat.le_add_right ..
  have prefix_ : births+N≤LayoutSum.Finish.base s M top profiles N :=
    Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _
  have end_ : LayoutSum.Finish.base s M top profiles N≤doneAt := by
    change _≤LayoutSum.Finish.base s M top profiles N+2*_+4*N+2+1
    exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans
      ((Nat.le_add_right ..).trans (Nat.le_add_right ..)))
  have from_ : ft≤doneAt := first.trans ((Nat.le_add_right ..).trans (prefix_.trans end_))
  have topEnd : (top).base+N≤doneAt := ((Nat.add_le_add_left nt _).trans (le_max_left ..)).trans from_
  have profileEnd : profiles+N≤doneAt := ((Nat.add_le_add_left np _).trans (le_max_right ..)).trans from_
  have get (x : ℕ) (before_ : x<doneAt) :=frame x (.inl before_)
  have accessEnd : nextBase≤doneAt := (show nextBase≤(top).base by apply next_before_topology).trans
    ((Nat.le_add_right _ N).trans topEnd)
  have refEnd : (plan).source.base+(plan).source.size=(top).base:=rfl
  have dictEnd : (plan).source.base≤doneAt := (Nat.le_add_right ..).trans (refEnd.le.trans
    ((Nat.le_add_right ..).trans topEnd))
  refine ⟨_,⟨i,j,hm,run.then post,(get _ (Nat.lt_succ_self _)).trans flag,
    (get _ ((le_max_left ..).trans_lt early)).trans mu,seed,
    (get _ ((le_max_right ..).trans_lt early)).trans paint,sign,wins,rails.moved ⟨0,Nat.two_pow_pos k⟩ (fun a h=>get a (h.trans_le accessEnd)),
    packed.moved (fun a h=>get a (h.trans_le dictEnd)),?_,?_,?_,?_⟩,?_⟩
  · intro q
    exact (get _ ((Nat.add_lt_add_left q.isLt _).trans_le topEnd)).trans (keys q)
  · intro c e
    obtain ⟨v,hv,token,born⟩:=real c e
    let p:=slot he A gid vid hm c
    refine ⟨v,hv,?_,?_⟩
    · rw [get _ ((Nat.add_lt_add_left p.1.isLt _).trans_le profileEnd)]
      exact token
    · intro q
      rw [get _ ((Nat.add_lt_add_left p.1.isLt _).trans_le (prefix_.trans end_))]
      exact born q
  · intro x a j h q
    rw [get _ ((Nat.add_lt_add_left x.isLt _).trans_le (prefix_.trans end_))]
    exact holes x a j h q
  · intro a both
    exact (frame a both.2).trans (held a both.1)
  · simpa only [seed] using chosen i mu

theorem cpu_installed_rotation {Pin : Type} (choice : (A.stage.result he).Choice)
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
    (birthUnit : SixBirths.unit s≤unit) (endRoom : rotEnd<2^w)
    (budget : seats*(gadget.C+8+8*gadget.k)<2^w) :
    let code:=(((publish).seq ((initCPU).seq ((before).seq ((warm).seq matcher)))).seq suffix).seq writeRot
    let time:=(((8+10*((CI).length+(PI).length))+(timeInit+(time₀+time₁)))+tock)+rotTime
    ∃done,dataAt choice rs m code time (fun x=>x<floor ∨ rotEnd≤x) done ∧ done rotOut=((matrix).val:Word w) := by
  have priorEnd : doneAt≤rotEnd := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have all:=cpu_installed_layout A native S ready he groups hosts hv C b payload unit ratio profile seats romBase P₀ act
    wire origin hubBank atom choice rs m setup floor entryRoom oldC oldP printed ceilingC ceilingP rosterBase apart named prior
    oldPort raster cables mounted inputs flagFits hostsFit readHub atomFit atomRead allocated low next large cap norm headers
    path z truth epoch entry selected indexed extend initial issued preserved birthUnit (priorEnd.trans_lt endRoom) budget
  have banks:=(Phase.Arena.space C.chart C.marked A.fieldBits H G setup.room).final
  have past : (sh).output≤romBase := (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans next)
  have mark : romBase≤doneAt := by apply rom_before_rotation
  have early := (max_lt banks.seed banks.paint).trans_le (past.trans mark)
  obtain ⟨done,⟨i,j,hm,exec,flag,mu,seed,paint,color_,actors,rails,packed,keys,rows,holes,frame⟩,rot⟩:=
    LayoutReport.rotation A native S ready he groups hosts hv C b payload unit profile seats romBase P₀ choice rs m _ _ _ all early endRoom
  have oldFloor : floor≤doneAt := entryRoom.trans (by
    have begin_ : origin≤ startSum:=(Nat.le_add_right origin (H*chunks G M)).trans (Nat.le_add_right ..)
    have entries_ : startSum≤C.source.base := (Nat.le_add_right ..).trans allocated
    exact begin_.trans (entries_.trans ((Nat.le_add_right C.source.base C.source.size).trans
      (setup.sourceFits.2.2.trans (low.trans mark)))))
  refine ⟨done,⟨i,j,hm,exec,flag,mu,seed,paint,color_,actors,rails,packed,keys,rows,holes,?_⟩,rot⟩
  intro x where_
  rcases where_ with lo|hi
  · exact frame x ⟨.inl lo,.inl (lo.trans_le oldFloor)⟩
  · exact frame x ⟨.inr (priorEnd.trans hi),.inr hi⟩

theorem cpu_installed_rotation_any (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree)
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
    (birthUnit : SixBirths.unit s≤unit) (endRoom : rotEnd<2^w) (m : Memory w) :
    ∃out,((((publish).seq ((initCPU).seq ((before).seq ((warm).seq matcher)))).seq suffix).seq writeRot).Exec m out
      ((((8+10*((CI).length+(PI).length))+(timeInit+(time₀+time₁)))+tock)+rotTime) := by
  have priorEnd : doneAt≤rotEnd := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  obtain ⟨mid,run⟩:=cpu_installed_layout_any A hosts hv C b payload unit ratio profile seats romBase P₀ act wire origin
    hubBank atom rs setup floor entry prior oldPort inputs flagFits atomFit allocated low next large ceilingC ceilingP
    birthUnit (priorEnd.trans_lt endRoom) m
  have past : (sh).output≤romBase := (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans next)
  have mark : romBase≤doneAt := by apply rom_before_rotation
  have room:=(Phase.Arena.space C.chart C.marked A.fieldBits H G setup.room).final
  have early :=room.seed.trans_le (past.trans mark)
  exact ⟨_,run.then (DescentExteriorRotationWord.ordinary_fresh A.fieldBits (sh).mu doneAt mid early endRoom).1⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
