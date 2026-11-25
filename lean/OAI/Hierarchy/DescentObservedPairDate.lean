import OAI.Hierarchy.DescentPackedOrdinaryRotation
import OAI.Hierarchy.DescentIssuedPairCount
import OAI.Hierarchy.DescentTerminalExecUnique
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # Count the first rejected choice from the real dated matcher topology -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentCompiler DescentSixParty DescentStageEdgeReceipt DescentKernelHistory.BitDescription
open DescentSIMDLookup DescentPackedColony DescentTerminalEpochDecoder DescentPackedProfileWindow
open DescentSixParty.Chronology DescentTerminalEpochChart DescentPackedProfileArchive DescentPackedProfileWide
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentSixParty.StarKeys
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 850000
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
variable (P₀ : Ports A.degree) (act : Bank) (wire : Fin (2^k)→ Fin (2*A.cap)→ Bank)
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

variable (origin : ℕ) (hubBank : Bank) (atom : Fin rdx→ Expr)
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


/-- The actual current profile may be malformed. Its six-record pass and saved
rotation leave the published match topology below their allocation. -/
theorem ObservedReport.count_on_date (ok : Option Prop) (choice : (A.stage.result he).Choice)
    (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree) (m : Memory w)
    (code : Procedure w) (time : ℕ) (protectedAt : ℕ → Prop)
    (observed : ObservedReport A native S ready he groups hosts hv C b payload unit profile seats romBase P₀
      ok choice rs m code time protectedAt) (named : A.SiteNamed rank)
    (earlier : (sh).mu< ft) (width : SixBirths.width s M≤ w)
    (finish : NativePhase w) (advance : ∀o,finish.Runs o)
    (at_ : ℕ) (untouched : ∀o a,a<rotEnd ∨ at_≤a → finish.image o a=o a)
    (fresh : rotEnd≤ at_) (room : DescentOrdinaryCountScan.endAddress ((s).outputBits*M) at_ N<2^w) :
    let f:=chunkCount s M
    let cnt:=DescentOrdinaryCountScan.address ((s).outputBits*M) at_ N
    ∃o,((((code.seq suffix).seq writeRot).seq finish.program).seq (DescentOrdinaryCountScan.program w top f at_ N)).Exec m o
      ((((time+tock)+rotTime)+finish.ticks)+DescentOrdinaryCountScan.clock ((s).outputBits*M) N) ∧
      o cnt=((Fintype.card (scannedRows he A.stage).pairs):Computability.VPVNP.BurstRAM.Word w) ∧ o rotOut=((matrix).val:Computability.VPVNP.BurstRAM.Word w) ∧
      ∀a,protectedAt a → (a< ft ∨ DescentOrdinaryCountScan.endAddress ((s).outputBits*M) at_ N≤ a) → o a=m a :=by
  intro f cnt
  obtain ⟨mid,i,j,hm,first,selected,_,seed,_,winning,_,_,counted,_,past⟩:=observed
  let pub:=A.publishedTicket groups hosts rs i j
  let win (h : J×V):=pub (vid h.2) (gid h.1)
  have short_ (u : W.graph.Site) : (win (A.pos u) (A.block u)).val<2^panelBits :=
    (win (A.pos u) (A.block u)).isLt.trans_le (Nat.pow_le_pow_right (by decide) (le_max_left ..))
  have degree : A.degree<2^panelBits :=
    (Nat.lt_succ_self _).trans_le ((Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) (le_max_right ..)))
  have nt : N≤(top).size:=Gather.ROM.column_size _ _
  have finishLow : ft≤ doneAt :=by
    have one : ft≤ births:=Nat.le_add_right ..
    have two : births≤ LayoutSum.Finish.base s M top profiles N:=Nat.le_add_right ..
    have three : LayoutSum.Finish.base s M top profiles N≤ doneAt:=by
      change _≤ LayoutSum.Finish.base s M top profiles N+2*_+4*N+2+1;omega
    exact one.trans (two.trans three)
  have rotLow : doneAt≤ rotEnd:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have bound : at_≤ DescentOrdinaryCountScan.endAddress ((s).outputBits*M) at_ N:=by
    exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have endRot : rotEnd<2^w:=(fresh.trans bound).trans_lt room
  obtain ⟨afterFinish,doFinish,kept,_⟩:=LayoutSum.Finish.any_framed s M top profiles N gadget mid nt width (rotLow.trans_lt endRot)
  obtain ⟨rotate,_,chosen,retained⟩:=DescentExteriorRotationWord.ordinary_fresh A.fieldBits (sh).mu doneAt afterFinish (earlier.trans_le finishLow) endRot
  let rotated:=image rotOut 1 expr ((sheet).output afterFinish)
  have unchanged (a : ℕ) (ha : a< ft ∨ rotEnd≤ a) : rotated a=mid a :=by
    have one:=retained a (ha.imp_left (fun h=>h.trans_le finishLow))
    have two:=kept a (ha.imp_right (fun h=>lt_of_lt_of_le (Nat.lt_succ_self (B).out) (rotLow.trans h)))
    exact one.trans two
  have priorEnd : (top).base+(top).size≤ ft:=le_max_left ..
  have tf : (top).Fits w at_ :=⟨Nat.two_pow_pos _,((Nat.le_add_left ..).trans
    (priorEnd.trans (finishLow.trans (rotLow.trans fresh)))).trans_lt (bound.trans_lt room),
    priorEnd.trans (finishLow.trans (rotLow.trans fresh))⟩
  have authentic:=topology_scalar A native S ready rank win he gid vid hm ready.coordinates named short_
    winning degree profile top at_ (finish.image rotated) tf nt
    (fun q=>by
      have cell:= (Nat.add_lt_add_left (q.isLt.trans_le nt) (top).base).trans_le priorEnd
      exact (untouched rotated _ (.inl (cell.trans_le (finishLow.trans rotLow)))).trans
        ((unchanged _ (.inl cell)).trans (counted q))) room
  have guard:=(DescentOrdinaryCountScan.run top f at_ N (finish.image rotated) tf room).2
  have selectedWord : rotated rotOut=((matrix).val:Computability.VPVNP.BurstRAM.Word w):=by
    rw [←selected]
    exact chosen i ((kept _ (.inl earlier)).trans seed)
  have saved : finish.image rotated rotOut=rotated rotOut:=untouched _ _ (.inl (Nat.lt_succ_self _))
  exact ⟨_,Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then first doFinish) rotate) (advance rotated)) authentic.1,authentic.2,
    (guard _ (.inl ((Nat.lt_succ_self _).trans_le fresh))).trans (saved.trans selectedWord),fun a outside where_=>
    (guard a (where_.imp_left (fun h=>h.trans_le (finishLow.trans (rotLow.trans fresh))))).trans
      ((untouched rotated a (where_.imp (fun h=>h.trans_le (finishLow.trans rotLow)) (fun h=>bound.trans h))).trans
        ((unchanged a (where_.imp_right (fun h=>(fresh.trans bound).trans h))).trans (past a outside)))⟩

theorem ObservedReport.count_on_public_date (ok : Option Prop) (choice : (A.stage.result he).Choice)
    (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree) (m : Memory w)
    (code : Procedure w) (time : ℕ) (protectedAt : ℕ → Prop)
    (observed : ObservedReport A native S ready he groups hosts hv C b payload unit profile seats romBase P₀
      ok choice rs m code time protectedAt) (named : A.SiteNamed rank)
    (earlier : (sh).mu< ft) (width : SixBirths.width s M≤ w)
    (matchPhase donor after_ : NativePhase w)
    (codeAt : matchPhase.program=(code.seq suffix).seq writeRot) (attained : matchPhase.Runs m)
    (paid : ∀o,donor.Runs o) (advance : ∀o,after_.Runs o)
    (at_ : ℕ) (unchanged : ∀o a,a<rotEnd ∨ at_≤a → (donor.seq after_).image o a=o a)
    (fresh : rotEnd≤at_) (srcFit : (top).Fits w at_)
    (room : DescentOrdinaryCountScan.endAddress ((s).outputBits*M) at_ N<2^w) :
    let f:=chunkCount s M
    let count : NativePhase w:=⟨DescentOrdinaryCountScan.program w top f at_ N,
      DescentOrdinaryCountScan.clock ((s).outputBits*M) N,DescentOrdinaryCountScan.output top f at_ N,
      (DescentOrdinaryCountScan.hardware w top f at_ N).1⟩
    let dated:=(matchPhase.seq donor).seq (after_.seq count)
    dated.Runs m ∧ dated.image m (DescentOrdinaryCountScan.address ((s).outputBits*M) at_ N)=
      ((Fintype.card (scannedRows he A.stage).pairs):Computability.VPVNP.BurstRAM.Word w) ∧ dated.image m rotOut=((matrix).val:Computability.VPVNP.BurstRAM.Word w) ∧
      ∀a,protectedAt a → (a<ft ∨ DescentOrdinaryCountScan.endAddress ((s).outputBits*M) at_ N≤a) →
        dated.image m a=m a :=by
  intro f count dated
  let main:=donor.seq after_
  let mid:=matchPhase.image m
  have tailRuns (o : Memory w) : main.Runs o:=donor.seq_runs after_ o (paid o) (advance _)
  have countRuns (o : Memory w) : count.Runs o:=(DescentOrdinaryCountScan.run top f at_ N o srcFit room).1
  have joined:=ObservedReport.count_on_date A native S ready he groups hosts hv C b payload unit profile seats
    romBase P₀ ok choice rs m code time protectedAt observed named earlier width main tailRuns at_ unchanged fresh room
  obtain ⟨out,execute,actual,rotate,frame⟩:=joined
  have reference : (((matchPhase.program.seq main.program).seq count.program)).Exec m (dated.image m)
      ((matchPhase.ticks+main.ticks)+count.ticks) :=
    ((matchPhase.seq main).seq_runs count m (matchPhase.seq_runs main m attained (tailRuns mid)) (countRuns _))
  rw [codeAt] at reference
  have unique_:=ProtocolRAM.exec_unique _ m _ out reference execute
  exact ⟨(matchPhase.seq donor).seq_runs (after_.seq count) m (matchPhase.seq_runs donor m attained (paid mid))
    (after_.seq_runs count _ (advance _) (countRuns _)),unique_.symm ▸ actual,unique_.symm ▸ rotate,unique_.symm ▸ frame⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
