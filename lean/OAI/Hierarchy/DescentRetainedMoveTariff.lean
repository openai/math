import OAI.Hierarchy.DescentPackedColumnHardware
import OAI.Hierarchy.DescentResetRetainedMixer
import OAI.Hierarchy.DescentFundedSetupInvoice

namespace OAI
/-! # Physical cost of the elected basis on the genuine previous retained channels -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentSIMDLookup.Overlap DescentPackedZip DescentPackedColony
open DescentGLPacked DescentGLPacked.BankImage DescentGLNielsen DescentGLControlCode DescentGL
open DescentSixParty.Chronology DescentResetRetainedSetup DescentPacking.PackedMatch.Local
open DescentStaticWordColumn (names names_seq names_scan names_mount)
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (v : Layout)

def stripCharge (H G A B a : ℕ) :=2048*((pieces G A B+1)*(A+1)*2^(a*A)+Overlap.rows H G A+Overlap.rows H G B+1)

theorem strip_cost {K : ℕ} (base H G A B a w : ℕ) (old : Fin K→Bank) (before : 0<A) (after_ : 0<B) :
    (Strip.code base H G A B a w old).ticks+7*names (Strip.code base H G A B a w old).program≤109+K*stripCharge H G A B a:=by
  have each (bs : List Bank) (loc : ℕ) :
      let p:=Books.phase w loc (bs.map (Strip.one H G A B a))
      p.ticks+7*names p.program≤109+bs.length*stripCharge H G A B a :=by
    induction bs generalizing loc with
    | nil=>
      change 4+7*names (scan w 0 0 (.lit 0))≤109+0*stripCharge H G A B a
      rw [names_scan,Nat.zero_mul];decide
    | cons b bs ih=>
      let item:=Strip.one H G A B a b
      have one:=Overlap.tariff loc H G A B a w b before after_
      have next:=ih (item.limit loc)
      simp only [List.map_cons,Books.phase,NativePhase.seq,names_seq,List.length_cons]
      rw [Nat.succ_mul bs.length]
      change (item.phase loc w).ticks+_+7*(names (item.phase loc w).program+_)≤_
      change (item.phase loc w).ticks+7*names (item.phase loc w).program≤ stripCharge H G A B a at one
      dsimp only [item] at one next ⊢
      omega
  simpa only [Strip.code,List.length_ofFn] using each (List.ofFn old) base

def retainedFieldWork :=1+v.blocks*23
theorem joined_work (base i : ℕ) (active : i<v.channels) : (v.joined base i).work≤v.retainedFieldWork:=by
  unfold joined SignedFields.joinOp
  rw [dite_eq_left active]
  simpa [Gather.assembly,retainedFieldWork] using Gather.collect_work _ (v.oldScalar base ⟨i,active⟩)
    (List.finRange v.blocks) 12 (fun _=>by change 12 ≤ 12; decide)

private theorem step_names (A : DescentGLPacked.Layout) (H P n start w : ℕ) :
    names (ProtocolRAM.program w (steps A H P start n))≤15+n*(11+4*110) :=by
  induction n generalizing start with
  | zero=>rw [steps,ProtocolRAM.program,names_scan];rfl
  | succ n ih=>
    have term:=DescentGLPacked.work (A.board start) (A.bank start) (A.flag start)
    have later:=ih (start+1)
    rw [steps,ProtocolRAM.program,names_seq,Pass.procedure,names_scan,Nat.succ_mul]
    dsimp only [single]
    omega

def literalCount (base w : ℕ) :=
  (SignedFields.controlSheet (v.matrix base) (v.high+v.low) w).length+
    (Dated.routes (v.chart base) (v.channels*v.hosts) v.high v.low v.bits w).length
/-- The selected control sheet and the explicitly printed shuffle tables are
both charged between the retained matrix start and its real successor boundary. -/
theorem literalCount_le (base w : ℕ) : v.literalCount base w≤v.mixed base-v.matrix base:=by
  let C:=v.chart base
  let d:=v.high+v.low
  let stop:=v.mixed base
  obtain ⟨valid,control,_,_,_⟩:=SignedFields.allocation (v.matrix base) v.channels v.hosts v.high v.low v.bits stop
    (show stop<2^stop from Nat.lt_two_pow_self)
  have lo : v.matrix base≤SignedFields.controlEnd (v.matrix base) d:=by unfold SignedFields.controlEnd;omega
  change SignedFields.controlEnd (v.matrix base) d ≤ C.input.base at control
  have inputSum : C.input.base+C.input.size≤C.start := valid.input.2.2
  have input : C.input.base≤C.start:=(Nat.le_add_right ..).trans inputSum
  have start : C.start≤C.heap d:=Nat.le_add_right ..
  have finish : C.heap d≤ stop:=Nat.le_add_right ..
  change (SignedFields.controlEnd (v.matrix base) d-v.matrix base)+(C.heap d-C.start)≤ stop-v.matrix base
  omega

def rowCount:=v.hosts*2^v.high
def glCost (base w : ℕ) :=
  let n:=(schedule (v.high+v.low)).length
  let rows:=v.rowCount
  let score:=v.retainedFieldWork
  let printed:=v.literalCount base w
  (8+10*printed)+((4+v.channels*(4+rows*(2*score+4)))+
    ((4+n*(2*19+4))+(4+n*(4+((v.channels*v.hosts)*2^v.high)*(2*110+4)))))+
  7*(15*(printed+2)+((15+v.channels*(11+4*score))+((11+4*19)+(15+n*(11+4*110)))))

theorem gl_price (base w : ℕ) (saved : Bank) :
    SignedFields.duration (v.matrix base) (v.chart base) saved (v.joined base) v.channels v.hosts v.high v.low v.bits w+
    7*names (v.basisCode base w saved)≤v.glCost base w :=by
  let C:=v.chart base
  let d:=v.high+v.low
  let n:=(schedule d).length
  let rows:=v.hosts*2^v.high
  let gs:=DescentPackedFlowBatch.passes C.input.base rows rows (v.joined base) 0 v.channels
  let ps:=steps (C.chosen d) (v.channels*v.hosts) (2^v.high) 0 n
  let pre:=(SignedFields.controlBanks (v.matrix base) d).expr (.lookup saved (.lit 0))
  let I:=SignedFields.controlSheet (v.matrix base) d w
  let J:=Dated.routes C (v.channels*v.hosts) v.high v.low v.bits w
  have gTime:=DescentPackedFlowBatch.tariff C.input.base rows rows v.channels (v.joined base) v.retainedFieldWork (v.joined_work base)
  have gNames:=DescentOperandVectorArena.names_passes C.input.base rows rows w v.retainedFieldWork (v.joined base) 0 v.channels
    (fun j _ hj=>v.joined_work base j (by simpa using hj))
  have pTime:=DescentGLPacked.tariff (C.chosen d) (v.channels*v.hosts) v.high 0 n
  have pNames:=step_names (C.chosen d) (v.channels*v.hosts) (2^v.high) n 0 w
  have preWork:pre.work=19:=rfl
  unfold basisCode SignedFields.program
  simp only [names_seq,names_scan]
  change ((8+10*(I.length+J.length))+(clock gs+((4+n*(2*pre.work+4))+clock ps)))+
    7*((names I.program+names J.program)+(names (ProtocolRAM.program w gs)+
          ((11+4*pre.work)+names (ProtocolRAM.program w ps))))≤_
  rw [I.hardware.2,J.hardware.2,preWork]
  dsimp only [glCost,rowCount,literalCount,I,J,C,d,n,rows,gs,ps] at *
  omega

def mountFee (q : ℕ) :=4+10*q+7*(15*(q+1))
def movementFee (base w : ℕ) :=
  (109+v.sources*stripCharge v.hosts v.groups v.previousLanes v.gatherLanes v.wholeWord)+
    mountFee (v.previousNodes*2^(v.wholeWord*v.gatherLanes))+
    mountFee (v.blocks*(2*2^(SignedFields.joinWidth v.bits v.blocks*v.gatherLanes)))+
    v.glCost base w+
    (109+v.channels*stripCharge v.hosts v.grouped v.matrixLanes v.decodedLanes v.stripWord)

theorem moved_price (base w : ℕ) (old : Fin v.sources→Bank) (saved : Bank)
    (a : 0<v.previousLanes) (b : 0<v.gatherLanes) (c : 0<v.matrixLanes) (d : 0<v.decodedLanes) :
    v.movedTicks base w old saved+7*names (v.moved base w old saved)≤v.movementFee base w:=by
  have first:=strip_cost base v.hosts v.groups v.previousLanes v.gatherLanes v.wholeWord w old a b
  change (v.firstCode base w old).ticks+7*names (v.firstCode base w old).program≤_ at first
  have last:=strip_cost (v.mixed base) v.hosts v.grouped v.matrixLanes v.decodedLanes v.stripWord w (v.mixedBank base) c d
  change (v.receiving base w).ticks+7*names (v.receiving base w).program≤_ at last
  have gl:=v.gl_price base w saved
  simp only [movedTicks,moved,basisTicks,basisProgram,digitDict,DescentOrdinaryAtomFieldRAM.ROM.mount,
    blockDict,Book.install,names_seq,names_mount,movementFee,mountFee]
  omega
end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
