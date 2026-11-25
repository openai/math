import OAI.Hierarchy.DescentFundedMixerReturn
import OAI.Hierarchy.DescentFundedCensusInvoice
import OAI.Hierarchy.DescentOverlapTariff
import OAI.Hierarchy.DescentPackedMatchedAll

namespace OAI
/-! # Native clocks and program size of the complete paid input transformation -/
namespace Hierarchy.DescentFundedCensus.Setup
open DescentSIMDLookup DescentSIMDLookup.Overlap DescentPackedZip DescentPackedColony
open DescentGLPacked DescentGLPacked.BankImage DescentGLNielsen DescentGLControlCode DescentGL
open DescentSixParty.Chronology DescentResetRetainedSetup DescentPacking.PackedMatch.Local
open DescentStaticWordColumn (names names_seq names_scan names_mount)
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (s : DescentFundedCensus.Setup) {w : ℕ}

def stripCharge :=2048*((pieces s.oldGroups s.oldLanes s.gatherLanes+1)*(s.oldLanes+1)*2^(s.precision*s.oldLanes)+
  Overlap.rows s.hosts s.oldGroups s.oldLanes+Overlap.rows s.hosts s.oldGroups s.gatherLanes+1)

theorem strip_invoice (base w : ℕ) (old : Fin s.blocks→Bank) (before : 0<s.oldLanes) (after_ : 0<s.gatherLanes) :
    (s.copy base w old).ticks+7*names (s.copy base w old).program≤109+s.blocks*s.stripCharge :=by
  have each (bs : List Bank) (loc : ℕ) :
      let p:=Books.phase w loc (bs.map (Strip.one s.hosts s.oldGroups s.oldLanes s.gatherLanes s.precision))
      p.ticks+7*names p.program≤109+bs.length*s.stripCharge :=by
    induction bs generalizing loc with
    | nil=>
      change 4+7*names (scan w 0 0 (.lit 0))≤109+0*s.stripCharge
      rw [names_scan,Nat.zero_mul];decide
    | cons b bs ih=>
      let item:=Strip.one s.hosts s.oldGroups s.oldLanes s.gatherLanes s.precision b
      have one:=Overlap.tariff loc s.hosts s.oldGroups s.oldLanes s.gatherLanes s.precision w b before after_
      have next:=ih (item.limit loc)
      simp only [List.map_cons,Books.phase,NativePhase.seq,names_seq,List.length_cons]
      rw [Nat.succ_mul bs.length]
      change (item.phase loc w).ticks+_+7*(names (item.phase loc w).program+_)≤_
      change (item.phase loc w).ticks+7*names (item.phase loc w).program≤ s.stripCharge at one
      dsimp only [item] at one next ⊢
      omega
  simpa only [copy,Strip.code,List.length_ofFn] using each (List.ofFn old) base

def fieldWork :=1+s.blocks*18
theorem selector_work (base j : ℕ) (range_ : j<1) : (s.selector base j).work≤ s.fieldWork :=by
  unfold selector SignedFields.joinOp
  rw [dite_eq_left range_]
  simpa [Gather.assembly,fieldWork] using Gather.collect_work _ (s.prior base ⟨j,range_⟩)
    (List.finRange s.blocks) 7 (fun _=>by change 7 ≤ 7; decide)

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

def printed (base w : ℕ) :=
  (SignedFields.controlSheet (s.matrix base) (s.high+s.low) w).length+
  (Dated.routes (s.plan base) (1*s.hosts) s.high s.low s.precision w).length

/-- Both literal GL images lie in disjoint parts of the charged arena. -/
theorem printed_bound (base w : ℕ) : s.printed base w≤ s.roof 0 :=by
  let C:=s.plan base
  let d:=s.high+s.low
  let stop:=s.signedEnd base
  obtain ⟨valid,control,_,_,_⟩:=SignedFields.allocation (s.matrix base) 1 s.hosts s.high s.low s.precision stop
    (show stop<2^stop from Nat.lt_two_pow_self)
  have lo: s.matrix base≤SignedFields.controlEnd (s.matrix base) d:=by unfold SignedFields.controlEnd;omega
  change SignedFields.controlEnd (s.matrix base) d ≤ C.input.base at control
  have inputSum : C.input.base+C.input.size≤C.start := valid.input.2.2
  have input: C.input.base≤C.start:=(Nat.le_add_right ..).trans inputSum
  have start: C.start≤C.heap d:=Nat.le_add_right ..
  have finish: C.heap d≤ s.signedEnd base:=Nat.le_add_right ..
  have end_:=s.order base
  have aff:=s.shift base
  change (SignedFields.controlEnd (s.matrix base) d-s.matrix base)+(C.heap d-C.start)≤ s.roof 0
  omega

def passesTime :=
  let rows:=s.hosts*2^s.high
  let n:=(schedule (s.high+s.low)).length
  (4+1*(4+rows*(2*s.fieldWork+4)))+((4+n*(2*19+4))+(4+n*(4+rows*(2*110+4))))

def passesNames :=
  let n:=(schedule (s.high+s.low)).length
  (15+1*(11+4*s.fieldWork))+((11+4*19)+(15+n*(11+4*110)))

theorem shuffle_invoice (base w : ℕ) (key : Bank) :
    let joins:=s.blocks*(2*2^(SignedFields.joinWidth s.precision s.blocks*s.gatherLanes))
    s.shuffleTime w base key≤(4+10*joins)+(8+10*s.printed base w+s.passesTime) ∧
    names (s.shuffle w base key)≤15*(joins+1)+(15*(s.printed base w+2)+s.passesNames) :=by
  intro joins
  let d:=s.high+s.low
  let n:=(schedule d).length
  let C:=s.plan base
  let rows:=s.hosts*2^s.high
  let I:=SignedFields.controlSheet (s.matrix base) d w
  let J:=Dated.routes C (1*s.hosts) s.high s.low s.precision w
  let old:=s.selector base
  let gs:=DescentPackedFlowBatch.passes C.input.base rows rows old 0 1
  let ps:=steps (C.chosen d) (1*s.hosts) (2^s.high) 0 n
  let pre:=(SignedFields.controlBanks (s.matrix base) d).expr (.lookup key (.lit 0))
  have term : pre.work=19:=rfl
  have gTime:=DescentPackedFlowBatch.tariff C.input.base rows rows 1 old s.fieldWork (s.selector_work base)
  have pTime:=DescentGLPacked.tariff (C.chosen d) (1*s.hosts) s.high 0 n
  have pTicks : clock ps ≤ 4+n*(4+rows*(2*110+4)) := by
    simpa only [ps,rows,Nat.one_mul] using pTime
  have gNames : names (ProtocolRAM.program w gs)≤15+1*(11+4*s.fieldWork):=by
    have cheap : (old 0).work ≤ s.fieldWork := s.selector_work base 0 (by decide)
    simp only [gs,DescentPackedFlowBatch.passes,ProtocolRAM.program,names_seq,Pass.procedure,names_scan]
    change 11+4*(old 0).work+15≤_
    omega
  have pNames:=step_names (C.chosen d) (1*s.hosts) (2^s.high) n 0 w
  change names (ProtocolRAM.program w ps) ≤ 15+n*(11+4*110) at pNames
  constructor
  · change (4+10*joins)+((8+10*(I.length+J.length))+(clock gs+((4+n*(2*pre.work+4))+clock ps)))≤_
    rw [term]
    exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add gTime (Nat.add_le_add_left pTicks _)) _) _
  · simp only [shuffle,SignedFields.program,names_seq,Book.names,names_scan]
    change 15*(joins+1)+(names I.program+names J.program+
      (names (ProtocolRAM.program w gs)+((11+4*pre.work)+names (ProtocolRAM.program w ps))))≤_
    rw [I.hardware.2,J.hardware.2,term]
    change _≤15*(joins+1)+(15*(I.length+J.length+2)+((15+1*(11+4*s.fieldWork))+((11+4*19)+(15+n*(11+4*110)))))
    omega

theorem invoice (base w : ℕ) (old : Fin s.blocks→Bank) (key : Bank) (before : 0<s.oldLanes) (after_ : 0<s.gatherLanes) :
    let joins:=s.blocks*(2*2^(SignedFields.joinWidth s.precision s.blocks*s.gatherLanes))
    s.ticks w base old key+7*names (s.program w base old key)≤
      (109+s.blocks*s.stripCharge)+
      ((4+10*joins)+(8+10*s.printed base w+s.passesTime))+7*(15*(joins+1)+(15*(s.printed base w+2)+s.passesNames))+
      ((4+10*2^s.flagWidth)+7*(15*(2^s.flagWidth+1))) :=by
  intro joins
  have cp:=s.strip_invoice base w old before after_
  obtain ⟨gl,tex⟩:=s.shuffle_invoice base w key
  unfold ticks program
  simp only [names_seq,Arrivals.program,DescentOrdinaryAtomFieldRAM.ROM.mount,names_mount,Nat.one_mul]
  change _+7*(_+15*(2^s.flagWidth+1))≤_
  omega

end
end Hierarchy.DescentFundedCensus.Setup

end OAI
