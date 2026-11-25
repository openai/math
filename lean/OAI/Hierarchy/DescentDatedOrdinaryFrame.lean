import OAI.Hierarchy.DescentDatedOrdinaryPhase
import OAI.Hierarchy.DescentCensusIngressAnyFrame
import OAI.Hierarchy.DescentPackedPhaseAnyFrame
import OAI.Hierarchy.DescentPreparedAnyFrame

namespace OAI
/-! # The physical write interval of an ordinary calendar date on arbitrary RAM words -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary
open DescentSIMDLookup DescentPackedColony DescentSixParty DescentCompiler ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

variable (a : Ordinary) (i : Operands) (w floor : ℕ)
local notation "M" => a.lanesAt
local notation "r" => 2^a.k
local notation "K" => 2^(a.k+1)
local notation "p" => 2*a.cap
local notation "c" => a.chooser i.roster floor
local notation "rom" => a.prepareAt i.roster floor
local notation "base" => a.sorterAt i.roster floor
local notation "plan" => a.matcher i.roster floor
local notation "port" => i.ports a.D
set_option quotPrecheck false in
local notation "wireBanks" => fun (x : Fin r) (j : Fin p)=>i.wire x.val j.val

private theorem choose_any_framed (hk : 0 < a.k) (safe : Space a i w floor) (m : Memory w) :
    ∃out,((c).program a.D a.k a.b p a.H a.G M w).Exec m out
      ((c).ticks a.D a.k a.b p a.H a.G M w) ∧
      ∀z,z<floor ∨ a.winnerEnd i.roster floor≤z → out z=m z := by
  let u:=(1+a.b+2*p)*r
  have origin:=a.origin_order floor
  have R:=phase_room a i w floor hk safe
  have endRoom:=R.endFits
  have terminal : a.phaseAt floor < 2^w := by
    apply (a.phase_before_winners i.roster floor).trans_lt
    rw [a.phase_lanes] at endRoom
    exact endRoom
  have sourceRoom : (c).source.Fits w (c).chart.weights.base := by
    have pbound : a.page < 2^w := by
      exact (show a.page ≤ a.phaseAt floor from Nat.le_add_left _ _).trans_lt terminal
    exact ⟨Nat.two_pow_pos _,pbound,origin.2.2.1⟩
  have half : M*max u (a.b*r) ≤ w/2 := by
    have inp : u ≤ a.unit := (le_max_right ..).trans safe.chooserWidth
    have fieldWidth : a.b*r ≤ u := Nat.mul_le_mul_right _ (show a.b ≤ 1+a.b+2*p by omega)
    exact (Nat.mul_le_mul_left M (max_le inp (fieldWidth.trans inp))).trans
      ((lanes_fit a.payload a.unit).trans (Nat.div_le_div_right safe.embed))
  have upper : (c).marked.base+a.rows < 2^w := origin.2.2.2.2.trans_lt terminal
  have weight : (c).chart.weights.base+a.rows < 2^w :=
    origin.2.2.2.1.trans_lt ((Nat.le_add_right ..).trans_lt upper)
  obtain ⟨mid,read,readFrame⟩:=PackedCensus.any_framed ((c).census a.k a.b p a.H a.G M false)
    ((c).census a.k a.b p a.H a.G M true)
    (Phase.CensusTables.fits (c).source (c).origin (c).chart.weights.base false sourceRoom a.rows_fit
      (le_refl _) weight half)
    (Phase.CensusTables.fits (c).source (c).origin (c).marked.base true
      (Chooser.bank_before sourceRoom (Nat.le_add_right ..)) a.rows_fit (Nat.le_add_right ..) upper half) m
  have layout:=Phase.Arena.space (c).chart (c).marked hk a.H a.G R
  rw [a.phase_lanes] at layout
  obtain ⟨out,chosen,choiceFrame⟩:=Phase.any_framed ((c).shelves a.D a.k a.b M) layout mid
  refine ⟨out,read.then chosen,?_⟩
  have firstArea : a.phaseAt floor ≤ ((c).shelves a.D a.k a.b M).first := by
    change (c).chart.origin ≤ Phase.Arena.first (c).chart a.D a.k a.b a.phaseWidth
    exact (show (c).chart.origin≤Phase.Arena.menu (c).chart a.D a.k from Nat.le_add_right ..).trans
      ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have chartEnd := a.phase_before_winners i.roster floor
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩:=a.origin_order floor
  intro z hz
  have choiceRead : out z=mid z := by
    apply choiceFrame
    rcases hz with low|high
    · left;omega
    · exact .inr high
  apply choiceRead.trans
  apply readFrame
  · change z<a.weightsAt floor ∨ a.weightsAt floor+a.rows≤z
    omega
  · change z<a.markedAt floor ∨ a.markedAt floor+a.rows≤z
    omega

private def endMemory {w t : ℕ} {cpu : Procedure w} {m out : Memory w} (_ : cpu.Exec m out t) : Memory w := out

/-- This calendar entry executes for its exact published number of ticks on
every initial memory. No semantic stage, seed, path, or validity witness is used. -/
theorem any_framed {F : Type} [Field F] (gadget : PoweredGadget F) (hk : 0 < a.k) (v : Measures)
    (safe : Space a i w floor) (m : Memory w) :
    ∃out,(a.program gadget hk i v w floor).Exec m out (a.ticks gadget hk i v w floor) ∧
      ∀z,z<floor ∨ a.rotationEnd i.roster floor≤z → out z=m z := by
  let ci:=a.censusImage gadget i v w floor
  let pi:=a.chooserImage gadget hk i v w floor
  have B:=subphase_order a i floor
  have phase:=a.phase_before_winners i.roster floor
  have flagRoom : a.flagEnd i.roster floor < 2^w :=
    ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans_lt safe.endAddress
  have last := B.2.2.2.trans_lt flagRoom
  have rem := B.2.2.1.trans_lt last
  have winRoom := B.2.1.trans_lt rem
  have start := B.1.trans (phase.trans B.2.1)
  have low := phase.trans_lt winRoom
  obtain ⟨floorSource,sourceRows,weight,marks,phaseRows⟩:=a.origin_order floor
  have firstEnd : ci.low+ci.length < 2^w := by
    change a.censusAt floor+(a.weightsAt floor-a.censusAt floor) < 2^w
    omega
  have chartEnd : Phase.Arena.first (c).chart a.D a.k a.b a.phaseWidth ≤ a.winnerEnd i.roster floor := by
    change _ ≤ Phase.Arena.endAt (c).chart a.D a.k a.b a.phaseWidth+_
    simp only [Phase.Arena.endAt, Phase.Arena.colorWork, Phase.Arena.selected, Phase.Arena.seedWork, Nat.add_assoc]
    exact Nat.le_add_right ..
  have secondEnd : pi.low+pi.length < 2^w := by
    change a.phaseAt floor+(Phase.Arena.first (c).chart a.D a.k a.b a.phaseWidth-a.phaseAt floor) < 2^w
    omega
  let printed:=pi.output (ci.output m)
  have fixed : (ci.program.seq pi.program).Exec m printed (8+10*(ci.length+pi.length)) := by
    rw [show 8+10*(ci.length+pi.length)=(4+10*ci.length)+(4+10*pi.length) by omega]
    intro pcs regs pubs machine
    exact Procedure.Exec.then (ci.issue m firstEnd).1 (pi.issue (ci.output m) secondEnd).1 machine
  have inputRoom : (c).source.base+a.rows < 2^w := by
    change a.sourceAt floor+a.rows < 2^w
    omega
  obtain ⟨input,inputFrame⟩:=Census.any_framed a.k a.D a.cap a.b a.unit M a.H a.G floor (c).source.base i.hubs
    (fun x=>i.atoms x.val) wireBanks printed safe.inputWidth safe.hubs safe.counts (fun x j=>(safe.wires x j).1)
    (le_refl _) inputRoom
  obtain ⟨selected,elected,electedFrame⟩:=choose_any_framed a i w floor hk safe (endMemory input)
  have access:=Chooser.accessible_before port i.actors safe.accessible start
  have banks : Prepare.ROM.OldRoom i.actors ((c).winners a.D a.k a.b a.H a.G M) wireBanks
      i.roster a.H a.G a.D M w rom :=
    ⟨⟨access.source,access.srcRoom⟩,Chooser.winners_before c a.k a.b a.D a.H a.G M w rom (le_refl _) rem,
      fun x j=>⟨Chooser.bank_before (safe.wires x j).1 start,(safe.wires x j).2⟩,
      ⟨access.roster,access.rosterRoom⟩⟩
  have half: a.unit*M ≤ a.payload/2 := by simpa only [lanesAt,Nat.mul_comm a.unit] using lanes_fit a.payload a.unit
  have bitRoom := half.trans (Nat.div_le_div_right safe.embed)
  have panel : a.panelBits ≤ a.unit := (Nat.le_add_left _ _).trans ((le_max_left ..).trans safe.matchWidth)
  have signed : DescentSignedCableCodec.width a.D a.cap ≤ a.unit :=
    (le_max_right ..).trans ((le_max_right ..).trans safe.inputWidth)
  have key : M*max (DescentSignedCableCodec.width a.D a.cap) a.panelBits ≤ w/2 :=
    (Nat.mul_le_mul_left M (max_le signed panel)).trans (by simpa only [Nat.mul_comm M a.unit] using bitRoom)
  have deg : a.D ≤ a.H*a.D := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right a.D safe.hosts
  have range := max_lt (safe.accessible.offRoom.trans_lt safe.accessible.offsets.2.1)
    ((deg.trans safe.accessible.rosterRoom).trans_lt safe.accessible.roster.2.1)
  obtain ⟨exec,preparedFrame⟩:=Prepared.any_frame (a:=a.k+3) (short:=a.panelBits) a.shapeAt K a.cap a.unit rom a.seats
    port i.actors ((c).winners a.D a.k a.b a.H a.G M) wireBanks banks access key safe.matchWidth bitRoom range last selected
  have birth:=LayoutSum.Finish.width_le a.shapeAt M a.unit a.payload safe.birthWidth half
  obtain ⟨done,report,layoutFrame,_⟩:=LayoutSum.Finish.any_framed a.shapeAt M (plan).layout.topology (plan).layout.out a.batch
    gadget (endMemory exec) (Gather.ROM.column_size _ _) (birth.trans ((Nat.div_le_self ..).trans safe.embed)) flagRoom
  have layout:=Phase.Arena.space (c).chart (c).marked hk a.H a.G (phase_room a i w floor hk safe)
  rw [a.phase_lanes] at layout
  have past : ((c).shelves a.D a.k a.b M).output ≤ a.winnerEnd i.roster floor := Nat.le_add_right ..
  have seed:=layout.final.seed.trans_le (past.trans (B.2.1.trans (B.2.2.1.trans B.2.2.2)))
  have rotate:=DescentExteriorRotationWord.ordinary_fresh hk ((c).shelves a.D a.k a.b M).mu
    (a.flagEnd i.roster floor) done seed safe.endAddress
  refine ⟨endMemory rotate.1, ?_, ?_⟩
  · intro pcs regs pubs machine
    exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then fixed
      (Procedure.Exec.then input (Procedure.Exec.then elected exec))) report) rotate.1 machine
  have oldEnd := (a.packed_last i.roster floor).2
  have batchFits := Nat.le_pow_clog (by decide : 1<2) a.batch
  have preLayout : (plan).endAddr ≤ LayoutSum.Finish.first (plan).layout.topology (plan).layout.out a.batch := by
    change (plan).endAddr ≤ max _ ((plan).layout.out+2^Nat.clog 2 a.batch)
    exact (oldEnd.symm.le.trans (Nat.add_le_add_left batchFits _)).trans (le_max_right ..)
  intro z hz
  have flagPast : a.flagEnd i.roster floor ≤ a.rotationEnd i.roster floor :=
    (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have outside (lo hi : ℕ) (lower : floor ≤ lo) (upper : hi ≤ a.flagEnd i.roster floor) :
      z < lo ∨ hi ≤ z := hz.imp (fun h => h.trans_le lower) (fun h => upper.trans (flagPast.trans h))
  have planPast := B.2.2.2
  have romPast := B.2.2.1.trans planPast
  have winPast := B.2.1.trans romPast
  have phasePast := phase.trans winPast
  have floorToEnd := start.trans B.2.2.1
  have rotRead := rotate.2.2.2 z (hz.imp_left (fun h => h.trans_le (floorToEnd.trans planPast)))
  have layRead := layoutFrame z (outside _ _ (floorToEnd.trans preLayout) (le_refl _))
  have prepRead := preparedFrame z (outside _ _ start planPast)
  have chooseRead := electedFrame z (outside _ _ le_rfl winPast)
  have rowsToPhase : a.sourceAt floor + a.rows ≤ a.phaseAt floor := by omega
  have srcRead := inputFrame z (outside _ _ le_rfl (rowsToPhase.trans phasePast))
  have secondRead := (pi.issue (ci.output m) secondEnd).2.2 z (outside _ _ B.1 (chartEnd.trans winPast))
  have floorToCensus : floor ≤ a.censusAt floor := by omega
  have weightsToPhase : a.weightsAt floor ≤ a.phaseAt floor := by omega
  have firstRead := (ci.issue m firstEnd).2.2 z (outside _ _ floorToCensus (weightsToPhase.trans phasePast))
  exact rotRead.trans (layRead.trans (prepRead.trans (chooseRead.trans (srcRead.trans (secondRead.trans firstRead)))))

theorem any_frame {F : Type} [Field F] (gadget : PoweredGadget F) (hk : 0<a.k) (v : Measures)
    (safe : Space a i w floor) (m : Memory w) (z : ℕ) (outside : z<floor ∨ a.rotationEnd i.roster floor≤z) :
    (a.nativePhase gadget hk i v w floor safe).image m z=m z :=
  (a.nativePhase_report gadget hk i v w floor safe m
    (fun out=>∀x,x<floor ∨ a.rotationEnd i.roster floor≤x → out x=m x)
    (a.any_framed i w floor gadget hk v safe m)) z outside

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary

end OAI
