import OAI.Hierarchy.DescentDatedOrdinaryProgram
import OAI.Hierarchy.DescentPackedCensusAny
import OAI.Hierarchy.DescentPackedPhaseAny
import OAI.Hierarchy.DescentPackedMatchAny

namespace OAI
/-! # Total fixed-time ordinary execution on arbitrary memory -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary
open DescentSIMDLookup DescentPackedColony DescentSixParty DescentCompiler ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 2400000
set_option maxRecDepth 32000

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
local notation "wireBanks" => fun (x : Fin r) (j : Fin p)=>i.wire x.val j.val

/-- This contract contains only public sizes and addresses. In particular every
input value, including every roster entry, is an unrestricted RAM word. -/
structure Space : Prop where
  hosts : 0 < a.H
  chooserWidth : Phase.recordWidth a.k a.b p ≤ a.unit
  inputWidth : max 1 (max a.b (DescentSignedCableCodec.width a.D a.cap)) ≤ a.unit
  matchWidth : Gather.matchUnit a.shapeAt a.panelBits r a.D p ≤ a.unit
  birthWidth : SixBirths.unit a.shapeAt ≤ a.unit
  laneWidth : 2*a.unit ≤ a.payload
  embed : a.payload ≤ w
  accessible : Accessible port i.actors a.H a.G M w floor
  wires : ∀(x : Fin r) (j : Fin p),(i.wire x.val j.val).Fits w floor ∧ a.rows ≤ (i.wire x.val j.val).size
  hubs : i.hubs.Fits w floor
  counts : ∀x : Fin r,(i.atoms x.val).Fits w floor
  endAddress : a.rotationEnd i.roster floor < 2^w

theorem subphase_order :
    floor ≤ a.phaseAt floor ∧ a.winnerEnd i.roster floor ≤ rom ∧ rom ≤ (plan).endAddr ∧
    (plan).endAddr ≤ a.flagEnd i.roster floor := by
  have origin:=a.origin_order floor
  have winner : a.winnerEnd i.roster floor ≤ rom := Nat.le_add_right ..
  have b₀ : rom ≤ base := by
    simp only [sorterAt,Prepare.ROM.sortBase,Nat.add_assoc]
    exact Nat.le_add_right ..
  have b₁ : base ≤ a.matcherAt i.roster floor :=
    (Nat.le_add_right base (Prepare.rosterBank base a.H a.D).size).trans (le_max_right ..)
  have b₂ : a.matcherAt i.roster floor ≤ (plan).raw.base := by
    simp only [matcher,Gather.ROM.place,Gather.ROM.column,Gather.ROM.stop,Nat.add_assoc]
    exact Nat.le_add_right ..
  have b₃ : (plan).raw.base ≤ (plan).endAddr := by
    simp only [matcher,Gather.ROM.place,Gather.ROM.column,Gather.ROM.stop,Nat.add_assoc]
    simp only [Nat.add_le_add_iff_left]
    exact Nat.le_add_right ..
  have last:=(a.packed_last i.roster floor).2
  have pad : a.batch ≤ 2^Nat.clog 2 a.batch := Nat.le_pow_clog (by decide) _
  have flag:=a.flag_at i.roster floor
  exact ⟨by obtain ⟨h₁,h₂,h₃,h₄,h₅⟩:=origin;omega,winner,b₀.trans (b₁.trans (b₂.trans b₃)),by omega⟩

theorem phase_room (hk : 0 < a.k) (safe : Space a i w floor) :
    Phase.Arena.Room (c).chart (c).marked a.D a.k a.b a.phaseWidth w a.H a.G := by
  have B:=subphase_order a i floor
  have stage:=a.phase_before_winners i.roster floor
  have flagRoom : a.flagEnd i.roster floor < 2^w :=
    ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans_lt safe.endAddress
  have avail : rom < 2^w := B.2.2.1.trans_lt (B.2.2.2.trans_lt flagRoom)
  have low : a.phaseAt floor < 2^w := stage.trans_lt (B.2.1.trans_lt avail)
  have U : Phase.unit a.k a.b ≤ a.unit := (le_max_left ..).trans safe.chooserWidth
  have up : 0 < a.unit := (show 0 < Phase.unit a.k a.b by dsimp [Phase.unit];omega).trans_le U
  have lanesPos := (occupancy a.payload a.unit up safe.laneWidth).1
  have mass : a.unit*M ≤ a.payload/2 := by simpa only [lanesAt,Nat.mul_comm a.unit] using lanes_fit a.payload a.unit
  have chunk : a.phaseWidth ≤ w := by
    have h:=(Nat.mul_le_mul_right M U).trans mass
    change 2*Phase.unit a.k a.b*M ≤ w
    rw [Nat.mul_assoc]
    have := safe.embed
    omega
  have wide : 2*Phase.unit a.k a.b ≤ a.phaseWidth :=
    Nat.le_mul_of_pos_right _ lanesPos
  have page : a.page < 2^w := by
    apply LE.le.trans_lt _ low
    exact Nat.le_add_left _ (a.markedAt floor)
  have origin:=a.origin_order floor
  have wf : (c).chart.weights.Fits w (c).chart.origin := by
    exact ⟨Nat.two_pow_pos _,page,(show a.markedAt floor ≤ a.phaseAt floor from Nat.le_add_right ..)⟩
  have mf : (c).marked.Fits w (c).chart.origin := ⟨Nat.two_pow_pos _,page,le_refl _⟩
  have hbits : (c).chart.bits=Frame.pageBits a.H a.G a.k a.b (lanes a.phaseWidth (Phase.unit a.k a.b)) := by
    rw [a.phase_lanes];rfl
  apply Phase.Arena.room_of_page (c).chart (c).marked hk a.H a.G hbits
    (Chooser.bank_before safe.accessible.roster B.1) safe.accessible.rosterRoom wf
  · rw [a.phase_lanes];exact a.rows_fit
  · exact mf
  · rw [a.phase_lanes];exact a.rows_fit
  · exact wide
  · exact chunk
  · rw [a.phase_lanes]
    exact B.2.1.trans_lt avail

private theorem choose_any (hk : 0 < a.k) (safe : Space a i w floor) (m : Memory w) :
    ∃out,((c).program a.D a.k a.b p a.H a.G M w).Exec m out
      ((c).ticks a.D a.k a.b p a.H a.G M w) := by
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
  obtain ⟨mid,read⟩:=PackedCensus.any ((c).census a.k a.b p a.H a.G M false)
    ((c).census a.k a.b p a.H a.G M true)
    (Phase.CensusTables.fits (c).source (c).origin (c).chart.weights.base false sourceRoom a.rows_fit
      (le_refl _) weight half)
    (Phase.CensusTables.fits (c).source (c).origin (c).marked.base true
      (Chooser.bank_before sourceRoom (Nat.le_add_right ..)) a.rows_fit (Nat.le_add_right ..) upper half) m
  have layout:=Phase.Arena.space (c).chart (c).marked hk a.H a.G R
  rw [a.phase_lanes] at layout
  obtain ⟨out,chosen⟩:=Phase.any ((c).shelves a.D a.k a.b M) layout mid
  exact ⟨out,read.then chosen⟩

private def endMemory {w t : ℕ} {cpu : Procedure w} {m out : Memory w} (_ : cpu.Exec m out t) : Memory w := out

/-- This calendar entry executes for its exact published number of ticks on
every initial memory. No semantic stage, seed, path, or validity witness is used. -/
theorem any {F : Type} [Field F] (gadget : PoweredGadget F) (hk : 0 < a.k) (v : Measures)
    (safe : Space a i w floor) (m : Memory w) :
    ∃out,(a.program gadget hk i v w floor).Exec m out (a.ticks gadget hk i v w floor) := by
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
  have input : (a.intake i w floor).Exec printed _ _ := Census.any a.k a.D a.cap a.b a.unit M a.H a.G floor (c).source.base i.hubs
    (fun x=>i.atoms x.val) wireBanks printed safe.inputWidth safe.hubs safe.counts (fun x j=>(safe.wires x j).1)
    (le_refl _) inputRoom
  obtain ⟨selected,elected⟩:=choose_any a i w floor hk safe (endMemory input)
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
  have exec : (a.matchCPU i w floor).Exec selected _ _ := Prepared.any (a:=a.k+3) (short:=a.panelBits) a.shapeAt K a.cap a.unit rom a.seats
    port i.actors ((c).winners a.D a.k a.b a.H a.G M) wireBanks banks access key safe.matchWidth bitRoom range last selected
  have birth:=LayoutSum.Finish.width_le a.shapeAt M a.unit a.payload safe.birthWidth half
  obtain ⟨done,report,_⟩:=LayoutSum.Finish.any a.shapeAt M (plan).layout.topology (plan).layout.out a.batch
    gadget (endMemory exec) (Gather.ROM.column_size _ _) (birth.trans ((Nat.div_le_self ..).trans safe.embed)) flagRoom
  have layout:=Phase.Arena.space (c).chart (c).marked hk a.H a.G (phase_room a i w floor hk safe)
  rw [a.phase_lanes] at layout
  have past : ((c).shelves a.D a.k a.b M).output ≤ a.winnerEnd i.roster floor := Nat.le_add_right ..
  have seed:=layout.final.seed.trans_le (past.trans (B.2.1.trans (B.2.2.1.trans B.2.2.2)))
  have rotate:=DescentExteriorRotationWord.ordinary_fresh hk ((c).shelves a.D a.k a.b M).mu
    (a.flagEnd i.roster floor) done seed safe.endAddress
  refine ⟨endMemory rotate.1, ?_⟩
  intro pcs regs pubs machine
  exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then fixed
    (Procedure.Exec.then input (Procedure.Exec.then elected exec))) report) rotate.1 machine

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary

end OAI
