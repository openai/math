import OAI.Hierarchy.GridChosenReceiverMapReturn
import OAI.Hierarchy.TraceReceiverJournalWires
import OAI.Hierarchy.TraceReceiverRegisteredGeometry

namespace OAI
/-! # Numeric admission for the terminal map at a selected grid receiver -/

noncomputable section
namespace Hierarchy.GridChosenReceiver

open ThreeFlat Diagonal PhysicalStage HistoryContraction RAM
open Computability.VPVNP.BurstRAM PrivateRAM GridScale TraceDistribution GridRegisteredSetting GridInstalledEvaluator
open GridThrough GridReceiverDirectory Filter
open scoped Classical BigOperators Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {w pc regs slots S addr fuel axes : ℕ}
variable (D : RunData F (64*w) pc regs slots S addr fuel axes (w/2)) (l : GridNativeImage.Layout)
set_option quotPrecheck false
local notation "W" => (64*w)
local notation "B" => D.block
local notation "u" => TraceAdmission.receiverAge w
local notation "passes" => ((B).repeat D.passes).length
local notation "unit" => D.issuedUnit w l.degree l.stageRate l.rootRate
local notation "X" => GridReceiverDirectory.archive D l
local notation "stop" => GridReceiverDirectory.native D l

structure TerminalScalars (h : D.run.plan.History) : Prop where
  terminal : (X).TerminalRoom (stop).stages (stop).edges W
  work : ∀ i,D.issuedTreeWork h l.degree l.stageRate l.rootRate i≤D.work h D.issuedCharges unit i
  degree : 2*(D.run.terminalLayer h).degree≤HistoryStageBody.Physical.volume u
  tags : Fintype.card ((Fin 3→Bool)→F)≤2^W
  large : max 64 (B).stageClockRate≤w
  count : passes≤w
  resources : ∀ i,(D.issuedTree h i).resources≤Run.treeFee ((B).localCoefficient*(W+1)^3) passes*D.rawCharge h i

private theorem actual_degree (h : D.run.plan.History) :
    (D.run.terminalLayer h).degree=2^(B).exponent 0 := by
  have e : axes+1=((B).repeat D.passes).charge+(axes+1-((B).repeat D.passes).charge) := by
    rw [(B).charge_repeat]
    have := D.passesFit
    omega
  exact (B).terminalDegree_onLanes _ e h

variable {Q : ℕ→ℕ} {loss : ℕ→ℝ}

set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
theorem eventual_terminal_scalars (blk : Block F) (m A : ℕ) (env : Envelopes Q loss)
    (q : ℕ→ℕ) (range : ∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop,∀ (v : TickSelection F (m+1) A w Q loss),v.copies=q w →
      ∀ (I : Installed blk m A w (degree blk) (stageRate blk) rootRate v)
        (_R : GridInstalledFit.Receipt blk m A w (degree blk) (stageRate blk) rootRate v I reserve 0)
        (_recv : Machine (64*w) (GridDescription.capacity w) (GridDescription.capacity w) (GridDescription.capacity w))
        (_safe : GridNativeDispatch.WordRoom I.D) (z : I.D.trace)
        (_x : GridDiagonal.Pins (Fin (GridControllerSimGeometry.railCount m
          ((layout m A w (overhead Q loss w) v.copies (degree blk) (stageRate blk) rootRate).sideMinusOne)
          ((layout m A w (overhead Q loss w) v.copies (degree blk) (stageRate blk) rootRate).bank))))
        (_c : Cell (m+1) ((layout m A w (overhead Q loss w) v.copies (degree blk) (stageRate blk) rootRate).sideMinusOne))
        (_j : Fin v.copies),
        TerminalScalars I.D (layout m A w (overhead Q loss w) v.copies (degree blk) (stageRate blk) rootRate) z.1 := by
  let k:=m+1
  let depth:=fun w=>evalDepth w k A 2 (overhead Q loss w) (q w)
  let repetitions:=fun w=>traceBlocks k (overhead Q loss w)
  have scale : Scale depth repetitions:=trace_scale env k A 2 q range
  obtain ⟨_,paid⟩:=RunData.eventual_ranked_factor_bounds blk scale (degree blk) (stageRate blk) rootRate
  let cutoff:=max (max 64 blk.stageClockRate) (max (Fintype.card ((Fin 3→Bool)→F)) (2*2^blk.exponent 0))
  filter_upwards [TraceReceiverElectedJournal.eventual_wire_room blk scale,stage_count blk scale,paid,
    RunData.eventual_universal_issued_resources blk scale,eventually_ge_atTop cutoff]
    with w wire stage bounds charged big
  intro v copies I _R _recv _safe z _x _c _j
  let dims:=layout m A w (overhead Q loss w) v.copies (degree blk) (stageRate blk) rootRate
  let gb:=26*GridDescription.sector w
  let ct:=GridNativeDispatch.actualTable I.D _safe
  let room:=GridNativeDispatch.selectorRoom I.D dims _R.table _R.selector _safe
  let sel:=InputWindow I.D dims z _safe room
  let batch:=(_R.rooms _recv 0 gb).choose
  let widths:=fun i=>(v.replacement.width_le_size i).trans v.size_le
  let self:=GridDescription.code (q:=w^2) _recv I.D.machine
  let idWord:=((GridTicks.index (_c,_j)).val:Word (64*w))
  let head:=GridRegisteredPublication.headers (m:=m) (n:=dims.sideMinusOne) (q:=v.copies) I.D
    (GridNativeDispatch.params I.D dims 0 gb) _recv sel _R.text (_c,_j)
  have read : head.length≤dims.pinWidth := (stream_header I _recv 0 gb _R.text batch widths ct.codes room z _x _c _j).1
  have pinFit : dims.pinWidth≤2^w := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have exp := TraceAdmission.receiverAge_lower w
  have stride : (2:ℕ)^w≤TickWorkspace.stride (TraceAdmission.receiverAge w) := by
    change 2^w≤(2^((TraceAdmission.receiverAge w)^10))^4
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have roomHead : 2+head.length≤(archive I.D dims).seed := by
    change 2+head.length≤21*TickWorkspace.stride (TraceAdmission.receiverAge w)
    have := Nat.two_pow_pos w
    omega
  have axis : I.axes+1=depth w+1-w/2 := by simpa only [depth,k,←copies] using I.axes_eq
  have cap : GridDescription.capacity w≤64*w := (Nat.div_le_self w 1024).trans (by omega)
  have resource:=charged I.D I.block_eq I.passes_eq axis rfl cap cap cap z.1
  have bill:=bounds I.D I.block_eq I.passes_eq axis rfl cap cap cap z.1
  have src := @wire
  have sizeBound : max (Fintype.card ((Fin 3→Bool)→F)) (2*2^blk.exponent 0) ≤ w :=
    (le_max_right (max 64 blk.stageClockRate) _).trans big
  have pass : I.D.passes = repetitions w := I.passes_eq
  let headerSize (b : Block F) (n : ℕ) : ℕ := 2+(GridReceiverHeader.header _ _R.text self idWord
    (GridStructuralHeader.parameters b (I.axes+1) n dims.selectorCap
      I.D.machine I.D.fit I.D.field I.D.state 0 gb) sel).length
  have stagesEq := congrArg₂ (fun (b : Block F) (n : ℕ)=>(b.repeat n).length) I.block_eq pass
  simp only [←I.block_eq,←pass] at src
  refine ⟨src I.D.axesFit axis I.D.machine I.D.fit I.D.field I.D.state I.D.passesFit
      dims sel _R.text self idWord ?_,fun i=>(bill.2 i).1,?_,?_,?_,?_,?_⟩
  · exact (congrArg₂ headerSize I.block_eq.symm pass.symm).le.trans roomHead
  · have eqn : (I.D.run.terminalLayer z.1).degree=2^blk.exponent 0 :=
      (actual_degree I.D z.1).trans (congrArg (fun b : Block F=>2^b.exponent 0) I.block_eq)
    have enough : 2*2^blk.exponent 0≤w := (le_max_right _ _).trans sizeBound
    calc
      2*(I.D.run.terminalLayer z.1).degree = 2*(2^blk.exponent 0) := congrArg (2*·) eqn
      _ ≤ w := enough
      _ ≤ 2^w := Nat.lt_two_pow_self.le
      _ ≤ 2^((TraceAdmission.receiverAge w)^10) := Nat.pow_le_pow_right (by decide)
        ((Nat.le_mul_of_pos_left w (by decide : 0 < 4)).trans exp)
  · have enough : Fintype.card ((Fin 3→Bool)→F)≤w := (le_max_left _ _).trans sizeBound
    exact enough.trans (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide)
      (Nat.le_mul_of_pos_left w (by decide : 0<64))))
  · exact (congrArg (fun b : Block F => max 64 b.stageClockRate) I.block_eq).le.trans
      ((le_max_left _ _).trans big)
  · exact stagesEq.le.trans stage
  · intro i
    exact (resource i).trans (congrArg₂ (fun (b : Block F) (n : ℕ)=>
      Run.treeFee (b.localCoefficient*(64*w+1)^3) (b.repeat n).length*I.D.rawCharge z.1 i)
      I.block_eq.symm pass.symm).le

end Hierarchy.GridChosenReceiver
end

end OAI
