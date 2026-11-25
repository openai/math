import OAI.Hierarchy.GridChosenReceiverInstalledPrefix
import OAI.Hierarchy.TraceReceiverDescendantExecution
import OAI.Hierarchy.TraceReceiverSlotRows

namespace OAI
/-! # Running a paid receiving tick through its native instruction sequence -/

noncomputable section
namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal Diagonal.HistoryContraction Diagonal.PhysicalStage
open RAM RAM.PhysicalProcedure RAM.TickTerminalRoot Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution GridScale GridThrough GridRegisteredSetting GridInstalledEvaluator
open TraceFactorReceiver TraceFactorReceiver.Gather
open scoped BigOperators Classical

variable {F : Type} [Field F] [Fintype F] {w pc rr pp S base fuel axes : ℕ}
variable (D : RunData F (64*w) pc rr pp S base fuel axes (w/2)) (l : GridNativeImage.Layout)
set_option quotPrecheck false
local notation "W" => (64*w)
local notation "V" => TraceAdmission.receiverAge w
local notation "dir" => GridReceiverDirectory.native D l
local notation "receiverParams" => (dir).parameters
local notation "receiverArena" => GridReceiverBanks.arena D l

def descendants :=
  TraceReceiverDescendantExecution.program D l (receiverParams).firstFinal (receiverParams).roots (GridReceiverBanks.pinPlan D l)

def terminal :=
  TraceReceiverProgram.terminal w V (SelfAdvice.textSize W pc pp) (receiverParams).roots ((l.dimension+1)+2)
    (GridReceiverBanks.limit w) (GridReceiverBanks.tasks w) receiverArena ((receiverArena).control+1)
    (GridReceiverBanks.mapHeader w) (GridReceiverBanks.commands w) (GridReceiverBanks.cursor w)
    (GridReceiverBanks.width w)

theorem source_parts :
    source D l=(GridReceiverDirectory.prefixProgram D l).seq ((descendants D l).seq (terminal D l)) := rfl

/-- The native templates and stored maps may use intermediate memory in their
proofs. Each witness stays associated with the very execution that issued it. -/
theorem phases {initial : Memory W} {eligible : Memory W→Prop}
    {cache : Memory W→Memory W→Prop} {prepared : Memory W→Prop} {navCost compileCost termCost : ℕ}
    (navigate : (GridReceiverDirectory.prefixProgram D l).Spec (·=initial) (fun _=>eligible) navCost)
    (compile : ∀ m,eligible m → (descendants D l).Spec (·=m) (fun _=>cache m) compileCost)
    (maps : ∀ m q,eligible m → cache m q → (terminal D l).Spec (·=q) (fun _=>prepared) termCost) :
    (source D l).Spec (·=initial) (fun _=>prepared) (navCost+(compileCost+termCost)) := by
  let stored:=fun q=>∃ m,eligible m ∧ cache m q
  have compile' : (descendants D l).Spec eligible (fun _=>stored) compileCost := by
    intro p r k M loc R K exit installed pub cfg mem entry ok
    obtain ⟨t,paid,endCfg,out,run,arrived,written⟩:=
      compile mem ok M loc R K exit installed pub cfg mem entry rfl
    exact ⟨t,paid,endCfg,out,run,arrived,mem,ok,written⟩
  have maps' : (terminal D l).Spec stored (fun _=>prepared) termCost := by
    intro p r k M loc R K exit installed pub cfg mem entry ok
    obtain ⟨m,yes,issued⟩:=ok
    exact maps m mem yes issued M loc R K exit installed pub cfg mem entry rfl
  have tail : ((descendants D l).seq (terminal D l)).Spec eligible (fun _=>prepared) (compileCost+termCost) := by
    intro labels regs slots machine
    exact Procedure.Spec.mono (Procedure.Spec.seq compile' maps' (fun _ _ h=>h))
      (fun _ h=>h) (fun _ _ ⟨_,_,ready⟩=>ready) le_rfl machine
  rw [source_parts]
  intro labels regs slots machine
  exact Procedure.Spec.mono (Procedure.Spec.seq navigate tail (fun _ _ h=>h))
    (fun _ h=>h) (fun _ _ ⟨_,_,ready⟩=>ready) le_rfl machine

/-- Pay a heterogeneous forest after its original head switch, independent
selection, root assembly, map publication, gathering, padding and RAM evaluation. -/
theorem paid_phases {«p» n : ℕ} {arity : Fin n→ℕ} (trees : ∀ i,Tree F (arity i))
    (wire : ∀ i, Fin (arity i)→Fin «p») (pins : Fin «p»→Bool) (spans : List Gather.Span)
    (clk setup navCost compileCost termCost : ℕ) (fee : Fin n→ℕ)
    (sizes : ∀ i,10000*((trees i).compile.cells+(trees i).compile.internal)≤fee i)
    (tariff : reserve*(∑ i,fee i)≤clk) (startup : 4*setup≤clk) (field : 4*fieldCost F≤clk)
    (combined : 28+16*«p»+((navCost+(compileCost+termCost))+Gather.fuel spans)≤ setup+65536*(∑ i,fee i))
    (eligible : Memory W→Prop) (cache : Memory W→Memory W→Prop)
    (navigate : (GridReceiverDirectory.prefixProgram D l).Spec (·=TickMountedPins.memory (w:=W) pins)
      (fun _=>eligible) navCost)
    (compile : ∀ m,eligible m → (descendants D l).Spec (·=m) (fun _=>cache m) compileCost)
    (maps : ∀ m q,eligible m → cache m q → (terminal D l).Spec (·=q) (fun _ out=>
      Gather.Prepared (fun i=>(trees i).compile) (ctrl:=GridReceiverBanks.cursor w)
        (control:=TickWorkspace.base V 18) (atCmd:=GridReceiverBanks.commands w) (H:=clk/40000)
        wire pins (TickWorkspace.base V 9) spans out) termCost) :
    let N:=forest (fun i=>(trees i).compile) wire
    let H:=clk/40000
    let J:=2*H
    let pad:=H-N.internal
    let fill:=J-(N.cells+pad)
    N.internal≤H ∧ N.cells+pad≤J ∧
    (source D l).Spec (·=TickMountedPins.memory (w:=W) pins) (fun _ out=>
      Gather.Prepared (fun i=>(trees i).compile) (ctrl:=GridReceiverBanks.cursor w)
        (control:=TickWorkspace.base V 18) (atCmd:=GridReceiverBanks.commands w) (H:=H)
        wire pins (TickWorkspace.base V 9) spans out) (navCost+(compileCost+termCost)) ∧
    (28+16*«p»+((navCost+(compileCost+termCost))+Gather.fuel spans)+TickTerminalPadding.budget F pad fill)+
      evalCost F H J≤clk := by
  intro N H J pad fill
  obtain ⟨bits,rows,clock⟩:=slot_clock (fun i=>(trees i).compile) wire fee sizes tariff startup field combined
  exact ⟨bits,rows,phases D l navigate compile maps,clock⟩

variable {Q : ℕ→ℕ} {loss : ℕ→ℝ}

/-- The charged work in a receiver's S43 column pays for every real row
and hidden Boolean in that root's assembled tree. -/
theorem eventual_slot_rows (blk : Block F) (m «A» : ℕ) (env : Envelopes Q loss) (q : ℕ→ℕ)
    (range : ∀ᶠ w : ℕ in Filter.atTop,0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in Filter.atTop,∀ v : TickSelection F (m+1) «A» w Q loss,v.copies=q w →
      ∀ I : Installed blk m «A» w (degree blk) (stageRate blk) rootRate v,
      ∀ h i,10000*((I.D.issuedTree h i).compile.cells+(I.D.issuedTree h i).compile.internal)≤
        I.D.work h I.D.issuedCharges (I.D.issuedUnit w (degree blk) (stageRate blk) rootRate) i := by
  let k:=m+1
  let depth:=fun w=>evalDepth w k «A» 2 (overhead Q loss w) (q w)
  let n:=fun w=>traceBlocks k (overhead Q loss w)
  have scale : Scale depth n:=trace_scale env k «A» 2 q range
  obtain ⟨_,charge⟩:=RunData.eventual_ranked_factor_bounds blk scale (degree blk) (stageRate blk) rootRate
  filter_upwards [charge] with w paid
  intro v same I h i
  have axes : I.axes+1=depth w+1-w/2 := by simpa only [depth,k,←same] using I.axes_eq
  have capacity : GridDescription.capacity w≤64*w:=(Nat.div_le_self w 1024).trans (by omega)
  have bounds:=(paid I.D I.block_eq I.passes_eq axes rfl capacity capacity capacity h).2 i
  exact Gather.forest_tariff (I.D.issuedTree h i) bounds.1

end Hierarchy.GridChosenReceiver
end

end OAI
