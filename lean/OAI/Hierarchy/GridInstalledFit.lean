import OAI.Hierarchy.GridNativeDispatch
import OAI.Hierarchy.GridPhysicalSelector
import OAI.Hierarchy.GridInstalledSmall
import OAI.Hierarchy.GridRegisteredIssuedRoom

namespace OAI
/-! # Native dispatch bounds for the single padded grid evaluator -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridInstalledFit

open ThreeFlat Diagonal Diagonal.PhysicalStage RAM
open GridScale Filter GridInstalledEvaluator GridRegisteredSetting TraceDistribution
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators

variable {F : Type} [Field F] [Fintype F] (blk : Block F)
variable {Q : ℕ→ℕ} {loss : ℕ→ℝ} (m A w degree stageRate rootRate : ℕ)
variable (v : TickSelection F (m+1) A w Q loss)
local notation "ageAtScale" => overhead Q loss w
local notation "activeLayout" => layout m A w ageAtScale v.copies degree stageRate rootRate
local notation "rateCoefficient" => GridInstalledSmall.coefficient blk degree stageRate rootRate
variable (I : Installed blk m A w degree stageRate rootRate v)
local notation "activeRun" => I.D
local notation "unit" => I.D.issuedUnit w degree stageRate rootRate

/-- Both the selected header and the work lists use the stage table and the
actual ordinal of the installed machine at this word length. -/
structure Receipt (J r : ℕ) where
  fits : GridNativeDispatch.Fits activeRun activeLayout v.replacement rateCoefficient 2
  table : GridNativeDispatch.Tables activeRun
  selector : GridSelector.Room (activeRun).run.plan table.codes
    (GridPhysicalSelector.bits (activeRun).run) (activeLayout).selectorCap
  text : (activeLayout).receiverText≤w^2
  sites : ∀ h : (activeRun).run.plan.History, (activeRun).roots h≤2^(3*w/5)
  rooms : ∀ {rc kc : ℕ} (recv : Machine (64*w) (activeLayout).receiverPC rc kc) (raw gateBase : ℕ),
    ∃ rooms : GridNativeDispatch.Rooms activeRun activeLayout recv raw gateBase text,
      ∀ (s : Fin ((activeLayout).selectorCap+1)→Bool) (z : (activeRun).trace), (rooms s z).cap=2^(3*w/5) ∧
        ∀ t : GridThrough.Cell (m+1) (activeLayout).sideMinusOne × Fin v.copies,
          J*(w+1)^r*((FactorAllocation.factors w
            ((activeRun).costs (GridNativeImage.resources activeRun activeLayout) z.1 m
              (activeLayout).sideMinusOne (activeLayout).bank (activeRun).issuedCharges unit)
            (List.finRange ((activeRun).roots z.1)) (GridTicks.index t)).map
              fun i => (activeRun).work z.1 (activeRun).issuedCharges unit i).sum ≤
            UniversalTick.clock w UniversalTick.saving

private theorem native_table (env : Envelopes Q loss) (q : ℕ→ℕ)
    (range : ∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop, ∀ (v : TickSelection F (m+1) A w Q loss) (_chosen : v.copies=q w)
      (I : Installed blk m A w degree stageRate rootRate v),
      ∃ table : GridNativeDispatch.Tables I.D,
        GridSelector.Room I.D.run.plan table.codes (GridPhysicalSelector.bits I.D.run)
          (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate).selectorCap ∧
          ∀ h : I.D.run.plan.History, I.D.roots h≤2^(3*w/5) := by
  filter_upwards [GridPhysicalSelector.native_codec blk env (m+1) A 2 q range,
    GridPhysicalSelector.physical_factor_budget blk (trace_scale env (m+1) A 2 q range)] with w native counts
  intro v _chosen I
  have cpu : GridDescription.capacity w≤64*w := (Nat.div_le_self w 1024).trans (by omega)
  dsimp only at native counts
  rw [←_chosen] at native counts
  let a := overhead Q loss w
  let arch := GridDescription.capacity w
  have select {S base fuel axes : ℕ} (D : RunData F (64*w) arch arch arch S base fuel axes (w/2))
      (b : D.block=blk) (p : D.passes=traceBlocks (m+1) a)
      (dim : axes+1=evalDepth w (m+1) A 2 a v.copies+1-w/2) :
      ∃ table : GridNativeDispatch.Tables D,
        GridSelector.Room D.run.plan table.codes (GridPhysicalSelector.bits D.run) (selector (m+1) w a-1) ∧
          ∀ h : D.run.plan.History, D.roots h≤2^(3*w/5) := by
    obtain ⟨M,fit,hf,state,block,hk,passes,passed⟩ := D
    change block=blk at b
    change passes=traceBlocks (m+1) a at p
    subst block passes
    obtain ⟨book⟩ := native cpu cpu cpu hk dim M fit hf state passed
    exact ⟨book.table,book.room,fun h => (counts hk dim M fit hf state passed h).1⟩
  exact select I.D I.block_eq I.passes_eq I.axes_eq



private theorem dispatch_fits (env : Envelopes Q loss) (q : ℕ→ℕ)
    (range : ∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop, ∀ (v : TickSelection F (m+1) A w Q loss),v.copies=q w→
      ∀ I : Installed blk m A w degree stageRate rootRate v,
      GridNativeDispatch.Fits I.D (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate)
        v.replacement (GridInstalledSmall.coefficient blk degree stageRate rootRate) 2 := by
  let k:=m+1
  let coefficient:=GridStructuralHeader.coefficient blk
  filter_upwards [GridInstalledSmall.eventual blk env m A degree stageRate rootRate q range,
    GridCompilerAdmission.selected_space (F:=F) env A k (Nat.succ_pos m),
    GridSelfHeader.raw_room_of_poly env k A 2 coefficient 14 (Nat.succ_pos m),
    header_room env k A (Nat.succ_pos m), depth_range env k A 0, sublinear env (10*k+3),
    eventually_ge_atTop (m+1024)] with w localRoom spaces raws geometry depths overheadFit age
  intro v chosen I
  let a := overhead Q loss w
  let l := GridInstalledEvaluator.layout m A w a v.copies degree stageRate rootRate
  let E := external k a (pairs A w v.copies)
  have pages := spaces v.copies v.copies_pos v.copies_le v.replacement v.size_le
  have rawRoom := (raws v.copies v.copies_pos v.copies_le
    (GridNativeImage.parameterCount I.D l) I.parameters_le).2.1
  have enough := localRoom v chosen I
  have pairsFit : 0<l.bank := (geometry v.copies v.copies_pos v.copies_le l.bank (by simp [l,GridInstalledEvaluator.layout,a])).1
  have baseTwo : l.sideMinusOne+1=2^l.logRadix := Nat.sub_add_cancel (Nat.two_pow_pos _)
  have cpu : 1≤w := by omega
  have dep := (depths v.copies v.copies_pos v.copies_le).2
  change evalDepth w k A 0 a v.copies ≤ w+(10*k+3)*a at dep
  change (10*k+3)*a≤w at overheadFit
  have volume : (l.sideMinusOne+1)^k*l.bank≤2^(2*w) := by
    rw [baseTwo]
    calc
      _ = evalWork w k A 0 a v.copies := by simp [evalWork,l,GridInstalledEvaluator.layout,side]
      _ ≤ 2^(2*w) := (Nat.lt_log2_self.le).trans (Nat.pow_le_pow_right (n:=2) (by decide)
        (show evalDepth w k A 0 a v.copies≤2*w by omega))
  have idle := GridControllerIdle.fits_from_pages (m:=m) (n:=l.sideMinusOne)
    (B:=l.bank) (logRadix:=l.logRadix) (pc:=l.receiverPC) v.replacement
    (by change GridControllerSimGeometry.railCount m (side a-1) l.bank≤_; rw [rails]; exact pages.rails)
    pages.axes pages.pinData pages.compact cpu pairsFit v.copies_pos v.size_le baseTwo volume le_rfl
  have capFit : selector k w a-1<GridDescription.sector w := by
    have h : selector k w a≤2^w := Nat.pow_le_pow_right (n:=2) (by decide) (Nat.sub_le ..)
    have larger : 2^w<GridDescription.sector w :=
      Nat.pow_lt_pow_right (by decide : 1<2) (show w<32*w by omega)
    omega
  have dimension : l.dimension+1 ≤ w := by change m+1 ≤ w; omega
  refine ⟨dimension,I.cutoff,pairsFit,Nat.mul_pos v.copies_pos (Nat.two_pow_pos _),capFit,
    ?_,?_,enough.degree,enough.setup,enough.maps,enough.small,idle.1,idle.2,?_⟩
  · simpa only [k,l,a,GridInstalledEvaluator.layout,GridInstalledEvaluator.rails] using rawRoom
  · simpa only [GridInstalledEvaluator.layout,GridInstalledEvaluator.rails] using I.input_eq
  · simpa only [GridInstalledEvaluator.layout,GridInstalledEvaluator.rails] using pages



/-- For each installed evaluator, every valid selector can use the same real
record table and the registered work fits the selected tick's clock. -/
theorem eventual (env : Envelopes Q loss) (q : ℕ→ℕ)
    (range : ∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) (J r : ℕ)
    (saving : UniversalTick.saving+2+(r+51)<A) :
    ∀ᶠ w : ℕ in atTop, ∀ (v : TickSelection F (m+1) A w Q loss),v.copies=q w→
      ∀ I : Installed blk m A w degree stageRate rootRate v, Nonempty (Receipt blk m A w degree stageRate rootRate v I J r) := by
  let k:=m+1
  let coeff:=GridStructuralHeader.coefficient blk
  obtain ⟨C,est⟩ := eventual_issued_on blk env m A 2 coeff 14 q range degree stageRate rootRate
  filter_upwards [est,eventual_tick_work (F:=F) env m A 2 C J r saving,
    native_table blk m A degree stageRate rootRate env q range,
    dispatch_fits blk m A degree stageRate rootRate env q range,eventually_ge_atTop 1024]
    with w est work tables bounds age
  intro v chosen I
  let a:=overhead Q loss w
  let l:=layout m A w a v.copies degree stageRate rootRate
  have gpos : 0 < selector k w a := Nat.two_pow_pos _
  have selectorLength : l.selectorCap+1=selector k w a := Nat.sub_add_cancel gpos
  have cpu : GridDescription.capacity w≤64*w := (Nat.div_le_self w 1024).trans (by omega)
  have text : l.receiverText≤w^2 := by
    have both := (GridDescription.room (w:=w) age le_rfl le_rfl le_rfl le_rfl).room
    change SelfAdvice.textSize (64*w) (GridDescription.capacity w) (GridDescription.capacity w)≤_
    omega
  obtain ⟨table,fit,sites⟩ := tables v chosen I
  refine ⟨⟨bounds v chosen I,table,fit,text,sites,?_⟩⟩
  intro rc kc recv raw gateBase
  let pp := GridNativeDispatch.params I.D l raw gateBase
  let issued := I.D.issuedUnit w degree stageRate rootRate
  dsimp only at est
  rw [←chosen] at est
  have run := est (GridNativeImage.parameterCount I.D l) l.receiverText (l.selectorCap+1)
    I.parameters_le text selectorLength I.D I.input_eq I.block_eq I.passes_eq I.axes_eq cpu cpu cpu
  let code := GridDescription.code (q:=w^2) recv I.D.machine
  have each (s : Fin (l.selectorCap+1)→Bool) (z : I.D.trace) := run z.1 code pp s
  choose rooms hroom using each
  refine ⟨rooms,fun s z => ⟨(hroom s z).1,?_⟩⟩
  intro t
  exact work v.copies v.copies_pos v.copies_le I.D (GridNativeImage.resources I.D l)
    z.1 I.D.issuedCharges issued _ (rooms s z) (hroom s z).1 (hroom s z).2 t


end Hierarchy.GridInstalledFit
end

end OAI
