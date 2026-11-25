import OAI.ThreeFlat.Diagonal.PhysicalBlockLength
import OAI.Hierarchy.GridChosenReceiverSpending
import OAI.Hierarchy.GridChosenReceiverPhases

namespace OAI
/-! # The selected receiver's clock on actual issued factor groups -/

noncomputable section
namespace Hierarchy.GridChosenReceiver

open ThreeFlat Diagonal PhysicalStage Diagonal.HistoryContraction
open RAM RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open TraceDistribution GridScale GridRegisteredSetting GridInstalledEvaluator GridThrough Filter
open TraceFactorReceiver TraceFactorReceiver.Gather
open scoped Classical BigOperators

variable {F : Type} [Field F] [Fintype F] {Q : ℕ→ℕ} {loss : ℕ→ℝ}

omit [Fintype F] in
theorem stage_count (B : Block F) {depth count : ℕ→ℕ} (scale : Scale depth count) :
    ∀ᶠ w : ℕ in atTop,(B.repeat (count w)).length≤w := by
  have small:=(tendsto_order.mp scale.blocks).2 (1/((B.levels:ℝ)+1)) (by positivity)
  filter_upwards [small,eventually_ge_atTop 1] with w compare pos
  have per : (count w:ℝ)<(1/((B.levels:ℝ)+1))*(w:ℝ) :=
    (div_lt_iff₀ (by exact_mod_cast (show 0<w by omega))).mp compare
  have mul : (count w:ℝ)*((B.levels:ℝ)+1)<w := by
    apply (lt_div_iff₀ (by positivity : 0<(B.levels:ℝ)+1)).mp
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using per
  rw [B.length_repeat,Nat.mul_comm]
  exact_mod_cast mul.le

/-- Arbitrary registered groups can use the exact RAM clocks on the original
stage journal and the terminal map. The three terms include all unselected
initialization work even when the chosen tick receives no roots. -/
theorem eventual_slot_spending (B : Block F) (m A : ℕ) (env : Envelopes Q loss)
    (q : ℕ→ℕ) (range : ∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop,∀ (v : TickSelection F (m+1) A w Q loss),v.copies=q w →
      ∀ I : Installed B m A w (degree B) (stageRate B) rootRate v,
      let D:=I.D
      let l:=layout m A w (overhead Q loss w) v.copies (degree B) (stageRate B) rootRate
      ∀ z : D.trace,∀ t : Fin ((l.sideMinusOne+1)^(l.dimension+1)*l.copies),
      let ids:=selectedRoots D l z.1 t
      let rows:=fun i : Fin ids.length=>(D.issuedTree z.1 ids[i]).compile.cells
      28+16*l.pinWidth+((GridReceiverDirectory.prefixTime D l+
        (TraceReceiverElectedCache.replay D l z t+termAllowance D l z.1 ids))+
        Gather.fuel (List.ofFn (rootSpan (TickWorkspace.base (TraceAdmission.receiverAge w) 9) rows)))≤
        setupTime D l+65536*(∑i : Fin ids.length,rootBill D l z.1 ids[i]) := by
  let k:=m+1
  let depth:=fun w=>evalDepth w k A 2 (overhead Q loss w) (q w)
  let n:=fun w=>traceBlocks k (overhead Q loss w)
  have scale : Scale depth n:=trace_scale env k A 2 q range
  filter_upwards [stage_count B scale,RunData.eventual_universal_issued_resources B scale,
    eventually_ge_atTop (max 64 B.stageClockRate)] with w stages charged mature
  intro v copies I D l z t
  have axes : I.axes+1=depth w+1-w/2 := by simpa only [depth,k,←copies] using I.axes_eq
  have cap : GridDescription.capacity w≤64*w := (Nat.div_le_self w 1024).trans (by omega)
  have stageEq : (D.block.repeat D.passes).length = (B.repeat (n w)).length :=
    congrArg₂ (fun (b : Block F) (p : ℕ) => (b.repeat p).length) I.block_eq I.passes_eq
  apply slot_spending D l z t
  · simpa only [D,I.block_eq] using mature
  · exact stageEq.trans_le stages
  · change stageRate B=Gather.fullRate I.D.block.stageClockRate 0
    simp only [I.block_eq,stageRate]
  · rfl
  · intro i
    have bound:=charged D I.block_eq I.passes_eq axes rfl cap cap cap z.1 i
    rw [stageEq]
    simpa only [D,I.block_eq] using bound

end Hierarchy.GridChosenReceiver
end

end OAI
