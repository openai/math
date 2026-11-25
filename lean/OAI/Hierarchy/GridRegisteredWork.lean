import OAI.Hierarchy.GridRegisteredRunData
import OAI.Hierarchy.TraceNativeAdmittedWork

namespace OAI
/-! # Work of the actual ranks issued in the physical register -/

namespace Hierarchy.GridRegisteredSetting.RunData
open ThreeFlat Diagonal Diagonal.PhysicalStage
open TraceDistribution TraceFactorReceiver.Gather Computability.VPVNP.BurstRAM PrivateRAM Filter
open scoped BigOperators Classical
noncomputable section

variable {F : Type} [Field F] [Fintype F] {W pc regs words S base fuel axes low : ℕ}

/-- The actual assembler and charge column transported to the same native `D.run`. -/
def issuedRegister (D : RunData F W pc regs words S base fuel axes low) :
    D.run.Assembler (Fin S→Bool) × D.run.Charges :=
  let p:=D.block.repeat D.passes
  let rem:=axes+1-p.charge
  have e : axes+1=p.charge+rem := by
    dsimp [p,rem]
    rw [D.block.charge_repeat]
    have := D.passesFit
    omega
  let d:=(axes+1)+low
  let grid:=TraceStaticRow.gateTable D.field D.fit.width D.fit.labels base fuel D.state regs words d
  let X:=D.block.cursorState D.axesFit low (1+(d+d)) grid.cells
  Physical.registerOnLanes D.block (Fin S→Bool) D.passes rem X e

def issuedCharges (D : RunData F W pc regs words S base fuel axes low) : D.run.Charges :=
  D.issuedRegister.2

/-- Terminal pin layout and forest constructed by the same physical word assembler as
the charge register. -/
def issuedForest (D : RunData F W pc regs words S base fuel axes low) (h : D.run.plan.History) :=
  let L := TraceReceiverSeedWords.wordsLayout D.machine D.fit D.field D.state D.block D.axesFit
  let N := TraceReceiverSeedWords.forest D.machine D.fit D.field D.state D.block D.axesFit
  D.run.plan.assemble h (D.run.wordAssembly D.issuedRegister.1.steps L) N

def issuedTree (D : RunData F W pc regs words S base fuel axes low)
    (h : D.run.plan.History) (i : Fin (D.roots h)) :=
  (D.issuedForest h).2 ((D.ordinal h).symm i)

def issuedPorts (D : RunData F W pc regs words S base fuel axes low)
    (h : D.run.plan.History) (i : Fin (D.roots h)) :=
  (D.issuedForest h).1.width ((D.ordinal h).symm i)

/-- Unscaled real per-root subtotal underneath the S43 unit multiplication. -/
def rawCharge (D : RunData F W pc regs words S base fuel axes low)
    (h : D.run.plan.History) (i : Fin (D.roots h)) :=
  D.run.chargeAt h D.issuedCharges
    (TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit) ((D.ordinal h).symm i)

theorem work_eq_rawCharge (D : RunData F W pc regs words S base fuel axes low)
    (h : D.run.plan.History) (i : Fin (D.roots h)) (unit : ℕ) :
    D.work h D.issuedCharges unit i=unit*D.rawCharge h i := rfl

/-- The terminal RAM coefficient times the actual root's typed tree resources. -/
def issuedTreeWork (D : RunData F W pc regs words S base fuel axes low)
    (h : D.run.plan.History) (degree stageRate rootRate : ℕ) (i : Fin (D.roots h)) :=
  let stages := (D.block.repeat D.passes).length
  let depth := 4+stages
  let setup := setupPrice stages stageRate
  let maps := mapPrice degree rootRate
  (10025+1016*depth+setup+maps)*(D.issuedTree h i).resources

/-- Uniform per-run price used in the root's emitted S43 work column. -/
def issuedUnit (D : RunData F W pc regs words S base fuel axes low) (w degree stageRate rootRate : ℕ) :=
  let stages:=(D.block.repeat D.passes).length
  FactorWork.archiveTariff w (4+stages) (setupPrice stages stageRate) (mapPrice degree rootRate)
    stages D.block.localCoefficient

/-- Both estimates apply to the exact root ordinal used by the native resource table. -/
theorem eventual_ranked_factor_bounds (B : Block F) {u s : ℕ→ℕ} (scale : Scale u s)
    (degree stageRate rootRate : ℕ) :
    ∃ coefficient : ℕ, ∀ᶠ w : ℕ in atTop, ∀ {pc regs words S base fuel axes low : ℕ}
      (D : RunData F (64*w) pc regs words S base fuel axes low),
      D.block=B → D.passes=s w → axes+1=u w+1-w/2 → low=w/2 →
      pc≤64*w → regs≤64*w → words≤64*w →
      ∀ h : D.run.plan.History,
        let work:=D.work h D.issuedCharges (D.issuedUnit w degree stageRate rootRate)
        (∑ i, work i) ≤ 2^(u w)*coefficient*(w+1)^51 ∧
          ∀ i, D.issuedTreeWork h degree stageRate rootRate i≤work i ∧ work i≤2^(3*w/5) := by
  obtain ⟨c,estimate⟩:=Physical.native_scheduled_work_bounds B scale degree stageRate rootRate
  refine ⟨c,?_⟩
  have lower := (tendsto_order.mp scale.cap).1 (1/2) (by norm_num)
  have upper := (tendsto_order.mp scale.cap).2 2 (by norm_num)
  have passes := (tendsto_order.mp scale.blocks).2 1 (by norm_num)
  filter_upwards [estimate,lower,upper,passes,eventually_ge_atTop (Fintype.card F+1)]
    with w bound under above blocks big
  have pos : (0:ℝ)<w := by exact_mod_cast (show 0<w by omega)
  have lowerNat : w≤2*u w := by
    exact_mod_cast (show (w:ℝ)≤2*(u w:ℝ) by have h:=(lt_div_iff₀ pos).mp under;linarith)
  have upperNat : u w≤2*w := by exact_mod_cast ((div_lt_iff₀ pos).mp above).le
  have blocksNat : s w≤w := by
    have h:=(div_lt_iff₀ pos).mp blocks
    exact_mod_cast (show (s w:ℝ)≤w by linarith)
  intro pc regs words S base fuel axes low D hb hn ha hl hpc hregs hwords
  rcases D with ⟨M,t,hF,st,b,hk,n,nfits⟩
  change b=B at hb
  subst b
  change n=s w at hn
  subst n
  let D : RunData F (64*w) pc regs words S base fuel axes low:=⟨M,t,hF,st,B,hk,s w,nfits⟩
  let rem:=axes+1-(B.repeat (s w)).charge
  have e : axes+1=(B.repeat (s w)).charge+rem := by
    dsimp [rem]
    rw [B.charge_repeat]
    omega
  intro h
  let price:=D.issuedUnit w degree stageRate rootRate
  let f : (D.run.plan.finish h).Site→ℕ := Physical.publishedWork D.run h D.issuedCharges
    (TraceReceiverSeedWords.start M t hF st B hk) price
  have caps:=bound M t hF st hk rem e (by omega) (by omega) hpc hregs hwords (by omega)
    (by omega) (by omega) blocksNat h
  exact ⟨(le_of_eq ((D.ordinal h).symm.sum_comp f)).trans caps.1,
    fun i=>caps.2 ((D.ordinal h).symm i)⟩

/-- Both estimates apply to the exact root ordinal used by the native resource table. -/
theorem eventual_ranked_work_of_bounds (B : Block F) {u s : ℕ→ℕ} (scale : Scale u s)
    (degree stageRate rootRate : ℕ) :
    ∃ coefficient : ℕ, ∀ᶠ w : ℕ in atTop, ∀ {pc regs words S base fuel axes low : ℕ}
      (D : RunData F (64*w) pc regs words S base fuel axes low),
      D.block=B → D.passes=s w → axes+1=u w+1-w/2 → low=w/2 →
      pc≤64*w → regs≤64*w → words≤64*w →
      ∀ h : D.run.plan.History,
        let work:=D.work h D.issuedCharges (D.issuedUnit w degree stageRate rootRate)
        (∑ i, work i) ≤ 2^(u w)*coefficient*(w+1)^51 ∧ ∀ i, work i≤2^(3*w/5) := by
  obtain ⟨c,estimate⟩:=eventual_ranked_factor_bounds B scale degree stageRate rootRate
  refine ⟨c,?_⟩
  filter_upwards [estimate] with w bound
  intro pc regs words S base fuel axes low D block passes axesEq lowEq pcFit regsFit wordsFit h
  have paid:=bound D block passes axesEq lowEq pcFit regsFit wordsFit h
  exact ⟨paid.1,fun i=>(paid.2 i).2⟩

/-- Summation over the actual chronological factor list, including repeated occurrences. -/
theorem selected_tree_work_le (D : RunData F W pc regs words S base fuel axes low)
    (h : D.run.plan.History) (w degree stageRate rootRate : ℕ)
    (paid : ∀ i,D.issuedTreeWork h degree stageRate rootRate i ≤
      D.work h D.issuedCharges (D.issuedUnit w degree stageRate rootRate) i)
    (selected : List (Fin (D.roots h))) :
    (selected.map (D.issuedTreeWork h degree stageRate rootRate)).sum ≤
      (selected.map (D.work h D.issuedCharges (D.issuedUnit w degree stageRate rootRate))).sum := by
  induction selected with
  | nil => exact le_rfl
  | cons i rest ih => exact Nat.add_le_add (paid i) ih

/-- Fixed native machine dimensions satisfy the lane-width bounds on the same cofinal chart. -/
theorem eventual_ranked_work (B : Block F) {u s : ℕ→ℕ} (scale : Scale u s)
    (pc regs words degree stageRate rootRate : ℕ) :
    ∃ coefficient : ℕ, ∀ᶠ w : ℕ in atTop, ∀ {S base fuel axes low : ℕ}
      (D : RunData F (64*w) pc regs words S base fuel axes low),
      D.block=B → D.passes=s w → axes+1=u w+1-w/2 → low=w/2 →
      ∀ h : D.run.plan.History,
        let work:=D.work h D.issuedCharges (D.issuedUnit w degree stageRate rootRate)
        (∑ i, work i) ≤ 2^(u w)*coefficient*(w+1)^51 ∧ ∀ i, work i≤2^(3*w/5) := by
  obtain ⟨c,cap⟩:=eventual_ranked_work_of_bounds B scale degree stageRate rootRate
  refine ⟨c,?_⟩
  filter_upwards [cap,eventually_ge_atTop (pc+regs+words)] with w paid age
  exact fun D hB hn ha hl => paid D hB hn ha hl (by omega) (by omega) (by omega)

end
end Hierarchy.GridRegisteredSetting.RunData

end OAI
