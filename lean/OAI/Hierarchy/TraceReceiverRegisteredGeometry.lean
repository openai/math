import OAI.ThreeFlat.Diagonal.PhysicalEndLevel
import OAI.ThreeFlat.Diagonal.PhysicalTerminalDegree
import OAI.ThreeFlat.Diagonal.PhysicalTerminalPorts
import OAI.Hierarchy.TraceReceiverTerminalMap
import OAI.Hierarchy.HistorySelectedPairWidths
import OAI.Hierarchy.GridRegisteredWork
import OAI.Hierarchy.TraceFactorCofinalResources
import OAI.Hierarchy.TraceFactorRegisteredPins
import OAI.ThreeFlat.Diagonal.PhysicalTreeFee

namespace OAI
/-! # The terminal compiler and visit bill at the rank of the actual S43 record -/

noncomputable section
namespace Hierarchy.GridRegisteredSetting.RunData
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open TraceDistribution TraceFactorReceiver.Gather RAM Computability.VPVNP.BurstRAM PrivateRAM Filter
open scoped BigOperators Classical

variable {F : Type} [Field F] [Fintype F] {W pc regs words S base fuel axes low : ℕ}

omit [Fintype F] in
private theorem native_shape {Pins : Type} (B : Block F) (n rem : ℕ) {l : ℕ}
    (X : State (2^(B.exponent 0)) l) (e : l=(B.repeat n).charge+rem) (L : X.Words Pins)
    (N : Forest F L.ports.form) (atom : ∀ v, Tree.Within 4 (N v)) :
    let R := Program.recast e X ((B.repeat n).run rem (e ▸ X))
    let C := Physical.registerOnLanes B Pins n rem X e
    ∀ h : R.plan.History, R.endLevel h 0=(B.repeat n).length ∧ ∀ v,
      Tree.Within (4+(B.repeat n).length) ((R.plan.assemble h (R.wordAssembly C.1.steps L) N).2 v) := by
  subst l
  intro R C h
  refine ⟨?_,?_⟩
  · simpa only [Nat.zero_add] using R.endLevel_stageLength h 0 (B.repeat n).length
      ((B.repeat n).stageLength_run rem X)
  · exact Physical.terminal_factor_within (B.repeat n) rem X L h N atom

private theorem geometry (D : RunData F W pc regs words S base fuel axes low) :
    axes+1=(D.block.repeat D.passes).charge+(axes+1-(D.block.repeat D.passes).charge) := by
  rw [D.block.charge_repeat]
  have := D.passesFit
  omega

theorem issued_shape (D : RunData F W pc regs words S base fuel axes low) (h : D.run.plan.History) :
    D.run.endLevel h 0=(D.block.repeat D.passes).length ∧ ∀ i,
      Tree.Within (4+(D.block.repeat D.passes).length) (D.issuedTree h i) := by
  let N := TraceReceiverSeedWords.forest D.machine D.fit D.field D.state D.block D.axesFit
  have q:=native_shape D.block D.passes _ _ (geometry D)
    (TraceReceiverSeedWords.wordsLayout D.machine D.fit D.field D.state D.block D.axesFit) N
    (fun _ => Tree.Within.atom 4 _) h
  exact ⟨q.1,fun i => q.2 ((D.ordinal h).symm i)⟩

theorem issued_ports_pay (D : RunData F W pc regs words S base fuel axes low)
    (h : D.run.plan.History) (i : Fin (D.roots h)) :
    D.issuedPorts h i≤2*D.rawCharge h i :=
  D.run.assembled_port_width h D.issuedRegister.1.steps D.issuedCharges
    (Physical.registered_local_floor D.block _ D.passes _ _ (geometry D))
    (TraceReceiverSeedWords.wordsLayout D.machine D.fit D.field D.state D.block D.axesFit)
    (TraceReceiverSeedWords.forest D.machine D.fit D.field D.state D.block D.axesFit)
    (TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit)
    (fun v => (TraceReceiverSeedWords.seed_budget D.machine D.fit D.field D.state D.block D.axesFit v).2.1)
    ((D.ordinal h).symm i)

theorem eventual_universal_issued_resources (B : Block F) {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {pc regs words S base fuel axes low : ℕ}
      (D : RunData F (64*w) pc regs words S base fuel axes low),
      D.block=B → D.passes=s w → axes+1=u w+1-w/2 → low=w/2 →
      pc≤64*w → regs≤64*w → words≤64*w → ∀ h (i : Fin (D.roots h)),
      (D.issuedTree h i).resources≤Run.treeFee (B.localCoefficient*(64*w+1)^3)
        (B.repeat (s w)).length*D.rawCharge h i := by
  have upper := (tendsto_order.mp scale.cap).2 2 (by norm_num)
  filter_upwards [Physical.native_universal_resources B scale,upper,eventually_ge_atTop (Fintype.card F+1)]
    with w bound cap big
  have pos : 0<(w:ℝ) := by exact_mod_cast (show 0<w by omega)
  have uw : u w≤2*w := by exact_mod_cast ((div_lt_iff₀ pos).mp cap).le
  intro pc regs words S base fuel axes low D same passes axis half hp hr hw
  rcases D with ⟨M,t,hF,st,b,hk,n,nfits⟩
  change b=B at same
  subst b
  change n=s w at passes
  subst n
  let D : RunData F (64*w) pc regs words S base fuel axes low:=⟨M,t,hF,st,B,hk,s w,nfits⟩
  intro h i
  exact bound M t hF st hk _ (geometry D) (by omega) (by omega) hp hr hw (by omega)
    h ((D.ordinal h).symm i)

theorem eventual_issued_resources (B : Block F) {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ age : ℕ, 64*w=16*age^10 → ∀ {pc regs words S base fuel axes low : ℕ}
      (D : RunData F (64*w) pc regs words S base fuel axes low),
      D.block=B → D.passes=s w → axes+1=u w+1-w/2 → low=w/2 →
      pc≤64*w → regs≤64*w → words≤64*w → ∀ h (i : Fin (D.roots h)),
      (D.issuedTree h i).resources≤Run.treeFee (B.localCoefficient*(64*w+1)^3)
        (B.repeat (s w)).length*D.rawCharge h i := by
  filter_upwards [eventual_universal_issued_resources B scale] with w bound
  intro _age _aligned
  exact @bound

omit [Fintype F] in
private theorem mass_on_lanes (B : Block F) (n rem : ℕ) {l : ℕ}
    (X : State (2^(B.exponent 0)) l) (e : l=(B.repeat n).charge+rem) (work pairs : X.Site→ℕ)
    (seed : ∀ x,1+X.incidentWidth x+pairs x≤work x) :
    let R:=Program.recast e X ((B.repeat n).run rem (e ▸ X))
    let C:=Physical.registerOnLanes B (Fin S→Bool) n rem X e
    ∀ h v, 1+R.terminalIncident h v+(∑ a : {x // R.plan.destination h x=v},pairs a.val)≤
      R.chargeAt h C.2 work v := by
  subst l
  intro R C h v
  exact B.terminal_charge_covers n rem X h work pairs seed v

/-- Physical terminal state whose half table and coordinate are used by the root decoder. -/
abbrev terminalWords (D : RunData F W pc regs words S base fuel axes low) (h : D.run.plan.History) :=
  D.run.endWords h D.issuedRegister.1.steps
    (TraceReceiverSeedWords.wordsLayout D.machine D.fit D.field D.state D.block D.axesFit)

abbrev terminalSite (D : RunData F W pc regs words S base fuel axes low) (h : D.run.plan.History)
    (i : Fin (D.roots h)) :=
  cast (congrArg Shape.Site (D.run.terminalLayer_shape h)).symm ((D.ordinal h).symm i)

def terminalPairs (D : RunData F W pc regs words S base fuel axes low) (h : D.run.plan.History)
    (i : Fin (D.roots h)) :=
  ∑ a : {x // D.run.plan.destination h x=(D.ordinal h).symm i},
    TraceReceiverSeedWords.pairs D.machine D.fit D.field D.state a.val

/-- Reading the four-word records of the actual terminal site discharges the degree, paired
external width and complete incidence floor required by the native address-map writer. -/
theorem issued_task_fields (D : RunData F W pc regs words S base fuel axes low) (h : D.run.plan.History)
    (i : Fin (D.roots h)) (task : HistoryTerminalTape.Root) (raw : ℕ→ℕ) (suffix : ℕ)
    (tab : TraceReceiverTerminalMap.HalfRows (D.run.terminalLayer h).state (D.terminalWords h)
      (D.terminalSite h i) task raw suffix) (even : Even S) :
    task.halves=2*(2^D.block.exponent 0) ∧ task.ext=2*D.terminalPairs h i ∧
      1+(∑ j : Fin task.halves,(HistoryTerminalTape.half task raw j.val).width)+D.terminalPairs h i≤
        D.rawCharge h i ∧
      task.ext+(∑ j : Fin task.halves,(HistoryTerminalTape.half task raw j.val).width)=D.issuedPorts h i := by
  let L:=TraceReceiverSeedWords.wordsLayout D.machine D.fit D.field D.state D.block D.axesFit
  let p:=TraceReceiverSeedWords.pairs D.machine D.fit D.field D.state
  let start:=TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit
  let v:=(D.ordinal h).symm i
  let z:=D.terminalSite h i
  let T:=D.terminalWords h
  have ordered:=TraceReceiverSeedWords.words_ordered D.machine D.fit D.field D.state D.block D.axesFit
  have ends:=D.run.endWords_halves h D.issuedRegister.1.steps L ordered
  have inc : (∑ j : Fin task.halves,(HistoryTerminalTape.half task raw j.val).width)=
      D.run.terminalIncident h v := by
    calc
      _ = ∑ j : Fin (T.count z),(HistoryTerminalTape.half task raw j.val).width :=
        ((finCongr tab.halves_eq).symm.sum_comp (fun j=>(HistoryTerminalTape.half task raw j.val).width)).symm
      _ = T.ports.halfBits z := Finset.sum_congr rfl (fun j _ => tab.width j)
      _ = _ := ends.halfBits_eq_incident z
  have pair : task.ext=2*D.terminalPairs h i := by
    rw [tab.ext_eq,D.run.terminal_ext_sum h D.issuedRegister.1.steps L v,terminalPairs,Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => HistorySelectedPairWidths.exact_seed D.machine D.fit D.field D.state even j.val
  have seed := TraceReceiverSeedWords.seed_pairs_budget D.machine D.fit D.field D.state D.block D.axesFit
  have paid:=mass_on_lanes (S:=S) D.block D.passes _ _ (geometry D) start p seed h v
  have number:=D.block.terminalDegree_onLanes _ (geometry D) h
  have width:=D.run.terminal_width_exact h D.issuedRegister.1.steps L ordered
    (TraceReceiverSeedWords.forest D.machine D.fit D.field D.state D.block D.axesFit) v
  refine ⟨tab.halves_eq.trans ((ends.count z).trans (congrArg (2*·) number)),pair,?_,?_⟩
  · rw [inc]
    exact paid
  · rw [inc,tab.ext_eq]
    exact width.symm

/-- The numeric row, hidden and pin columns can be accumulated together. The first two
are projections of the compiled issued tree, and the last is charged by its true pin floor. -/
theorem issued_dimensions_pay (D : RunData F W pc regs words S base fuel axes low)
    (h : D.run.plan.History) (i : Fin (D.roots h)) (w degree stageRate rootRate : ℕ)
    (paid : D.issuedTreeWork h degree stageRate rootRate i≤
      D.work h D.issuedCharges (D.issuedUnit w degree stageRate rootRate) i) :
    let T:=D.issuedTree h i
    T.compile.cells+T.compile.internal+D.issuedPorts h i≤
      D.work h D.issuedCharges (D.issuedUnit w degree stageRate rootRate) i := by
  let T:=D.issuedTree h i
  let stages:=(D.block.repeat D.passes).length
  let setup:=setupPrice stages stageRate
  let maps:=mapPrice degree rootRate
  let c:=10025+1016*(4+stages)+setup+maps
  let unit:=D.issuedUnit w degree stageRate rootRate
  let price:=D.work h D.issuedCharges unit i
  have intrinsic : T.compile.cells+T.compile.internal≤T.resources := by
    rw [Tree.compiled_rows,Tree.compiled_bits]
    change T.rows+T.bits≤T.bits+T.rows+T.nodes+T.footprint.pins
    omega
  have capacity : 2*(T.compile.cells+T.compile.internal)≤price :=
    (Nat.mul_le_mul (by dsimp [c];omega : 2≤c) intrinsic).trans paid
  have kpos : 0<D.block.localCoefficient := by unfold Block.localCoefficient; omega
  have unitRoom : 4≤unit := by
    change 4≤c*((2*stages+1)*(D.block.localCoefficient*(16*w^10+1)^3))
    exact (by dsimp [c];omega : 4≤c).trans (Nat.le_mul_of_pos_right _ (by positivity))
  have pins:=D.issued_ports_pay h i
  have coverage:=Nat.mul_le_mul_right (D.rawCharge h i) unitRoom
  change 4*D.rawCharge h i≤price at coverage
  change T.compile.cells+T.compile.internal+D.issuedPorts h i≤price
  omega

end Hierarchy.GridRegisteredSetting.RunData
end

end OAI
