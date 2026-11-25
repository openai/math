import OAI.Hierarchy.DescentTerminalRangeCalibration
import OAI.Hierarchy.DescentTerminalSharedTables

namespace OAI
/-! # The three literal lookup bounds for the normalized terminal epoch -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentResetGates DescentPrimitivePalette Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- Every literal lookup, including the alphabet and the full printed header table, fits the paid page. -/
theorem terminal_format_calibration_full (op : RotorSpec) (drift t f g reset τ B : ℕ)
    (branch : G.b ≤ 2^(capRate G t g)) (positive : 0 < B)
    (cohortBudget : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19)) ≤ B)
    (routingBudget : 2*((τ+groupRate G t f g reset+4)+
      (localSocketRate G t g+Nat.clog 2 G.b*(t+1))+2) ≤ B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        let W:=NativeBranch.binLimit (k:=k) S
        let q:=2^Nat.clog 2 (NativeBranch.localLimit G S)*(G.b^(t*J)*G.b)
        let piece:=h/(16*(q*W))
        let p:=W*piece
        let K:=NativeBranch.privateSlotCapacity G S drift
        let tags:=DescentBundleTagKeys.capacity (colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op)
          (max 8 (2^S.capGain)) K p drift
        let V:=S.groupCount S.length*2^k
        let nodes:=S.epochPower^S.localTokenExponent
        DescentTerminalDenseWindow.formatBits q p+2*(q*p) ≤ h/2 ∧
        DescentTerminalBinFormat.controlBits W q+DescentTerminalBinReaddress.sliceWidth W q piece ≤ h/2 ∧
        DescentTerminalScalarHeader.range q tags K nodes K p V+1 ≤ 2^(h/2) ∧
        DescentTerminalSiteShelves.alphabet V W (max 1 (V*actualSpan G S op q p drift)) ≤ 2^(h/2) ∧
        (DescentTerminalPrintedFields.capacity q tags K nodes K p V).total ≤ 2^(h/2) ∧
        DescentTerminalChronologicalBooks.Keys q tags K nodes K p V p ≤ 2^(h/2) := by
  filter_upwards [terminal_cohort_span G op drift t f g reset τ B branch positive cohortBudget,
    native_format_widths G t f g reset τ B positive routingBudget,
    eventually_ge_atTop 10] with h cohorts widths ten
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let W:=NativeBranch.binLimit (k:=k) S
  let q:=2^Nat.clog 2 (NativeBranch.localLimit G S)*(G.b^(t*J)*G.b)
  let piece:=h/(16*(q*W))
  let p:=W*piece
  let K:=NativeBranch.privateSlotCapacity G S drift
  let tags:=DescentBundleTagKeys.capacity (colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op)
    (max 8 (2^S.capGain)) K p drift
  let nodes:=S.epochPower^S.localTokenExponent
  let V:=S.groupCount S.length*2^k
  obtain ⟨wp, packed, pbound, qbound, dense, route⟩:=widths M
  have page : 32*(V*actualSpan G S op q p drift) ≤ h := cohorts M p q pbound qbound
  have tagsPositive : 0<tags := terminal_tag_capacity_pos G S op p drift
  have field : DescentTerminalVertexFields.span q tags K nodes K p ≤ actualSpan G S op q p drift :=
    Nat.le_succ _
  have lut:=DescentTerminalVertexFields.shared_tables q tags K nodes K p V W
    (V*actualSpan G S op q p drift) h tagsPositive (Nat.mul_le_mul_left _ field) page wp packed ten
  have vpos : 0 < V := by
    dsimp [V,S,AtomSchedule.groupCount,stageNumbers]
    positivity
  have count : 1 ≤ V*actualSpan G S op q p drift :=
    Nat.mul_pos vpos (Nat.succ_pos _)
  exact ⟨dense,route,lut.2.2.1,by rw [max_eq_right count]; exact lut.1,lut.2.1,lut.2.2.2⟩

end
end Hierarchy.DescentSixParty

end OAI
