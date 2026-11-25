import OAI.Hierarchy.DescentNativeFormatWidths
import OAI.Hierarchy.DescentTerminalIssuedScale
import OAI.Hierarchy.DescentTerminalRowStorage
import OAI.Hierarchy.DescentTerminalDenseWindow

namespace OAI
/-! # Calibrated exponents of the dense, route and scalar tables -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentResetGates DescentPrimitivePalette Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- Total width of the reached scalar records, with the original history-independent group count. -/
theorem terminal_cohort_span (op : RotorSpec) (drift t f g reset τ B : ℕ)
    (branch : G.b ≤ 2^(capRate G t g)) (positive : 0<B)
    (bought : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19)) ≤ B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M p q : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
        p ≤ h → q ≤ h → 32*((S.groupCount S.length*S.radix)*actualSpan G S op q p drift) ≤ h := by
  let σ:=6*(terminalDegree G t f g reset+1)+19
  filter_upwards [issued_terminal_spans G op drift t f g reset τ B branch positive,
    eventually_home τ (groupRate G t f g reset) σ B positive bought] with h spans layouts
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M p q pw qw
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
  have sites : S.groupCount S.length*S.radix ≤ 2^(tail τ J)*2^k := by
    simp [S,k,AtomSchedule.groupCount,stageNumbers]
  exact layouts.2 k _ _ sites (groupBits_linear ..) (spans M p q pw qw).1

theorem terminal_tag_capacity_pos (S : AtomSchedule) (op : RotorSpec) (p drift : ℕ) :
    0 < DescentBundleTagKeys.capacity (colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op)
      (max 8 (2^S.capGain)) (NativeBranch.privateSlotCapacity G S drift) p drift := by
  dsimp only [DescentBundleTagKeys.capacity,DescentEpochTagKeys.span,DescentBundleTagKeys.radix,
    DescentPrimitivePalette.colors,DescentPrimitivePalette.censusCount]
  positivity

/-- The three numerical lookups use the same epoch, printed format and socket geometry. -/
theorem terminal_format_calibration (op : RotorSpec) (drift t f g reset τ B : ℕ)
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
        DescentTerminalDenseWindow.formatBits q p+2*(q*p) ≤ h/2 ∧
        DescentTerminalBinFormat.controlBits W q+DescentTerminalBinReaddress.sliceWidth W q piece ≤ h/2 ∧
        DescentTerminalScalarHeader.range q tags K (S.epochPower^S.localTokenExponent) K p
          (S.groupCount S.length*2^k)+1 ≤ 2^(h/2) := by
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
  have scalar := DescentTerminalVertexFields.scalar_range q tags K nodes K p V h tagsPositive
    ((Nat.mul_le_mul_left 32 (Nat.mul_le_mul_left V field)).trans page) ten
  exact ⟨dense,route,scalar⟩

end
end Hierarchy.DescentSixParty

end OAI
