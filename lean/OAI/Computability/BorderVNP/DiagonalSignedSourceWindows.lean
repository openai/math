import OAI.Computability.BorderVNP.DiagonalSelectedPhaseWindows
import OAI.Computability.BorderVNP.DiagonalJointLength
import OAI.Computability.BorderVNP.RoutingISAScheduleClockSourceWindows

/-! # The measured signed source on the selected physical team and grid parameters -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing Cover Epoch Packing PackedHistoryCircuit.Normalized TeamScales
open RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock BorderVNP.Cube
open scoped Classical

variable {F : Type} [Field F] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m}
    {S : SiteSchedule G} {a extra E d Q A B j : ℕ} {s : EpochScales S a extra}

/-- The genuine source emitter includes the two sorted packet sections after the
routing and control columns. Bounding its interpreter therefore pays their full
word widths, even when most entries are padding. The finish scan may process a
different number of report words on this history. -/
theorem signed_emitted_and_report_words {p d gates pins cables route cells original controls field w reportWords : ℕ}
    {budget : ℝ} (width : 1≤w) (bits : 1≤field)
    (finish : (w+1)*reportWords≤⌈budget⌉₊) :
    let output := cables*3+(route+((cells+(original+cells))+(controls+CellPacketGeometry.Total p d)))
    (GeometryAdviceRate.ticks gates pins output field w : ℝ) ≤ budget →
    (w+1)*max (2^p+2^d) reportWords ≤ ⌈budget⌉₊ ∧ output ≤ ⌈budget⌉₊ := by
  intro output geometry
  have cost : GeometryAdviceRate.ticks gates pins output field w ≤ ⌈budget⌉₊ := by
    exact_mod_cast geometry.trans (Nat.le_ceil budget)
  have columns : CellPacketGeometry.Total p d ≤ output :=
    (Nat.le_add_left _ _).trans ((Nat.le_add_left _ _).trans ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _)))
  obtain ⟨words,out⟩ := geometrySubarrays_le (k:=gates) (u:=pins) width bits columns
  refine ⟨?_,out.trans cost⟩
  rcases le_total (2^p+2^d) reportWords with h | h
  · simpa only [max_eq_right h] using finish
  · simpa only [max_eq_left h] using words.trans cost

/-- At the chosen grid depth, actual team count, physical word width and stretched
batch, the measured source charges fit the very windows used by the positive
continuation. The public report field can have the sparse scanner's actual size.
The threshold precedes the substituted pin, every public receipt and all reader data. -/
theorem JointSchedule.eventually_signed_source_windows (b : JointSchedule s (E+1) d Q A B j)
    (degree bits rowFactor fixed emitted H : ℕ) (exponent : E+2 ≤ degree) :
    ∀ᶠ n : ℕ in atTop,
    let r := stretch b.ρ n
    let R := b.physical.teamsPred n+1
    let w := b.physical.word n
    let ξ := (s.τ:ℝ)/5
    let V := CoverScale.sites (Cube D) (CoverScale.initialDepth (Cube D) r n)
    let M := max ((epochGrowth S extra)^epochs s.τ n) R
    let Z := Routing.labelCount a s.α n
    let X := exterior ξ r n
    let P := RoutingISA.Evaluator.publicWork a s.α r n R
    let windows := s.signedWindows degree (512*(a+bits+1)) fixed emitted H n r
    ∀ (words k pins outputs field entries cells bundles core powers rectangle reader : ℕ)
        (l : LabelIndex.Layout) (mem : ℕ → ℕ) (weights : GroupWeights.Layout) (teams : TeamNative.Layout)
        (header : HeaderDecode.Layout),
      let geo := GeometryAdviceRate.ticks k pins outputs field w
      let costs := phaseCharges core geo fixed R V entries cells bundles
        (descriptorTicks l mem (Z-1) a weights teams) (declarationTicks header (a-1) bits) l.cableCount (Z^2+X+1)
        emitted H w words powers X rectangle reader
      1+l.cells+l.cableCount+l.deliveryCount ≤ rowFactor*(V+1)*(M+1) → l.labels=Z → 1≤Z →
      weights.cells=l.cells → teams.groups=weights.groups → teams.r+1≤weights.groups → weights.groups≤l.labels →
      header.d=weights.groups → header.a=a → header.cw≤w → header.rw≤w →
      (w+1)*words≤⌈P⌉₊ → outputs≤⌈P⌉₊ → (geo:ℝ)≤P → entries≤R*V → cells≤outputs → bundles≤outputs →
      powers≤r*logWidth r n → rectangle+reader≤r →
      core≤2048*(X+(R+1)^3+(l.deliveryCount+weights.groups.choose 2)+r+1) →
      costs.core≤windows.core ∧ costs.before≤windows.before ∧ costs.argumentsCalls≤windows.argumentsCalls ∧
        costs.finish≤windows.finish ∧ costs.reader≤windows.reader := by
  have hα : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have hτ : 0 ≤ (s.τ:ℝ) := by exact_mod_cast s.tau_pos.le
  have phases := eventually_measuredSourceWindows hα hτ (by linarith [s.tau_small,s.alpha_small] : (s.τ:ℝ)/5 ≤ 1)
    a degree bits rowFactor 1 fixed emitted H s.alpha_cube s.alpha_small.le (by omega) (epochGrowth S extra)
    (epochCopies S) (epochGrowth_bounds S extra).1 (epochCopies_pos S) s.growth.le s.copy_rate
  filter_upwards [phases,b.eventually_lengths 0,eventually_ge_atTop 1] with n all lengths pos
  intro r R w ξ V M Z X P windows words k pins outputs field entries cells bundles core powers rectangle reader
    l mem weights teams header geo costs rows labels alphabet cellsEq groups team groupCount dEq axes cw rw wordCharge
    out paid privateRows cellFit bundlesFit powerFit readerFit coreFit
  have same := (b.sizes pos).1
  have rr : 1 ≤ r := stretch_one ..
  have rM : R ≤ max ((epochGrowth S extra)^epochs s.τ n) (TeamScales.teams s.α s.τ (epochCopies S) n) :=
    same.le.trans (le_max_right ..)
  have cap : (V:ℝ) ≤ (1:ℕ)*r*(n:ℝ)^(9/10:ℝ) := by
    simpa only [Nat.cast_one,one_mul] using lengths.cover.2.2.2.1
  have wordFit : w ≤ logWidth r n^degree := Nat.pow_le_pow_right (GeometryAdviceRate.indexWidths rr pos).1 exponent
  have actual := all r R V (Z-1) w words k pins outputs field entries cells bundles core powers rectangle reader
    l mem weights teams header rr (Nat.succ_pos _) rM cap (by simpa only [←same] using rows) labels (by omega)
    cellsEq groups team groupCount dEq axes cw rw wordFit wordCharge out paid privateRows cellFit bundlesFit powerFit readerFit coreFit
  change _ ≤ (uniformWindows r R X _ _ _ fixed emitted H).core ∧ _ at actual
  simpa only [costs,windows,EpochScales.signedWindows,←same] using actual

end Diagonal

end BorderVNP
end Computability
end OAI
