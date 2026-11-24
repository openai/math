import OAI.Computability.VPVNP.FixedProgramTailOrder
import OAI.Computability.VPVNP.LiveLocalCountConditions

/-!
# Choosing the finite program's powers from a reader bound

Choose the evaluator clock, advice, radius and cut powers before choosing
the address multiplier. Enlarging that multiplier for the virtual pair
layout preserves these bounds. The same rational bucket ratio is used by
the compression simulation and the live site processor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open Compression BurstRAM LiveProgram CursorNetwork CursorBounds

variable {K : Type*} [Field K] {S : BlockSchedule K} (T : S.Templates)

/-- Assemble the fixed program from the selected powers, scalar evaluator, pair table and bucket exponent. -/
def ofPaperConstants (c : Constants) (E : UniversalMachine.Program) (O : PairTable)
    (factor : ℕ) (hfactor : 1 ≤ factor) {z : ℝ} (ratio : Ratio z) : FixedProgramDiagonal.Program :=
  ⟨c,E,O,factor,hfactor,ratio.num,ratio.den,ratio.less,0⟩

/-- Clock, advice, counter and layout bounds used to realize the fixed program at a given length. -/
structure Numerics (D : FixedProgramDiagonal.Program) (C : ℕ) (env : ℕ → ℕ) (ports n : ℕ) : Prop where
  time : 2^(6*env n+23)*(D.counterWidth n+1)^4 ≤ 2^(D.chainHeight n)
  space : 2240*(ports+1)*(env n+D.counterWidth n+1)^4 ≤ n^D.constants.radiusPower
  raw : env n ≤ n^D.constants.prefixPower
  advice : (D.geometry n).w + n^D.constants.prefixPower + T.denseCount n C*Nat.clog 2 (T.compressorLabelCount C n)
    ≤ n^D.constants.advicePower
  counters : 1 + T.denseCount n C*D.counterWidth n ≤ n^D.constants.deltaPower
  layout : LiveEvaluatorTail.Layout D.evaluator.extra (n^D.constants.radiusPower) (D.geometry n).w
    (n^D.constants.deltaPower)
  hw : 4 ≤ (D.geometry n).w
  hc : 2^(D.geometry n).d * (D.geometry n).H < 2^(D.geometry n).w
  hR : 4*n ≤ 2^(D.geometry n).d
  hZ : D.chainHeight n + 2*(D.geometry n).d ≤ D.counterWidth n
  group : ∀ G : PairStages.Group, G.constants = D.constants → G.g = D.geometry n → G.evaluator = D.evaluator →
    n^10000 ≤ G.clock → LocalCount.Conditions G (2^(D.geometry n).d) (D.geometry n).H

set_option maxHeartbeats 1200000 in
theorem select (C : ℕ) (u : PairExponents T.growthConstant) (E : UniversalMachine.Program)
    (env : ℕ → ℕ) (henv : PolynomiallyBounded env) (ports : ℕ) :
    ∃ c : Constants, c.circuitExponent = C ∧ c.motifLabels = Fintype.card T.Entry ∧
      2 ≤ c.chainPower ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ b ≥ N, ∀ O : PairTable,
        ∀ᶠ n : ℕ in Filter.atTop, ∃ hb : 1 ≤ b,
          Numerics T (ofPaperConstants c E O b hb (liveRatio u)) C env ports n := by
  let P := fun n => 6*env n+23
  let radius := fun n Z => 2240*(ports+1)*(env n+Z+1)^4
  have hP : PolynomiallyBounded P := ((PolynomiallyBounded.const 6).mul henv).add (.const 23)
  have hr (a : ℕ) : PolynomiallyBounded (fun n => radius n (2*n^a)) :=
    (PolynomiallyBounded.const (2240*(ports+1))).mul
      (((henv.add ((PolynomiallyBounded.const 2).mul (PolynomiallyBounded.id.pow a))).add (.const 1)).pow 4)
  obtain ⟨a,da,d₁,d₂,r,b₀,ha,hb₀,H⟩ := LocalCount.eventually_paper_conditions u C (Fintype.card T.Entry)
    radius hP henv hr E
  let c : Constants := ⟨C,a,d₁,d₂,r,da,Fintype.card T.Entry⟩
  let N := max b₀ (max S.laneBits 5)
  refine ⟨c,rfl,rfl,ha,N,hb₀.trans (le_max_left ..),?_⟩
  intro b hb O
  have hb' : 1 ≤ b := hb₀.trans ((le_max_left ..).trans hb)
  let D := ofPaperConstants c E O b hb' (liveRatio u)
  filter_upwards [H 4 b ((le_max_left ..).trans hb),
    eventually_numeric T u b a ((le_max_right ..).trans hb) (by omega)] with n H numeric
  obtain ⟨time,space,raw,adv,cut,layout,groups⟩ := H
  obtain ⟨hw,hc,hR,hZ,_,_⟩ := numeric
  have labels : c.labels.eval (paperGeometry b (liveCapacity u) n) = T.denseCount n C :=
    physicalLabelCount_eq D T rfl rfl
  have card : T.denseCount n C = T.compressorLabelCount C n := JointLabelSystem.FixedRows.labelOrder_length T.Entry n C
  rw [labels] at adv
  have adv' : (D.geometry n).w + n^da + T.denseCount n C * Nat.clog 2 (T.compressorLabelCount C n) ≤ n^d₁ := by
    rw [← card]
    exact adv
  rw [labels] at cut
  exact ⟨hb',time,space,raw,adv',cut,layout,hw,hc,hR,hZ,groups⟩

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
