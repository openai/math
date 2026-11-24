import OAI.Computability.VPVNP.LiveLocalGroupCount
import OAI.Computability.VPVNP.LiveProgramPaperParameters
import OAI.Computability.VPVNP.PaperPairParameters
import OAI.Computability.VPVNP.LiveHeaderResources

/-!
# Numeric bounds for the native local group count

Section 9 chooses the cut, evaluator-space and advice powers before the
processor exponent. The same choice made by `paper_parameters` supplies all
word, header and cost bounds needed for `LocalCount.group`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.LocalCount
open Filter LiveHeaderSchedule LiveEvaluatorEncoding PairStages CursorBounds

private theorem header_le_shadow (c : Constants) (g : Geometry) :
    LiveHeaderSchedule.limit (c.lengths.eval g) (2^g.d+1) ≤ (Layout.shadow c).eval g := by
  change (Layout.descriptor c).eval g ≤ _
  simp only [Layout.shadow,Layout.orderMap,Layout.packedPrefix,Layout.adviceFrames,Layout.transitionScratch,
    Layout.newState,Layout.oldState,Layout.counter,eval_add]
  omega

/-- Direct adapter for any choice of the public powers and processor exponent
satisfying the size bounds of `paper_parameters`. -/
theorem conditions_of_majorant (G : Group) (word : 5 ≤ G.g.w) (bucket : 11 ≤ G.g.H) (clock : 154 ≤ G.clock)
    (fit : 1 + G.constants.labels.eval G.g * G.constants.Z.eval G.g ≤ G.g.n^G.constants.deltaPower)
    (layout : LiveEvaluatorTail.Layout G.evaluator.extra (G.g.n^G.constants.radiusPower) G.g.w (G.g.n^G.constants.deltaPower))
    (width : G.g.w ≤ G.g.n) (major : OutsideBudget.majorant G.constants G.g.n < 2^G.g.d)
    (shadow : (Layout.shadow G.constants).eval G.g < 2^G.g.w) :
    Conditions G (2^G.g.d) G.g.H := by
  let s := profile G
  have he : 1+s.e ≤ s.delta := by simpa only [s,profile,Header.sizes,Lengths.eval,Constants.lengths,
    PublicExpr.eval_natPow,eval_mul,PublicExpr.eval] using fit
  have hf : 1+s.config ≤ s.delta := by
    simpa only [s,profile,Header.sizes,Lengths.eval,Constants.lengths,Constants.configWords,Constants.radius,
      PublicExpr.eval_natPow,eval_mul,eval_add,eval_numeral,PublicExpr.eval,fieldWords] using layout.cutWidth
  have hbound := OutsideBudget.actual_le G.constants G.g 0 false false true width (Nat.zero_le _)
  have hcost : costBound s+3 ≤ 2^G.g.d := by
    have h := hbound.trans_lt major
    change costBound s+8+_+100+_+_+_ < _ at h
    omega
  have hfields := field_le_cost s
  have tagfit : stages.length ≤ 2^G.g.w := by
    exact (by decide : stages.length ≤ 2^5).trans (Nat.pow_le_pow_right (by decide) word)
  refine ⟨by omega,clock,⟨(header_le_shadow G.constants G.g).trans_lt shadow,?_,?_,he,hf⟩,
    ?_,?_,tagfit,?_,bucket⟩
  · change 2^G.g.d ≤ 2^G.g.d+1; omega
  · change (s.h+1)*s.delta ≤ 2^G.g.d; omega
  · change s.h+2 ≤ 2^G.g.d; omega
  · change s.advice ≤ 2^G.g.d; omega
  · exact hcost.trans (Nat.le_mul_of_pos_right _ (by omega))

/-- The fixed instruction clock and live bucket meet the two constant lower
bounds simultaneously at every sufficiently large length. -/
theorem eventually_conditions_adapter {C₂ : ℕ} (u : CursorNetwork.PairExponents C₂) (c : Constants) (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, let g := paperGeometry B (liveCapacity u) n
      ∀ G : Group, G.constants = c → G.g = g → n^10000 ≤ G.clock →
        1 + c.labels.eval g * c.Z.eval g ≤ n^c.deltaPower →
        LiveEvaluatorTail.Layout G.evaluator.extra (n^c.radiusPower) g.w (n^c.deltaPower) →
        g.w ≤ n → OutsideBudget.majorant c n < processorCount B n →
        (Layout.shadow c).eval g < 2^g.w → Conditions G (processorCount B n) (liveCapacity u n) := by
  filter_upwards [eventually_liveCapacity_ge u 11,eventually_ge_atTop 154] with n bucket hn
  dsimp only
  intro G constants geometry hclock fit layout width major shadow
  have w : 5 ≤ (paperGeometry B (liveCapacity u) n).w :=
    (by decide : 5 ≤ 10^4).trans (Nat.pow_le_pow_left (Nat.le_add_left 10 (addressBits B n)) 4)
  have hp : n ≤ n^10000 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < n) (by decide : 1 ≤ 10000)
  have cfit := hn.trans (hp.trans hclock)
  have gR : 2^G.g.d = processorCount B n := by rw [geometry]; rfl
  have gH : G.g.H = liveCapacity u n := by rw [geometry]; rfl
  rw [← gR,← gH]
  apply conditions_of_majorant G (geometry ▸ w) (gH ▸ bucket) cfit
  · rw [constants,geometry]; exact fit
  · rw [constants,geometry]; exact layout
  · rw [geometry]; exact width
  · rw [constants,geometry]; exact major
  · rw [constants,geometry]; exact shadow

/-- Select all length powers before the processor exponent and obtain the
actual local-count conditions at all sufficiently large lengths. -/
theorem eventually_paper_conditions {C₂ : ℕ} (u : CursorNetwork.PairExponents C₂) (C motif : ℕ)
    {P rawLength : ℕ → ℕ} (radius : ℕ → ℕ → ℕ) (hP : PolynomiallyBounded P)
    (hraw : PolynomiallyBounded rawLength) (hr : ∀ a, PolynomiallyBounded (fun n => radius n (2*n^a)))
    (E : UniversalMachine.Program) :
    ∃ a dA d₁ d₂ r B₀ : ℕ, 2 ≤ a ∧ 1 ≤ B₀ ∧ ∀ k B : ℕ, B₀ ≤ B → ∀ᶠ n : ℕ in atTop,
      let c : Constants := ⟨C,a,d₁,d₂,r,dA,motif⟩
      let g := paperGeometry B (liveCapacity u) n
      2^(P n)*(2*n^a+1)^k ≤ 2^(n^a-1) ∧ radius n (2*n^a) ≤ n^r ∧ rawLength n ≤ n^dA ∧
      g.w+n^dA+c.labels.eval g*Nat.clog 2 (c.labels.eval g) ≤ n^d₁ ∧
      1+c.labels.eval g*(2*n^a) ≤ n^d₂ ∧ LiveEvaluatorTail.Layout E.extra (n^r) g.w (n^d₂) ∧
      (∀ G : Group, G.constants = c → G.g = g → G.evaluator = E → n^10000 ≤ G.clock →
        Conditions G (processorCount B n) (liveCapacity u n)) := by
  obtain ⟨a,dA,d₁,d₂,r,B₀,ha,hB₀,all⟩ := paper_parameters C motif radius hP hraw (liveCapacity_polynomial u) hr E
  refine ⟨a,dA,d₁,d₂,r,B₀,ha,hB₀,fun k B hB => ?_⟩
  let c : Constants := ⟨C,a,d₁,d₂,r,dA,motif⟩
  filter_upwards [all k B hB,eventually_conditions_adapter u c B] with n pp adapter
  obtain ⟨time,space,raw,advice,field,layout,major,width,_,shadow,_⟩ := pp
  refine ⟨time,space,raw,advice,field,layout,fun G constants geometry evaluator clock => ?_⟩
  apply adapter G constants geometry clock
  · simpa only [c,Constants.Z,Constants.height,eval_mul,eval_numeral,PublicExpr.eval_natPow,paperGeometry,PublicExpr.eval] using field
  · rw [evaluator]; exact layout
  · exact width
  · exact major
  · exact shadow

end LiveProgram.LocalCount

end VPVNP
end Computability
end OAI
