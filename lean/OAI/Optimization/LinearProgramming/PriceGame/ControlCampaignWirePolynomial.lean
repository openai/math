import OAI.Optimization.LinearProgramming.OracleSpec.SessionBound
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignWireBounds
import OAI.Optimization.LinearProgramming.PriceGame.CampaignRounds
import OAI.Optimization.LinearProgramming.PriceGame.ControlWireFormula

/-! A single input polynomial bounds the size and number of all physical oracle exchanges. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open Learning States.Mass OracleSpec

noncomputable def pricePolynomial : Polynomial ℕ :=
  Formula.price 300 Pool.catalogueExponent Bits.commonDenominator.log2

noncomputable def queryPolynomial : Polynomial ℕ := Formula.query 300 605

/-- Covers the echoed input, the retained replies, and the entire next price packet. -/
noncomputable def dialoguePolynomial : Polynomial ℕ := Formula.dialogue queryPolynomial pricePolynomial

private theorem priceBits_at (N R T time : ℕ) (hT : T ≤ (N+R.size+1)^time) :
    campaignPriceBits N R T ≤
      (Formula.price time Pool.catalogueExponent Bits.commonDenominator.log2).eval (N+R.size+1) := by
  let x := N+R.size+1
  let count := (x*(x^time+1))^Pool.catalogueExponent
  let W := x+count+Bits.commonDenominator.log2
  have hm : expertCount N R T ≤ count := Formula.roster_growth Pool.catalogueExponent x T (x^time) hT
  have hN : N ≤ x := by unfold x; omega
  have hR : R.size ≤ x := by unfold x; omega
  obtain ⟨hn,he,hr,hd⟩ := Formula.input_bounds (d := Bits.commonDenominator.log2) hN hR hm
  have cap := TrialExecution.trialPriceBits_polynomial N (expertCount N R T) R Bits.commonDenominator W
    hn he hr hd
  exact cap.trans_eq (Formula.price_eval time Pool.catalogueExponent Bits.commonDenominator.log2 x).symm

theorem campaignPriceBits_polynomial (N R T : ℕ) (hT : T ≤ (N+R.size+1)^300) :
    campaignPriceBits N R T ≤ pricePolynomial.eval (N+R.size+1) := priceBits_at N R T 300 hT

private theorem queryBound_at (N R T time branches : ℕ) (hT : T ≤ (N+R.size+1)^time)
    (hq : TrialExecution.queryBound N Moment.probes (depth N) 0 ≤ (2*(N+1))^branches) :
    T * TrialExecution.queryBound N Moment.probes (depth N) 0 ≤
      (Formula.query time branches).eval (N+R.size+1) := by
  let x := N+R.size+1
  have hb : 2*(N+1) ≤ 2*(x+1) := by unfold x; omega
  have h := Formula.query_growth branches hT hq hb
  exact h.trans_eq (Formula.query_eval time branches x).symm

theorem campaignQueryBound_polynomial (N R T : ℕ) (hT : T ≤ (N+R.size+1)^300) :
    T * TrialExecution.queryBound N Moment.probes (depth N) 0 ≤ queryPolynomial.eval (N+R.size+1) :=
  queryBound_at N R T 300 605 hT (TrialExecution.queryBound_polynomial N)

theorem padded_header_budget (i : PublicInput) :
    (eiPad i).length ≤ 6*(i.goods+i.range.size+1)+4 := by
  rw [eiPad_length,encodeInput_length]
  have hg : i.goods.size ≤ i.goods := Nat.size_le.mpr i.goods.lt_two_pow_self
  have ha : i.anchor.val.size ≤ i.anchor.val := Nat.size_le.mpr i.anchor.val.lt_two_pow_self
  have hv := i.anchor.isLt
  omega

/-- Both the physical word budget and the complete number of exchanges are bounded
by fixed polynomials, for every answer strategy and every prefix on the padded ABI. -/
theorem campaign_session_polynomial (trials : ℕ → ℕ → ℕ) (i : PublicInput)
    (hT : trials i.goods i.range ≤ (i.goods+i.range.size+1)^300)
    (reply : Transcript → Word → Bool) :
    let x := i.goods+i.range.size+1
    ∃ n ≤ queryPolynomial.eval x+1,
      Dialogue.Session eiPad ecPad (dispatch (campaignSolver trials)) reply
        (dialoguePolynomial.eval x) (.inl i) []
        (wirePlay reply (campaignSolver trials i) []).1 (wirePlay reply (campaignSolver trials i) []).2 n := by
  let x := i.goods+i.range.size+1
  let T := trials i.goods i.range
  have hh := campaignQueryBound_polynomial i.goods i.range T hT
  have hp := campaignPriceBits_polynomial i.goods i.range T hT
  have gx : i.goods ≤ x := by unfold x; omega
  have bound := Formula.packet_total hh (padded_header_budget i) hp gx
  obtain ⟨n,hn,hr⟩ := campaign_session trials i reply (campaignPriceBits i.goods i.range T)
    (campaignSolver_all_prices trials i)
  exact ⟨n,hn.trans (Nat.add_le_add_right hh 1),
    hr.raiseLimit (bound.trans_eq (Formula.dialogue_eval queryPolynomial pricePolynomial x).symm)⟩

private theorem input_cap (N R T d : ℕ) (h : T = Campaign.inputSize N R ^ d) : T ≤ (N+R.size+1)^d := by
  simpa only [Campaign.inputSize] using h.le

set_option exponentiation.threshold 300 in
/-- The actual fixed majority campaign used to recover the hidden sign. -/
theorem reference_session_polynomial (i : PublicInput) (reply : Transcript → Word → Bool) :
    let x := Campaign.inputSize i.goods i.range
    ∃ n ≤ queryPolynomial.eval x+1,
      Dialogue.Session eiPad ecPad (dispatch (campaignSolver Campaign.rounds)) reply
        (dialoguePolynomial.eval x) (.inl i) []
        (wirePlay reply (campaignSolver Campaign.rounds i) []).1
        (wirePlay reply (campaignSolver Campaign.rounds i) []).2 n := by
  have cap := input_cap i.goods i.range (Campaign.rounds i.goods i.range) 300 (Campaign.rounds_eq i.goods i.range)
  simpa only [Campaign.inputSize] using campaign_session_polynomial Campaign.rounds i cap reply

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
