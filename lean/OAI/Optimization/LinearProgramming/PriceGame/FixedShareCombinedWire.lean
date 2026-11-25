import OAI.Optimization.LinearProgramming.PriceGame.FixedShareCursorWire
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialEnvelope

/-! One bound for both kinds of physical campaign state. The inner bound counts
the current program counter and every saved frame, including its prepared market,
historical prices, cached child results, allocations and reply tape. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open States.Mass Learning
noncomputable section

private structure SizeInput where
  goods : ℕ
  range : ℕ
  trials : ℕ
  cap : trials ≤ (goods+range.size+1)^300

private def argument (i : SizeInput) := i.goods+i.range.size+1

private structure Bound (f : SizeInput → ℕ) where
  poly : Polynomial ℕ
  le : ∀ i, f i ≤ poly.eval (argument i)

private def constantBound (n : ℕ) : Bound (fun _ => n) :=
  ⟨Polynomial.C n, fun _ => by rw [Polynomial.eval_C]⟩

private def addBound {f g : SizeInput → ℕ} (a : Bound f) (b : Bound g) :
    Bound (fun i => f i + g i) :=
  ⟨a.poly + b.poly, fun i => by rw [Polynomial.eval_add]; exact Nat.add_le_add (a.le i) (b.le i)⟩

private def mulBound {f g : SizeInput → ℕ} (a : Bound f) (b : Bound g) :
    Bound (fun i => f i * g i) :=
  ⟨a.poly * b.poly, fun i => by rw [Polynomial.eval_mul]; exact Nat.mul_le_mul (a.le i) (b.le i)⟩

private def powBound {f : SizeInput → ℕ} (a : Bound f) (k : ℕ) : Bound (fun i => f i^k) :=
  ⟨a.poly^k, fun i => by rw [Polynomial.eval_pow]; exact Nat.pow_le_pow_left (a.le i) k⟩

private def pairSizeBound {f g : SizeInput → ℕ} (a : Bound f) (b : Bound g) :
    Bound (fun i => pairBound (f i) (g i)) :=
  addBound (addBound (mulBound (constantBound 2) a) b) (constantBound 1)

private def listSizeBound {n w : SizeInput → ℕ} (count : Bound n) (width : Bound w) :
    Bound (fun i => listBound (n i) (w i)) :=
  addBound (mulBound count (addBound (mulBound (constantBound 2) width) (constantBound 2))) (constantBound 1)

/-- Lift every constructor of the checked trial stack encoding to its bounding polynomial. -/
private def trialLayoutBound (e : SizeInput → Envelope) {calls ticks : SizeInput → ℕ}
    (d : Bound (fun i => (e i).depth)) (v : Bound (fun i => (e i).vertices))
    (m : Bound (fun i => (e i).experts)) (w : Bound (fun i => (e i).width))
    (s : Bound (fun i => (e i).score)) (logs : Bound (fun i => (e i).logSize))
    (c : Bound calls) (t : Bound ticks) : Bound (fun i => (e i).stateSize (calls i) (ticks i)) := by
  let row := listSizeBound v w
  let weights := listSizeBound m w
  let history := listSizeBound d row
  let probe : Bound (fun i => (e i).probeSize) := pairSizeBound d (pairSizeBound row history)
  let result : Bound (fun i => (e i).resultSize) :=
    pairSizeBound row (pairSizeBound (listSizeBound m s) (listSizeBound logs probe))
  let input : Bound (fun i => (e i).inputSize) := pairSizeBound d (pairSizeBound history weights)
  let prep : Bound (fun i => (e i).preparedSize) :=
    pairSizeBound (constantBound 1) (pairSizeBound row (pairSizeBound (listSizeBound m row) weights))
  let completed : Bound (fun i => (e i).completedSize) :=
    pairSizeBound row (pairSizeBound row (pairSizeBound weights result))
  let saved := listSizeBound c completed
  let frame : Bound (fun i => (e i).frameSize (calls i)) :=
    pairSizeBound d (pairSizeBound c (pairSizeBound input (pairSizeBound saved prep)))
  let enter := pairSizeBound d input
  let schedule := pairSizeBound d (pairSizeBound c (pairSizeBound input saved))
  let feedback := pairSizeBound frame (pairSizeBound result t)
  let pc : Bound (fun i => (e i).pcSize (calls i) (ticks i)) :=
    addBound (addBound (addBound (addBound (constantBound 2) enter) schedule) result) feedback
  exact pairSizeBound pc (listSizeBound d frame)

private def horizonBound (k : ℕ)
    (cap : ∀ i : SizeInput, i.trials ≤ (i.goods+i.range.size+1)^k) : Bound SizeInput.trials :=
  ⟨Polynomial.X^k, fun i => by
    rw [Polynomial.eval_pow, Polynomial.eval_X]
    exact cap i⟩

attribute [local irreducible] Moment.probes Pool.catalogueExponent

set_option exponentiation.threshold 605 in
private def trialStateBound : Bound (fun i => (campaignEnvelope i.goods i.range i.trials).stateSize
    (2*Moment.probes) (totalTrialTicks i.goods)) := by
  let x : Bound argument := ⟨Polynomial.X, fun _ => by rw [Polynomial.eval_X]⟩
  let goods : Bound SizeInput.goods :=
    ⟨Polynomial.X, fun i => by rw [Polynomial.eval_X]; unfold argument; omega⟩
  let dep : Bound (fun i => depth i.goods) :=
    ⟨Polynomial.X, fun i => by
      rw [Polynomial.eval_X]
      exact (Nat.succ_le_succ (Nat.log2_le_self i.goods)).trans (by unfold argument; omega)⟩
  let time := horizonBound 300 SizeInput.cap
  let experts := powBound (mulBound x (addBound time (constantBound 1))) Pool.catalogueExponent
  let prices : Bound (fun i => campaignPriceBits i.goods i.range i.trials) :=
    ⟨pricePolynomial, fun i => campaignPriceBits_polynomial i.goods i.range i.trials i.cap⟩
  let register : Bound (fun i => Campaign.registerWeightPolynomial.eval (argument i)) :=
    ⟨Campaign.registerWeightPolynomial, fun _ => le_rfl⟩
  let priceWidth := addBound (mulBound (constantBound 2) prices) (constantBound 4)
  let registerBits := addBound (constantBound 3) (mulBound (constantBound 4) register)
  let getWidth := addBound priceWidth (addBound (mulBound (constantBound 2) registerBits) (constantBound 4))
  let twice := mulBound (constantBound 2) goods
  let branch := mulBound (constantBound 2) (addBound goods (constantBound 1))
  let ticks := addBound (mulBound (constantBound 5) (powBound twice 602)) (powBound branch 605)
  exact trialLayoutBound (fun i => campaignEnvelope i.goods i.range i.trials)
    dep (mulBound (constantBound 2) (powBound goods 2)) experts getWidth
    (powBound twice 274) (powBound branch 604) (constantBound (2*Moment.probes)) ticks

private opaque taggedTrialBound : Bound (fun i => pairBound (cursorWidth i.goods i.range i.trials)
    ((campaignEnvelope i.goods i.range i.trials).stateSize (2*Moment.probes) (totalTrialTicks i.goods))+1) :=
  let cursor : Bound (fun i => cursorWidth i.goods i.range i.trials) :=
    ⟨cursorPolynomial, fun i => cursorWidth_polynomial i.goods i.range i.trials i.cap⟩
  addBound (pairSizeBound cursor trialStateBound) (constantBound 1)

private theorem bound_at_input {f : SizeInput → ℕ} (b : Bound f) (N R T : ℕ)
    (cap : T ≤ (N+R.size+1)^300) : f ⟨N,R,T,cap⟩ ≤ b.poly.eval (N+R.size+1) :=
  b.le ⟨N,R,T,cap⟩

/-- The single polynomial used on both tags of the physical campaign interpreter. -/
def combinedPolynomial : Polynomial ℕ := taggedTrialBound.poly

theorem combined_trial_polynomial (N R T : ℕ) (hT : T ≤ (N+R.size+1)^300) :
    pairBound (cursorWidth N R T) ((campaignEnvelope N R T).stateSize (2*Moment.probes) (totalTrialTicks N))+1 ≤
      combinedPolynomial.eval (N+R.size+1) := by
  unfold combinedPolynomial
  exact bound_at_input taggedTrialBound N R T hT

theorem combined_campaign_polynomial (N R T : ℕ) (hT : T ≤ (N+R.size+1)^300) :
    cursorWidth N R T+1 ≤ combinedPolynomial.eval (N+R.size+1) := by
  have lift (x y : ℕ) : x+1 ≤ pairBound x y+1 := by unfold pairBound; omega
  exact (lift ..).trans (combined_trial_polynomial N R T hT)

end
end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
