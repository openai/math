import OAI.Computability.MultitapeWeakETH.ResidentForest
import OAI.Computability.MultitapeWeakETH.IntegralStream
import OAI.Computability.MultitapeWeakETH.TerminalLayout

/-! # Common denominator for all physical terminal products -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords PairSimulation LocalHistory
open NetworkKernel DyadicBudget FactorizedCompression TemplateArithmetic
open scoped NumberField Classical
noncomputable section

variable {k K : Type} [_root_.Field k] [_root_.Field K] [NumberField K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f) (d : ℤ) (clear : ∀ i, IsIntegral ℤ ((d:K)*f i))
    (volume : Tally)

abbrev gridParsers (z : (gridExecution B f hf volume).Choices)
    (P : SiteParsers f (source B (gridIndex B volume)).network) :=
  let s := gridIndex B volume
  let X := source B s
  finalParsers ((gridExecution B f hf volume).termChain (B.records f hf s (lanes_fit B s) X) z)
    (selectedParsers B f hf s (lanes_fit B s) X z) P

variable (P : SiteParsers f (source B (gridIndex B volume)).network)

abbrev sharedHalf {a g : ℕ} (Y : State a g) (p : (e : Y.network.Edge) → Y.network.Payload e)
    (u : Y.network.Site) := WireTensor.edgeAssignment Y.network.src Y.network.dst p u

def terminalFactor (L : ℕ) (z : (gridExecution B f hf volume).Choices) :
    let Y := (gridExecution B f hf volume).finalState z
    ((e : Y.network.Edge) → Y.network.Payload e) → Y.network.Site → 𝓞 K :=
  fun p u => integralLocal f d clear (gridParsers B f hf volume z P) L L u (sharedHalf _ p u)

attribute [local irreducible] BlockProgram.script BlockProgram.layout OnlineWorkspace.table source scale entryMemory

set_option maxHeartbeats 1400000 in
/-- All paths have exactly the same terminal site count, so each product
carries the same power of the integer denominator. -/
theorem terminal_contraction (L count : ℕ)
    (value : contract (source B (gridIndex B volume)).network P.factors = (count:K))
    (bounds : ∀ z : (gridExecution B f hf volume).Choices,
      let Y := (gridExecution B f hf volume).finalState z
      let Q := gridParsers B f hf volume z P
      ∀ p u, let a := sharedHalf Y p u
        (∀ x, ((Q.read u a).encode x).length ≤ L) ∧ (∀ x, (∑ i, (Q.witnesses u a).exponents x i) ≤ L)) :
    let E := gridExecution B f hf volume
    let _ : Fintype E.Choices := choiceFintype E
    ∑ z : E.Choices, ∑ p : (e : (E.finalState z).network.Edge) → (E.finalState z).network.Payload e,
        ∏ u, terminalFactor B f hf d clear volume P L z p u =
      ((d^(L*sites B (gridIndex B volume))*(count:ℤ) : ℤ) : 𝓞 K) := by
  intro E inst
  let s := gridIndex B volume
  let X := source B s
  let recs := B.records f hf s (lanes_fit B s) X
  let φ := algebraMap (𝓞 K) K
  apply IsFractionRing.injective (𝓞 K) K
  simp only [map_sum,map_prod,Int.cast_mul,Int.cast_pow,Int.cast_natCast,map_mul,map_pow,map_intCast,map_natCast]
  rw [← value,contract_factorized E recs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  let Y := E.finalState z
  let Q := gridParsers B f hf volume z P
  have atSite (u : Y.network.Site) : φ (terminalFactor B f hf d clear volume P L z p u) =
      (d:K)^L * evaluate (E.termChain recs z) P.factors u (sharedHalf Y p u) := by
    let a := sharedHalf Y p u
    obtain ⟨len,deg⟩ := bounds z p u
    change algebraMap (𝓞 K) K (integralLocal f d clear Q L L u a) = _
    rw [integralLocal_eq _ _ _ _ _ _ _ _ deg,localSum_eq _ _ _ _ len]
    exact congrArg ((d:K)^L * ·) (congrFun (congrFun (finalParsers_factors _ _ P) u) a)
  change (∏ u, φ (terminalFactor B f hf d clear volume P L z p u)) = _
  simp only [atSite,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,← pow_mul]
  have card : Fintype.card Y.network.Site = sites B s := (terminal_size B f hf s z).1.symm
  rw [card]

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
