import OAI.Computability.MultitapeWeakETH.PackedFormula
import OAI.Computability.MultitapeWeakETH.CompressionCounts
import OAI.Computability.VPVNP.CompressionBudget

/-! # A finite shared-wire expansion for the exact model count

Outer indices are compression histories and assignments of their surviving
wires. The local expansions remain inside the product. Each leaf factor is
a Boolean test, so a successful leaf consumes no private bits.
-/

namespace OAI.Computability.MultitapeWeakETH.FactorizedCompression

open Algorithms.SubexponentialSAT VPVNP Compression NetworkKernel PairSimulation.LocalHistory
  CompressorRecords Finset
open scoped Classical
noncomputable section

variable {R : Type} [Field R] {I : Type} [Fintype I] (f : I → R)

private def optionalReader (p : Prop) [Decidable p] : ChoiceReader {_u : Unit // p} where
  encode _ := []
  read bits := if h : p then some (⟨(),h⟩,bits) else none
  read_iff bits i tail := by
    have h := i.property
    simp [h]

/-- Zero or one monomial, with coefficient one and no template factors. -/
def indicatorParsers {N : Network} (A : Factors R N) (binary : ∀ u b, A u b = 0 ∨ A u b = 1) :
    SiteParsers f N where
  factors := A
  witnesses u b := (MonomialWitness.paths f {_z : Unit // A u b = 1}).changeValue (by
    rcases binary u b with h | h <;> simp [h,Fintype.card_subtype])
  read u b := optionalReader (A u b = 1)

theorem indicator_bits {N : Network} (A : Factors R N) (binary : ∀ u b, A u b = 0 ∨ A u b = 1)
    (u b c) : (((indicatorParsers f A binary).read u b).encode c).length = 0 := rfl

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates) (κ : B.Entry → R)
    (hf : B.IsSolution κ) {g : ℕ} (T : ℕ) (h : T*S.laneBits ≤ g) (X : State (S.degreeExponent 0) g)

/-- The nested sum of template monomials computes the input contraction
with independent local choices after each shared edge assignment. -/
theorem sum_products (P : SiteParsers κ X.network) :
    let E := B.execute κ hf T h X
    letI := choiceFintype E
    contract X.network P.factors =
      ∑ z : E.Choices, ∑ bits : (e : (E.finalState z).network.Edge) → (E.finalState z).network.Payload e,
        ∏ v, let chain := E.termChain (B.records κ hf T h X) z
             let Q := finalParsers chain (selectedParsers B κ hf T h X z) P
             let Y := (E.finalState z).network
             let W := Q.witnesses v (WireTensor.edgeAssignment Y.src Y.dst bits v)
             ∑ c, Diagonal.labelMonomial κ (W.exponents c) := by
  apply Eq.trans (contract_factorized _ (B.records κ hf T h X) P.factors)
  apply sum_congr rfl
  intro z _
  apply sum_congr rfl
  intro bits _
  apply prod_congr rfl
  intro v _
  let E := B.execute κ hf T h X
  let chain := E.termChain (B.records κ hf T h X) z
  let parsers := selectedParsers B κ hf T h X z
  let Q := finalParsers chain parsers P
  let Y := (E.finalState z).network
  let b := WireTensor.edgeAssignment Y.src Y.dst bits v
  exact (congrFun (congrFun (finalParsers_factors chain parsers P).symm v) b).trans (Q.witnesses v b).evaluates.symm

end
end OAI.Computability.MultitapeWeakETH.FactorizedCompression
