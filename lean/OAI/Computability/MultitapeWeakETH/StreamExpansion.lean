import OAI.Computability.MultitapeWeakETH.ReaderEnumeration
import OAI.Computability.MultitapeWeakETH.VolumeBounds

/-! # Exact enumeration with separate outer and local Boolean loops -/

namespace OAI.Computability.MultitapeWeakETH.FactorizedCompression

open VPVNP Compression NetworkKernel PairSimulation.LocalHistory ReaderEnumeration Finset
open scoped Classical
noncomputable section

variable {k R : Type} [Field k] [Field R] {S : BlockSchedule k} (B : S.Templates) (f : B.Entry → R)
    (hf : B.IsSolution f) {g : ℕ} (T : ℕ) (h : T*S.laneBits ≤ g) (X : State (S.degreeExponent 0) g)

/-- A fixed-length deterministic search evaluates a local factor over its
monomial codes. Every rejected candidate contributes zero. -/
def localSum {I : Type} [Fintype I] {f : I → R} {N : Network}
    (Q : SiteParsers f N) (L : ℕ) (v : N.Site) (b : N.Half v) :=
  let W := Q.witnesses v b
  treeSum (fun bits => (decode (Q.read v b) bits).elim 0 (fun c => Diagonal.labelMonomial f (W.exponents c))) L []

theorem localSum_eq {I : Type} [Fintype I] {f : I → R} {N : Network}
    (Q : SiteParsers f N) (L : ℕ) (v : N.Site) (b : N.Half v)
    (hl : ∀ c, ((Q.read v b).encode c).length ≤ L) : localSum Q L v b = Q.factors v b :=
  (sum_decode (Q.read v b) L hl _).trans (Q.witnesses v b).evaluates

/-- One outer code and one shared assignment fix a product of independently
accumulated local sums. -/
def streamValue (P : SiteParsers f X.network) (H L : ℕ) : R :=
  let E := B.execute f hf T h X
  let reader := executeOuterReader B f hf T h X
  let term (z : E.Choices) :=
    let Q := finalParsers (E.termChain (B.records f hf T h X) z) (selectedParsers B f hf T h X z) P
    let Y := (E.finalState z).network
    ∑ bits : (e : Y.Edge) → Y.Payload e, ∏ v, localSum Q L v (WireTensor.edgeAssignment Y.src Y.dst bits v)
  treeSum (fun bits => (decode reader bits).elim 0 term) H []

theorem streamValue_eq (P : SiteParsers f X.network) (H L : ℕ)
    (outer : ∀ z, ((executeOuterReader B f hf T h X).encode z).length ≤ H)
    (localBound : ∀ z, let E := B.execute f hf T h X
      let Q := finalParsers (E.termChain (B.records f hf T h X) z) (selectedParsers B f hf T h X z) P
      ∀ v b c, ((Q.read v b).encode c).length ≤ L) :
    streamValue B f hf T h X P H L = contract X.network P.factors := by
  let E := B.execute f hf T h X
  let _ : Fintype E.Choices := choiceFintype E
  unfold streamValue
  rw [sum_decode _ _ outer]
  apply Eq.trans _ (contract_factorized E (B.records f hf T h X) P.factors).symm
  apply sum_congr rfl
  intro z _
  apply sum_congr rfl
  intro bits _
  apply prod_congr rfl
  intro v _
  let chain := E.termChain (B.records f hf T h X) z
  let parsers := selectedParsers B f hf T h X z
  let Q := finalParsers chain parsers P
  let Y := (E.finalState z).network
  let b := WireTensor.edgeAssignment Y.src Y.dst bits v
  exact (localSum_eq Q L v b (localBound z v b)).trans
    (congrFun (congrFun (finalParsers_factors chain parsers P) v) b)

end
end OAI.Computability.MultitapeWeakETH.FactorizedCompression
