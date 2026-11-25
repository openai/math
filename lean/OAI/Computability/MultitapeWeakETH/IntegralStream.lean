import OAI.Computability.MultitapeWeakETH.IntegralSums
import OAI.Computability.MultitapeWeakETH.StreamExpansion

/-! # Exact streamed accumulation in the fixed ring of integers -/

namespace OAI.Computability.MultitapeWeakETH.FactorizedCompression

open VPVNP Compression PairSimulation.LocalHistory NetworkKernel ReaderEnumeration TemplateArithmetic
open scoped NumberField Classical BigOperators
noncomputable section

private theorem map_search {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) (c : R)
    (g : List Bool → A) (f : List Bool → R) (term : ∀ w, φ (g w) = c*f w) (k : ℕ) (acc : List Bool) :
    φ (treeSum g k acc) = c*treeSum f k acc := by
  induction k generalizing acc with
  | zero => exact term acc
  | succ k ih => simp only [treeSum,map_add,ih,mul_add]

variable {I K : Type} [Fintype I] [Field K] [NumberField K] (f : I → K) (d : ℤ)
    (integral : ∀ i, IsIntegral ℤ ((d:K)*f i))

def integralLocal {N : Network} (Q : SiteParsers f N) (L M : ℕ) (v : N.Site) (a : N.Half v) : 𝓞 K :=
  treeSum (fun w => (decode (Q.read v a) w).elim 0 fun c =>
    scaledTerm f d integral M ((Q.witnesses v a).exponents c)) L []

omit [NumberField K] in
theorem integralLocal_eq {N : Network} (Q : SiteParsers f N) (L M : ℕ) (v : N.Site) (a : N.Half v)
    (deg : ∀ c, (∑ i, (Q.witnesses v a).exponents c i) ≤ M) :
    algebraMap (𝓞 K) K (integralLocal f d integral Q L M v a) = (d:K)^M*localSum Q L v a := by
  apply map_search
  intro w
  cases h : decode (Q.read v a) w with
  | none => simp
  | some c => exact scaled_term_eq f d integral M _ (deg c)

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    (κ : B.Entry → K) (hf : B.IsSolution κ) (clear : ∀ i, IsIntegral ℤ ((d:K)*κ i))
    {g : ℕ} (T : ℕ) (h : T*S.laneBits ≤ g) (X : State (S.degreeExponent 0) g)

/-- Each terminal factor uses denominator d^M. Padding the product up to the
initial position count gives all histories the same denominator. -/
def integralStream (P : SiteParsers κ X.network) (H L M : ℕ) : 𝓞 K :=
  let E := B.execute κ hf T h X
  let term (z : E.Choices) :=
    let Y := E.finalState z
    let Q := finalParsers (E.termChain (B.records κ hf T h X) z) (selectedParsers B κ hf T h X z) P
    ∑ bits : (e : Y.network.Edge) → Y.network.Payload e,
      (d^(M*(X.positions-Y.positions))) •
        ∏ v, integralLocal κ d clear Q L M v (WireTensor.edgeAssignment Y.network.src Y.network.dst bits v)
  treeSum (fun w => (decode (executeOuterReader B κ hf T h X) w).elim 0 term) H []

omit [NumberField K] in
theorem integralStream_eq (P : SiteParsers κ X.network) (H L M : ℕ)
    (degree : ∀ z, let E := B.execute κ hf T h X
      let Q := finalParsers (E.termChain (B.records κ hf T h X) z) (selectedParsers B κ hf T h X z) P
      ∀ v a c, (∑ i, (Q.witnesses v a).exponents c i) ≤ M) :
    algebraMap (𝓞 K) K (integralStream d B κ hf clear T h X P H L M) =
      (d:K)^(M*X.positions)*streamValue B κ hf T h X P H L := by
  let E := B.execute κ hf T h X
  apply map_search
  intro w
  cases hz : decode (executeOuterReader B κ hf T h X) w with
  | none => simp
  | some z =>
    let Y := E.finalState z
    let Q := finalParsers (E.termChain (B.records κ hf T h X) z) (selectedParsers B κ hf T h X z) P
    have pos : Y.positions ≤ X.positions := by
      rw [(B.branch_bounds κ hf T h X z).1]
      exact Nat.le_mul_of_pos_left _ (pow_pos (by have := S.positionFactor_gt_two; omega) _)
    simp only [Option.elim_some,map_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro bits _
    simp only [zsmul_eq_mul,map_mul,map_prod,Int.cast_pow,map_pow,map_intCast]
    change (d:K)^(M*(X.positions-Y.positions)) *
        (∏ v, algebraMap (𝓞 K) K (integralLocal κ d clear Q L M v _)) = _
    simp_rw [fun v => integralLocal_eq κ d clear Q L M v _ (degree z v _)]
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,← pow_mul,← mul_assoc,← pow_add]
    congr 2
    change M*(X.positions-Y.positions)+M*Y.positions = M*X.positions
    rw [← Nat.mul_add,Nat.sub_add_cancel pos]

end
end OAI.Computability.MultitapeWeakETH.FactorizedCompression
