import OAI.Computability.VPVNP.JointScalarLeafCall
import OAI.Computability.VPVNP.JointScalarLeafEncoding

/-! # Returning field-scalar query for the grammar and local motif equations

The input words carry the decoded equation number and the residual monomial.
Both remain available after the call. One fixed finite program returns the
formal integer coefficient cast to the presented scalar ring.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointScalar.Leaf

open MvPolynomial RAMTape UniversalCountStack JointLabelSystem RadicalCertificate.MonomialIndex

variable (V I : Type*) [Fintype V] [Fintype I] (F : I → MvPolynomial V ℤ) {n : ℕ} (c : ℕ)

/-- Immutable advice for the signed coefficient callback. -/
noncomputable def layout (hn : 2 ≤ n) (W p e v : ℕ) : Layout where
  prime := p
  degree := e
  limbWidth := v
  rowBits := n + highWidth I
  witnessBits := witnessWidth (ParseOracle.Flags n n (Fin (n^(c+5)))) (n^clockExponent) (motifWidth V I F)
  circuitAdvice := AdviceCircuit.encode (AdviceCircuit.compile (checker V I F c hn W))

set_option maxHeartbeats 1600000 in
/-- The two counts and the field conversion are actual nested calls in the
finite machine, with separate bounds on time and maximum stack height. -/
theorem coefficient_bounded (hn : 2 ≤ n) (W : ℕ) {p e v : ℕ} [Fact p.Prime] [NeZero e]
    (modulus : SliceArithmetic.Vector p e) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (wr : ℕ) (row : Fin (2^n + Fintype.card I)) (hj : row.val < 2^wr)
    (a : Fin (FixedRows.labelTotal V n c) → ℕ) (ha : ∀ i, a i < 2^W) :
    let C := checker V I F c hn W
    let L := layout V I F c hn W p e v
    let b := bankSize L wr (FixedRows.labelTotal V n c * W)
    let k := localCost L b
    let z := (unionEquations (grammarEquation hn c) F (FixedRows.rowIndex I n row)).coeff (exponentVector a)
    ∃ steps ≤ 2*(2^L.witnessBits * perChoice C) + k,
      machine.BoundedRun (max (stackLimit C) b + k) steps
        (clean L (digits wr row.val) (packed W a) [])
        (clean L (digits wr row.val) (packed W a) (RankQuery.Stack.Engine.scalar v (z : RankQuery.Stack.Scalar modulus))) := by
  intro C L b k z
  have signed (s : Bool) : TapeWord.value (digits (L.witnessBits+1) (Motif.part s z)) = Motif.part s z :=
    scalar_digits_value V I F c hn W row s a ha
  have joint := call_bounded modulus hv L rfl rfl rfl wr row.val hj (packed W a)
    (fun s => Motif.part s z) z (stackLimit C) (2^L.witnessBits*perChoice C) (fun s => by
      have eq : s :: (digits L.rowBits row.val ++ packed W a) =
          List.ofFn (query (n := n) (high := highWidth I) (W := W) s row.val a) :=
        (query_bits n (highWidth I) W s row.val a).symm
      rw [eq]
      dsimp only [L, layout, C, z, Layout.witnessBits, Layout.circuitAdvice]
      exact scalar_runs V I F c hn W row s a ha)
    (by rw [signed false,signed true]; exact signedParts_sub z)
  have hlen := packed_length W a
  rw [hlen] at joint
  exact joint

end JointScalar.Leaf

end VPVNP
end Computability
end OAI
