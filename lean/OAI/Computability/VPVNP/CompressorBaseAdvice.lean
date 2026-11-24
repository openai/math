import OAI.Computability.VPVNP.MacaulayBaseAdvice
import OAI.Computability.VPVNP.CompressorReaderBudgets
import OAI.Computability.VPVNP.RankQueryUniformResources

/-! # Fixed Macaulay reader advice at an admissible compressor length

The grammar checker stream, affine pin mask and field values, graded monomial
bounds and row counts are all chosen at the input length. The same bank serves
every coordinate query. Its height bound uses the reader plan fixed before the
prime and slice, including in characteristic zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead.BaseAdvice

open RadicalCertificate.MonomialIndex Coordinate.ConcreteResources

/-- All three immutable row-decoder parameters fit in the plan's physical
address words, even when an equation block is empty. -/
theorem plan_registers_fit {P : ReaderPlan} {F : Type*} {S : QueryData P.arity (P.equations+P.pins) F}
    (h : P.Covers S) {w : ℕ} (hw : P.wordWidth ≤ w) :
    P.equations < 2^w ∧ P.pins < 2^w ∧ size P.arity S.multiplierDegree < 2^w := by
  have dense : size P.arity S.multiplierDegree ≤ rawSize P.arity P.multiplier := by
    rw [size_eq_card]
    exact (RadicalCertificate.card_boundedMonomial_le ..).trans ((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans
      (ReaderPlan.raw_mono _ h.degrees.2.1))
  have hcap := (Nat.le_pow_clog (by decide : 1<2) P.addressLimit).trans
    (Nat.pow_le_pow_right (by decide : 0<2) (P.dispatchWidth.2.1.trans hw))
  change P.addressLimit ≤ 2^w at hcap
  unfold ReaderPlan.addressLimit at hcap
  omega

end RankQuery.Stack.MacaulayRead.BaseAdvice

namespace Compression.BlockSchedule.Templates

open LabelEvaluator RadicalCertificate.MonomialIndex RankQuery.Stack RAMTape SliceArithmetic
open MacaulayRead (BaseAdvice.RawPort)

local instance rawAdvicePrime (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩
/-- Finite enumeration of the ground field used to encode the Macaulay reader's affine pin
values. -/
noncomputable local instance rawAdviceFintype (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) := Fintype.ofFinite _
/-- Equality decision for elements of the ground field used in the fixed advice bank. -/
noncomputable local instance rawAdviceDecidable (p : Nat.Primes) (t d : ℕ) : DecidableEq (Ground p t d) := Classical.decEq _

variable {k : Type*} [Field k] {sched : BlockSchedule k} (B : sched.Templates) {p : Nat.Primes} {n c e : ℕ}
    (hn : 2 ≤ n) (M : Model p (B.compressorDegree n) (B.compressorEquations hn c))
    (modulus : Vector p.val e) (φ : AdjoinRoot (SliceArithmetic.modulus modulus) ≃ₐ[ZMod p.val]
      Ground p (B.compressorLabelCount c n) (B.compressorDegree n))

local notation "data" => M.queryData (B.compressorCoeff hn c)
local notation "orig" => (2^n+Fintype.card B.EquationIndex)
local notation "values" => (fun i ↦ AffinePin.Query.encode φ (M.values i))

/-- Actual immutable base matrix state before the first call. Its checker
parameters refer to the fixed equation types of both compressor templates. -/
noncomputable def compressorBaseBank (w v : ℕ) : Stacks MacaulayRead.BaseAdvice.RawPort :=
  let L := JointScalar.Leaf.layout B.Entry B.EquationIndex B.equation c hn w p.val e v
  MacaulayRead.BaseAdvice.initial (orig) (data) L modulus w v M.pins (values)

/-- The base advice stacks contain the equation data, modulus, affine pins and encoded pin
values for the chosen compressor instance. -/
noncomputable def compressorBaseReady (w v : ℕ) : Stacks MacaulayRead.BaseAdvice.RawPort → Prop :=
  let L := JointScalar.Leaf.layout B.Entry B.EquationIndex B.equation c hn w p.val e v
  MacaulayRead.BaseAdvice.ready (orig) (data) L modulus w v M.pins (values)

theorem compressorBaseBank_ready (q w v : ℕ) (hp : q ≠ 0 → p.val = q)
    (hz : q = 0 → p.val ≤ 2^B.compressorPrimeBits c n) (hw : (B.compressorReaderPlan q c n).wordWidth ≤ w) :
    B.compressorBaseReady hn M modulus φ w v (B.compressorBaseBank hn M modulus φ w v) := by
  obtain ⟨covers, _, _⟩ := B.compressorReaderCovers q c hn p M hp hz
  obtain ⟨ho, ht, hm⟩ := MacaulayRead.BaseAdvice.plan_registers_fit covers hw
  exact MacaulayRead.BaseAdvice.initial_ready _ _ _ _ _ _ _ _ ho ht hm

/-- The bound is uniform over the advised modulus and every ready state.
The original matrix reader's scratch registers need only satisfy its ready predicate. -/
theorem compressorBaseReady_length (q w v signedSpace : ℕ) (he : e ≤ B.readerDegreeBudget q c n)
    (hv : v ≤ B.readerLimbBudget q c n)
    (hs : JointScalar.Leaf.bankSize (JointScalar.Leaf.layout B.Entry B.EquationIndex B.equation c hn w p.val e v)
      w (B.compressorLabelCount c n*w) ≤ signedSpace)
    (s : Stacks MacaulayRead.BaseAdvice.RawPort) (h : B.compressorBaseReady hn M modulus φ w v s) (j : MacaulayRead.BaseAdvice.RawPort) :
    (s j).length ≤ (B.compressorReaderPlan q c n).live (B.readerDegreeBudget q c n) (B.readerLimbBudget q c n) w signedSpace :=
  MacaulayRead.BaseAdvice.ready_length_uniform (B.compressorReaderPlan q c n) (data) _ modulus M.pins (values)
    rfl he hv hs s h j

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
