import OAI.Computability.VPVNP.MacaulaySignedLeaf
import OAI.Computability.VPVNP.AffinePinCoefficient

/-! # Original-equation coefficients on the native matrix-reader bus -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead.SignedLeaf

open RAMTape BurstRAM UniversalCountStack MacaulayRowDispatch JointLabelSystem
open RadicalCertificate.MonomialIndex MvPolynomial

variable {K : Type} (V I : Type*) [Fintype V] [Fintype I] (F : I → MvPolynomial V ℤ) {n : ℕ} (c : ℕ)
variable {p e : ℕ} [Fact p.Prime] [NeZero e]

/-- Install the signed coefficient routine's initial layout and empty input and output stacks
at the embedded payload ports. -/
noncomputable def preload (inc : JointScalar.Leaf.Port ↪ K) (L : JointScalar.Leaf.Layout)
    (base : Stacks K) : Stacks K :=
  installStacks inc base (JointScalar.Leaf.clean L [] [] [])

theorem preload_correct (inc : JointScalar.Leaf.Port ↪ K) (L : JointScalar.Leaf.Layout) (base : Stacks K) :
    Loaded L inc (preload inc L base) := fun i _ _ _ => installStacks_at inc.injective base _ i

/-- Stack-length bound for one signed coefficient lookup, covering the Boolean checker,
coefficient bank and local scalar operations. -/
noncomputable abbrev callSpace (hn : 2 ≤ n) (w v : ℕ) (_modulus : SliceArithmetic.Vector p e) :=
  let C := JointScalar.checker V I F c hn w
  let L := JointScalar.Leaf.layout V I F c hn w p e v
  let b := JointScalar.Leaf.bankSize L w (FixedRows.labelTotal V n c * w)
  max (stackLimit C) b + JointScalar.Leaf.localCost L b

/-- Tick bound for one signed coefficient lookup, including both witness counts and the local
scalar operations. -/
noncomputable abbrev callTime (hn : 2 ≤ n) (w v : ℕ) (_modulus : SliceArithmetic.Vector p e) :=
  let C := JointScalar.checker V I F c hn w
  let L := JointScalar.Leaf.layout V I F c hn w p e v
  let b := JointScalar.Leaf.bankSize L w (FixedRows.labelTotal V n c * w)
  2*(2^L.witnessBits * perChoice C) + JointScalar.Leaf.localCost L b

private theorem encode_cast {E : Type*} [Field E] [Algebra (ZMod p) E] {m : SliceArithmetic.Vector p e}
    (φ : AdjoinRoot (SliceArithmetic.modulus m) ≃ₐ[ZMod p] E) (z : ℤ) :
    (z : Scalar m) = AffinePin.Query.encode φ (z : E) := by
  apply φ.injective.comp (Scalar.interpret_injective m)
  change φ (Scalar.interpretation m _) = φ (Scalar.interpretation m _)
  rw [AffinePin.Query.value_encode, map_intCast, map_intCast]

set_option maxHeartbeats 1600000 in
/-- On a divisible original row the decoded index and exponent buffer yield
the encoded coefficient of the integer system after base change to the
evaluation field. All scan buffers and the leaf advice survive the call. -/
theorem coefficient [DecidableEq K] (hn : 2 ≤ n) {w v S : ℕ} {modulus : SliceArithmetic.Vector p e}
    {E : Type*} [Field E] [Algebra (ZMod p) E] (φ : AdjoinRoot (SliceArithmetic.modulus modulus) ≃ₐ[ZMod p] E)
    (inc : JointScalar.Leaf.Port ↪ K) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (row : Fin (2^n+Fintype.card I)) (d : Fin (FixedRows.labelTotal V n c) →₀ ℕ) (hd : ∀ i, d i < 2^w)
    (rs : Reg → BurstRAM.Word w) (hi : (rs (outReg 1)).val = row.val)
    (data : Bool → PairCall.Inputs) (pack flag constants : Bool → List Bool) (aux : Stacks K)
    (hpack : pack false = ExponentPack.packed w (List.ofFn (fun i => d i)))
    (hpre : Loaded (JointScalar.Leaf.layout V I F c hn w p e v) inc aux)
    (hS : callSpace V I F c hn w v modulus ≤ S)
    (room : ∀ i, (frame rs [] (Arms.storage w data pack flag constants aux) i).length ≤ S) :
    let poly := unionEquations (grammarEquation hn c) F (FixedRows.rowIndex I n row)
    let ans := AffinePin.Query.encode φ ((MvPolynomial.map (Int.castRingHom E) poly).coeff d)
    ∃ steps ≤ callTime V I F c hn w v modulus,
      (JointScalar.Leaf.machine.onPorts (ports inc)).BoundedRun S steps
        (frame rs [] (Arms.storage w data pack flag constants aux))
        (frame rs (Engine.scalar v ans) (Arms.storage w data pack flag constants aux)) := by
  intro poly ans
  let L := JointScalar.Leaf.layout V I F c hn w p e v
  have fit : row.val < 2^w := hi ▸ (rs (outReg 1)).isLt
  obtain ⟨steps,ht,hr⟩ := JointScalar.Leaf.coefficient_bounded V I F c hn w modulus hv w row fit
    (fun i => d i) hd
  have hvec : exponentVector (fun i => d i) = d := Finsupp.ext fun _ => rfl
  rw [hvec] at hr
  have hans : (poly.coeff d : Scalar modulus) = ans := by
    dsimp only [ans]
    rw [MvPolynomial.coeff_map]
    exact encode_cast φ _
  have hp : pack false = JointScalar.Leaf.packed w (fun i => d i) := hpack
  refine ⟨steps,ht,bounded rs data pack flag constants aux inc inc.injective L hpre _ room ?_⟩
  rw [hi,hp,← hans]
  exact hr.enlarge hS

end RankQuery.Stack.MacaulayRead.SignedLeaf

end VPVNP
end Computability
end OAI
