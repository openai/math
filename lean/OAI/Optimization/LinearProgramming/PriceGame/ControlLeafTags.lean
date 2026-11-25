import OAI.Optimization.LinearProgramming.PriceGame.LearningAddressMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine
import OAI.Computability.QuantumFactoring.BitStackFold

/-! The low address bits determine the sign-dependent terminal mass. The comparison
scans the physical address word, even when the supplied binary level exceeds its length. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure States.Mass

/-- Each matching child tag is a low one bit in the mixed-radix address. -/
def lowTagCount (address level : ℕ) := (address.bits.take level).count true

private theorem lowTagCount_child (a k : ℕ) (b : Bool) :
    lowTagCount ((finTwoEquiv.symm b).val + 2*a) (k+1) = lowTagCount a k + (if b then 1 else 0) := by
  cases b with
  | false =>
    change lowTagCount (0+2*a) (k+1) = lowTagCount a k + 0
    by_cases ha : a = 0
    · simp [lowTagCount,ha]
    · simp [lowTagCount,Nat.bit0_bits a ha]
  | true =>
    change lowTagCount (1+2*a) (k+1) = lowTagCount a k + 1
    rw [Nat.add_comm 1 (2*a)]
    simp [lowTagCount,Nat.bit1_bits]

theorem lowTagCount_vertex (N l : ℕ) (v : Vertex N l) :
    lowTagCount (vertexEquivFin N l v).val l = matchingTags N l true v := by
  induction l with
  | zero => simp [lowTagCount,matchingTags]
  | succ k ih =>
    obtain ⟨i,b⟩ := v
    change lowTagCount ((finTwoEquiv.symm b).val + 2*(vertexEquivFin N k i).val) (k+1) = _
    rw [lowTagCount_child,ih]
    cases b <;> rfl

private abbrev counterCode := prodCode Nat.bits unaryCode

private def tagStep (b : Bool) (s : ℕ × ℕ) :=
  if s.1 = 0 then s else (s.1-1,s.2+(if b then 1 else 0))

private theorem count_fold (xs : List Bool) (k c : ℕ) :
    (xs.foldl (bitAction (tagStep false) (tagStep true)) (k,c)).2 = c + (xs.take k).count true := by
  induction xs generalizing k c with
  | nil => simp
  | cons b bs ih =>
    cases k with
    | zero => cases b <;> simpa [bitAction,tagStep] using ih 0 c
    | succ k =>
      cases b <;> simp [bitAction,tagStep,ih]
      omega

private noncomputable def tagStepP (b : Bool) : Procedure counterCode counterCode (tagStep b) := by
  let k := first Nat.bits unaryCode
  let c := second Nat.bits unaryCode
  let dec := binarySub.comp (k.pair (constant counterCode Nat.bits 1))
  let inc := unaryAdd.comp (c.pair (constant counterCode unaryCode (if b then 1 else 0)))
  apply (conditional (binaryZero.comp k) (identity counterCode) (dec.pair inc)).congrFun
  intro s
  simp [tagStep]

private theorem tagStep_size (b : Bool) (s : ℕ × ℕ) :
    (counterCode (tagStep b s)).length ≤ (counterCode s).length + 1 := by
  have hk := bits_length_mono (Nat.sub_le s.1 1)
  cases b <;> by_cases hz : s.1 = 0 <;>
    simp [tagStep,hz,counterCode,prodCode,pairBits_length,unaryCode] <;> omega

/-- The only dynamic loop runs for the actual physical address word length. -/
noncomputable def lowTagCountP : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun p => lowTagCount p.1 p.2) := by
  let arg := prodCode Nat.bits Nat.bits
  let word := ((identity (id : List Bool → List Bool)).precompose Nat.bits).comp (first Nat.bits Nat.bits)
  let start := (second Nat.bits Nat.bits).pair (constant arg unaryCode 0)
  let scan := foldBitsLinear (tagStepP false) (tagStepP true) 1 (tagStep_size false) (tagStep_size true)
  apply (unaryToBits.comp ((second Nat.bits unaryCode).comp (scan.comp (word.pair start)))).congrFun
  rintro ⟨a,k⟩
  change (a.bits.foldl (bitAction (tagStep false) (tagStep true)) (k,0)).2 = (a.bits.take k).count true
  rw [count_fold,Nat.zero_add]

/-- On every reachable node the common denominator is the stored vertex-row width. -/
def leafPositive (address level width : ℕ) : Bool := decide (4*lowTagCount address level < width.size)

theorem leafPositive_vertex (N l : ℕ) (v : Vertex N l) :
    leafPositive (vertexEquivFin N l v).val l (N*2^l) = true ↔ weight N l true v ≤ 1 := by
  have hn : 0 < N := by
    by_contra! h
    have ha := (vertexEquivFin N l v).isLt
    simp [Nat.eq_zero_of_le_zero h] at ha
  have hden : 0 < (N:ℚ)*2^l := by positivity
  rw [leafPositive,decide_eq_true_eq,lowTagCount_vertex,Nat.lt_size,weight_dyadic,div_le_one hden]
  rw [pow_mul]
  norm_cast

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
