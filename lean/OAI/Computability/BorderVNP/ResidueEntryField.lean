import OAI.Computability.BorderVNP.ResidueEntryFieldTranscript
import OAI.Computability.QuantumFactoring.WordBlocks
import OAI.Computability.QuantumFactoring.ModularMultiply

/-! # Prime-field limbs for the §10.2 residue-entry computation

Coordinates in a supplied basis of the finite extension use ordinary binary representatives
in the prime field. The multiplication table and the matrix of a linear coordinate
projection are advice. The circuits below use binary modular arithmetic on the limbs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryField

open ExactQuantumFactoring BooleanNetwork BitArithmetic
open scoped BigOperators

variable {n d w p : ℕ}

/-- Natural value of a little-endian bit word. -/
def value (x : Fin w → Bool) : ℕ := (bitsValue x).toNat

/-- A fixed binary limb. This is also how the modulus is supplied to the reduction circuit. -/
def literal (n w a : ℕ) : BooleanNetwork n w := wordConstant (.ofNat w a)

private theorem literal_value (a : ℕ) (x : Fin n → Bool) (ha : a < 2^w) :
    value ((literal n w a).eval x) = a := by
  simp [literal, value, wordConstant_eval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

private theorem literal_count (a : ℕ) : (literal n w a).net.count = w :=
  wordConstant_count _

/-- Polynomial bound for the fixed overhead of a single prime-field operation. -/
def limbCost (w : ℕ) : ℕ := 2000 * (w+1)^2

/-- Multiply two prime-field limbs, returning the least nonnegative representative. -/
def times (p : ℕ) (a b : BooleanNetwork n w) : BooleanNetwork n w :=
  mulMod a b (literal n w p)

/-- Add two prime-field limbs and reduce the result modulo the prime. -/
def plus (p : ℕ) (a b : BooleanNetwork n w) : BooleanNetwork n w :=
  addMod a b (literal n w p)

private theorem times_count (a b : BooleanNetwork n w) :
    (times p a b).net.count ≤ a.net.count + b.net.count + limbCost w := by
  have h := mulMod_count a b (literal n w p)
  rw [literal_count] at h
  dsimp only [times, limbCost]
  nlinarith

private theorem plus_count (a b : BooleanNetwork n w) :
    (plus p a b).net.count ≤ a.net.count + b.net.count + limbCost w := by
  have h := addMod_count a b (literal n w p)
  rw [literal_count] at h
  dsimp only [plus, limbCost]
  nlinarith

variable [Fact p.Prime]

private theorem times_value (hp : p < 2^w) (a b : BooleanNetwork n w) (x : Fin n → Bool)
    (s t : ZMod p) (hs : value (a.eval x) = s.val) (ht : value (b.eval x) = t.val) :
    value ((times p a b).eval x) = (s*t).val := by
  have hm := literal_value p x hp
  have pos := (Fact.out : Nat.Prime p).pos
  unfold times value at *
  rw [mulMod_word _ _ _ _ (hm.symm ▸ pos), hm, hs, ht, ZMod.val_mul]

private theorem plus_value (hp : p < 2^w) (a b : BooleanNetwork n w) (x : Fin n → Bool)
    (s t : ZMod p) (hs : value (a.eval x) = s.val) (ht : value (b.eval x) = t.val) :
    value ((plus p a b).eval x) = (s+t).val := by
  have hm := literal_value p x hp
  have pos := (Fact.out : Nat.Prime p).pos
  unfold plus value at *
  rw [addMod_value _ _ _ _ (hm.symm ▸ pos), hm, hs, ht, ZMod.val_add]

/-- Sum a finite table of prime-field limb networks with a linear sequence of modular additions. -/
def sumLimbs (p : ℕ) (f : Fin d → BooleanNetwork n w) : BooleanNetwork n w :=
  sumMod (literal n w p) (List.ofFn f)

private theorem sumLimbs_value (hp : p < 2^w) (f : Fin d → BooleanNetwork n w)
    (x : Fin n → Bool) (v : Fin d → ZMod p) (hv : ∀ i, value ((f i).eval x) = (v i).val) :
    value ((sumLimbs p f).eval x) = (∑ i, v i).val := by
  have hm := literal_value p x hp
  have pos := (Fact.out : Nat.Prime p).pos
  unfold sumLimbs value at *
  rw [sumMod_value _ _ _ (hm.symm ▸ pos), hm, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, hv]
  rw [← ZMod.val_natCast]
  simp

omit [Fact p.Prime] in
private theorem sumLimbs_count (f : Fin d → BooleanNetwork n w) (c : ℕ)
    (hc : ∀ i, (f i).net.count ≤ c) :
    (sumLimbs p f).net.count ≤ w + d * (c + limbCost w) := by
  have h := sumMod_count (literal n w p) (List.ofFn f) (c := c) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hc i)
  rw [List.length_ofFn, literal_count] at h
  refine h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
  dsimp only [limbCost]
  nlinarith

variable {K : Type*} [Field K] [Algebra (ZMod p) K]

/-- All limbs equal the canonical prime-field representatives of the basis coordinates. -/
def Represents (B : Module.Basis (Fin d) (ZMod p) K) (v : Fin (d*w) → Bool) (a : K) : Prop :=
  ∀ i, value (block v i) = (B.coord i a).val

/-- Encode a supplied field constant as its basis coordinates. -/
noncomputable def fieldConst (n w : ℕ) (B : Module.Basis (Fin d) (ZMod p) K) (a : K) :
    BooleanNetwork n (d*w) := wordBlocks fun i => literal n w (B.coord i a).val

/-- Constant advice yields the canonical encoding. -/
theorem fieldConst_value (hp : p < 2^w) (B : Module.Basis (Fin d) (ZMod p) K)
    (a : K) (x : Fin n → Bool) : Represents B ((fieldConst n w B a).eval x) a := by
  intro i
  rw [fieldConst, wordBlocks_eval]
  exact literal_value _ _ ((ZMod.val_lt _).trans hp)

/-- Number of Boolean gates used to materialize a field constant. -/
theorem fieldConst_count (B : Module.Basis (Fin d) (ZMod p) K) (a : K) :
    (fieldConst n w B a).net.count ≤ d*w*w :=
  wordBlocks_count _ (fun _ => (literal_count _).le)

private theorem coord_mul (B : Module.Basis (Fin d) (ZMod p) K) (a b : K) (i : Fin d) :
    ∑ j, ∑ k, (B.coord j a * B.coord k b) * B.coord i (B j * B k) = B.coord i (a*b) := by
  conv_rhs => rw [← B.sum_repr a, ← B.sum_repr b]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_sum, map_smul,
    smul_eq_mul, mul_assoc, Module.Basis.coord_apply]
  rw [Finset.sum_comm]
  simp only [mul_left_comm]

/-- Circuit for a single output coordinate of a multiplication table. -/
noncomputable def productLimb (B : Module.Basis (Fin d) (ZMod p) K)
    (u v : Fin d → BooleanNetwork n w) (i : Fin d) : BooleanNetwork n w :=
  sumLimbs p fun j => sumLimbs p fun k =>
    times p (times p (u j) (v k)) (literal n w (B.coord i (B j * B k)).val)

private theorem productLimb_value (hp : p < 2^w) (B : Module.Basis (Fin d) (ZMod p) K)
    (u v : Fin d → BooleanNetwork n w) (x : Fin n → Bool) (a b : K)
    (hu : ∀ j, value ((u j).eval x) = (B.coord j a).val)
    (hv : ∀ k, value ((v k).eval x) = (B.coord k b).val) (i : Fin d) :
    value ((productLimb B u v i).eval x) = (B.coord i (a*b)).val := by
  rw [← coord_mul B a b i]
  apply sumLimbs_value hp
  intro j
  apply sumLimbs_value hp
  intro k
  apply times_value hp
  · exact times_value hp _ _ _ _ _ (hu _) (hv _)
  · exact literal_value _ _ ((ZMod.val_lt _).trans hp)

/-- Fixed gate budget for one multiplication coordinate with both operands supplied on wires. -/
def productLimbCost (d w : ℕ) : ℕ :=
  w + d * (w + d * (w + 3 * limbCost w) + limbCost w)

private theorem productLimb_count (B : Module.Basis (Fin d) (ZMod p) K)
    (u v : Fin d → BooleanNetwork n w) (hu : ∀ j, (u j).net.count = 0)
    (hv : ∀ k, (v k).net.count = 0) (i : Fin d) :
    (productLimb B u v i).net.count ≤ productLimbCost d w := by
  apply sumLimbs_count
  intro j
  refine (sumLimbs_count _ (w + 2*limbCost w) ?_).trans ?_
  · intro k
    have h := times_count (p := p) (u j) (v k)
    rw [hu, hv] at h
    have h' := times_count (p := p) (times p (u j) (v k)) (literal n w (B.coord i (B j*B k)).val)
    rw [literal_count] at h'
    omega
  · apply Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_)
    omega

/-- Apply a supplied prime-field linear projection to a field element. -/
noncomputable def linearLimb (B : Module.Basis (Fin d) (ZMod p) K) (π : K →ₗ[ZMod p] ZMod p) :
    BooleanNetwork (d*w) w := sumLimbs p fun i =>
      times p (blockNet d w i) (literal (d*w) w (π (B i)).val)

/-- The projection circuit computes the true prime-field coordinate. -/
theorem linearLimb_value (hp : p < 2^w) (B : Module.Basis (Fin d) (ZMod p) K)
    (π : K →ₗ[ZMod p] ZMod p) (a : K) (x : Fin (d*w) → Bool) (hx : Represents B x a) :
    value ((linearLimb B π).eval x) = (π a).val := by
  have h : (∑ i, B.coord i a * π (B i)) = π a := by
    conv_rhs => rw [← B.sum_repr a]
    simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]
  rw [← h]
  apply sumLimbs_value hp
  intro i
  exact times_value hp _ _ _ _ _ (hx i) (literal_value _ _ ((ZMod.val_lt _).trans hp))

/-- Gate count of a supplied linear projection. -/
theorem linearLimb_count (B : Module.Basis (Fin d) (ZMod p) K) (π : K →ₗ[ZMod p] ZMod p) :
    (linearLimb (w := w) B π).net.count ≤ w + d*(w + limbCost w + limbCost w) := by
  apply sumLimbs_count
  intro i
  simpa only [blockNet_count, zero_add, literal_count] using
    times_count (p := p) (blockNet d w i) (literal (d*w) w (π (B i)).val)

private def operand (side : Fin (d*w) → Fin (d*w+d*w)) (i : Fin d) :
    BooleanNetwork (d*w+d*w) w := select fun j => side (finProdFinEquiv (i,j))

/-- A field gate on a pair of encoded operands. Subtraction negates the second limb
by a prime-field scalar multiplication. Multiplication contracts the supplied table. -/
noncomputable def fieldGate (w : ℕ) (B : Module.Basis (Fin d) (ZMod p) K)
    (op : VPVNP.BinOp) : BooleanNetwork (d*w+d*w) (d*w) := wordBlocks fun i =>
  let u := operand (Fin.castAdd (d*w))
  let v := operand (Fin.natAdd (d*w))
  match op with
  | .add => plus p (u i) (v i)
  | .sub => plus p (u i) (times p (v i) (literal _ _ (-1 : ZMod p).val))
  | .mul => productLimb B u v i

/-- All three field operations agree on every pair of canonically encoded inputs. -/
theorem fieldGate_value (hp : p < 2^w) (B : Module.Basis (Fin d) (ZMod p) K)
    (op : VPVNP.BinOp) (x y : Fin (d*w) → Bool) (a b : K)
    (hx : Represents B x a) (hy : Represents B y b) :
    Represents B ((fieldGate w B op).eval (Fin.append x y)) (op.apply a b) := by
  let u := operand (Fin.castAdd (d*w))
  let v := operand (Fin.natAdd (d*w))
  have hu (i : Fin d) : value ((u i).eval (Fin.append x y)) = (B.coord i a).val := by
    convert hx i using 2
    funext j
    exact Fin.append_left _ _ _
  have hv (i : Fin d) : value ((v i).eval (Fin.append x y)) = (B.coord i b).val := by
    convert hy i using 2
    funext j
    exact Fin.append_right _ _ _
  intro i
  rw [fieldGate, wordBlocks_eval]
  cases op with
  | add => simpa only [VPVNP.BinOp.apply, map_add] using
      plus_value hp (u i) (v i) _ _ _ (hu i) (hv i)
  | sub =>
    have hs := times_value hp (v i) (literal _ w (-1 : ZMod p).val) (Fin.append x y)
      (B.coord i b) (-1) (hv i) (literal_value _ _ ((ZMod.val_lt _).trans hp))
    simpa only [VPVNP.BinOp.apply, map_sub, map_add, map_neg, mul_neg, mul_one, sub_eq_add_neg] using
      plus_value hp (u i) (times p (v i) (literal _ _ (-1 : ZMod p).val)) _ _ _ (hu i) hs
  | mul => exact productLimb_value hp B u v _ a b hu hv i

/-- A common polynomial gate budget for the field operations. -/
def fieldGateCost (d w : ℕ) : ℕ := d*w*(w + 2*limbCost w + productLimbCost d w)

/-- The bit complexity of one shared arithmetic operation is polynomial in the number of
coordinates and the modulus width, including the cost of reading the advised table. -/
theorem fieldGate_count (B : Module.Basis (Fin d) (ZMod p) K) (op : VPVNP.BinOp) :
    (fieldGate w B op).net.count ≤ fieldGateCost d w := by
  apply wordBlocks_count
  intro i
  let u := operand (Fin.castAdd (d*w))
  let v := operand (Fin.natAdd (d*w))
  have hu (j : Fin d) : (u j).net.count = 0 := rfl
  have hv (j : Fin d) : (v j).net.count = 0 := rfl
  cases op with
  | add =>
    have h := plus_count (p := p) (u i) (v i)
    rw [hu,hv] at h
    exact h.trans (by omega)
  | sub =>
    have h := times_count (p := p) (v i) (literal _ w (-1 : ZMod p).val)
    have hh := plus_count (p := p) (u i) (times p (v i) (literal _ w (-1 : ZMod p).val))
    rw [hv, literal_count] at h
    rw [hu] at hh
    exact hh.trans (by omega)
  | mul => exact (productLimb_count B u v hu hv i).trans (by omega)

end ResidueEntryField

end BorderVNP
end Computability
end OAI
