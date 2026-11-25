import OAI.LinearAlgebra.MatrixExponent.CompareExchange
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ToLin
import OAI.LinearAlgebra.MatrixExponent.Network.Dense

section
namespace OAI.LinearAlgebra.MatrixExponent

/-- A matrix encoding on binary indices. Padding by zeros preserves products
but need not preserve the identity matrix on unused indices. -/
structure Representation (F L : Type) [Field F] [Field L] [Algebra F L] where
  wire : Wire
  root : Val wire
  M : L →ₗ[F] Matrix (Val wire) (Val wire) F
  mul : ∀ u v, M (u * v) = M u * M v
  scalar : ∀ x, M (algebraMap F L x) root root = x
  width : 2 ^ wd wire ≤ 2 * Module.finrank F L

private theorem card_word (n : ℕ) : Fintype.card (Val (word n)) = 2 ^ n := by
  induction n with
  | zero => change Fintype.card Unit = 1; simp
  | succ n ih =>
    change Fintype.card (Bool × Val (word n)) = _
    rw [Fintype.card_prod, Fintype.card_bool, ih, pow_succ']

/-- Use the regular representation and pad the complementary block with zeros.
Any active diagonal index recovers base-field elements. -/
theorem exists_representation (F L : Type) [Field F] [Field L] [Algebra F L]
    [Module.Finite F L] : Nonempty (Representation F L) := by
  classical
  let d := Module.finrank F L
  have hd : 0 < d := Module.finrank_pos
  let c := Nat.clog 2 d
  have hl : d ≤ 2 ^ c := Nat.le_pow_clog (by decide) d
  have hu : 2 ^ c ≤ 2 * d := by
    cases hc : c with
    | zero => simp only [pow_zero]; omega
    | succ n =>
      have hn : n < Nat.clog 2 d := by change n < c; omega
      rw [pow_succ']
      exact Nat.mul_le_mul_left 2 (Nat.pow_lt_of_lt_clog hn).le
  let I := Fin d ⊕ Fin (2 ^ c - d)
  let e : I ≃ Val (word c) := Fintype.equivOfCardEq (by
    rw [card_word]
    simp only [I, Fintype.card_sum, Fintype.card_fin]
    omega)
  let A := Algebra.leftMulMatrix (Module.finBasis F L)
  let B : L →ₗ[F] Matrix I I F :=
    { toFun := fun x => Matrix.fromBlocks (A x) 0 0 0
      map_add' := by intros; simp [I, Matrix.fromBlocks_add]
      map_smul' := by intros; simp [I, Matrix.fromBlocks_smul] }
  let E := Matrix.reindexAlgEquiv F F e
  let i : Fin d := ⟨0, hd⟩
  refine ⟨⟨word c, e (.inl i), E.toLinearMap.comp B, ?_, ?_, ?_⟩⟩
  · intro x y
    change E (B (x * y)) = E (B x) * E (B y)
    rw [← map_mul]
    apply congrArg E
    simp [B, I, Matrix.fromBlocks_multiply]
  · intro x
    change B (algebraMap F L x) (e.symm (e (.inl i))) (e.symm (e (.inl i))) = x
    rw [Equiv.symm_apply_apply]
    change A (algebraMap F L x) i i = x
    rw [A.commutes]
    simp [Algebra.algebraMap_eq_smul_one]
  · rw [wd_word]
    exact hu

end OAI.LinearAlgebra.MatrixExponent
end

section
/-!
# Returning a trivalent network to its ground field

A matrix index passes through the original vertices in sequence. Parallel
composition concatenates two chains, and trace sums the original wires. A
single additional table selects the distinguished index at both ends.
-/

namespace OAI.LinearAlgebra.MatrixExponent

variable {F L : Type} [Field F] [Field L] [Algebra F L]
variable {a b c d : Wire} {m n : ℕ}

namespace Representation

variable (R : Representation F L)

private def cost : ℕ := 8 * 2 ^ (wd R.wire + wd R.wire)

private def lifted (k : Val a → Val b → L) :
    Val (.pair a R.wire) → Val (.pair b R.wire) → F :=
  fun x y => R.M (k x.1 y.1) x.2 y.2

/-- The first branch handles empty networks without allocating an index.
Every nonempty chain reserves enough vertices to pin its ends once. -/
private def Chain (a b : Wire) (k : Val a → Val b → L) (m : ℕ) : Prop :=
  (∃ g, Net F a b g 0 ∧ k = fun x y => algebraMap F L (g x y)) ∨
    ∃ v, Net F (.pair a R.wire) (.pair b R.wire) (R.lifted k) v ∧
      v + R.cost ≤ 9 * R.cost * m

variable {R}

private theorem Chain.pre {f : Val a → Val b} {k : Val b → Val c → L}
    (h : R.Chain b c k m) (hf : Rewire a b f) : R.Chain a c (fun x y => k (f x) y) m := by
  rcases h with ⟨g, hg, rfl⟩ | ⟨v, hv, hbound⟩
  · exact .inl ⟨_, hg.pre hf, rfl⟩
  · exact .inr ⟨v, hv.pre (hf.par (.id _)), hbound⟩

private theorem Chain.post {f : Val c → Val b} {k : Val a → Val b → L}
    (h : R.Chain a b k m) (hf : Rewire c b f) : R.Chain a c (fun x y => k x (f y)) m := by
  rcases h with ⟨g, hg, rfl⟩ | ⟨v, hv, hbound⟩
  · exact .inl ⟨_, hg.post hf, rfl⟩
  · exact .inr ⟨v, hv.post (hf.par (.id _)), hbound⟩

private theorem swapTail (a b c : Wire) :
    Rewire (.pair (.pair a b) c) (.pair (.pair a c) b)
      (fun x => ((x.1.1, x.2), x.1.2)) :=
  (Rewire.assoc a b c).comp (((Rewire.id a).par (.swap b c)).comp (.assoc' _ _ _))

private theorem Chain.trace {k : Val (.pair a c) → Val (.pair b c) → L}
    (h : R.Chain (.pair a c) (.pair b c) k m) :
    R.Chain a b (fun x y => ∑ z : Val c, k (x, z) (y, z)) m := by
  rcases h with ⟨g, hg, rfl⟩ | ⟨v, hv, hbound⟩
  · exact .inl ⟨_, hg.trace, by simp only [map_sum]⟩
  · refine .inr ⟨v, ?_, hbound⟩
    unfold lifted
    simpa only [lifted, map_sum, Matrix.sum_apply] using
      ((hv.pre (swapTail a R.wire c)).post (swapTail b R.wire c)).trace

private theorem Chain.par {k : Val a → Val b → L} {l : Val c → Val d → L}
    (h : R.Chain a b k m) (i : R.Chain c d l n) :
    R.Chain (.pair a c) (.pair b d) (fun x y => k x.1 y.1 * l x.2 y.2) (m + n) := by
  rcases h with ⟨g, hg, rfl⟩ | ⟨u, hu, hbound⟩ <;>
    rcases i with ⟨f, hf, rfl⟩ | ⟨v, hv, ibound⟩
  · exact .inl ⟨_, hg.par hf, by simp only [map_mul]⟩
  · refine .inr ⟨0 + v, ?_, by rw [mul_add]; omega⟩
    unfold lifted
    simpa only [lifted, ← Algebra.smul_def, map_smul, Matrix.smul_apply, smul_eq_mul] using
      ((hg.par hv).pre (.assoc a c R.wire)).post (.assoc b d R.wire)
  · refine .inr ⟨u + 0, ?_, by rw [mul_add]; omega⟩
    have aux (s : L) (t : F) (x y : Val R.wire) :
        R.M (s * algebraMap F L t) x y = R.M s x y * t := by
      rw [mul_comm, ← Algebra.smul_def, map_smul, Matrix.smul_apply, smul_eq_mul, mul_comm]
    unfold lifted
    simpa only [lifted, aux] using
      ((hu.par hf).pre (swapTail a c R.wire)).post (swapTail b d R.wire)
  · refine .inr ⟨u + v, ?_, by rw [mul_add]; omega⟩
    let i := R.wire
    have left (p q : Wire) := (Rewire.assoc (.pair p q) i i).comp (.middle p q i i)
    have right := (swapTail (.pair b d) i i).comp (left b d)
    unfold lifted
    simpa only [lifted, R.mul, Matrix.mul_apply] using
      (((hu.par hv).pre (left a c)).post right).trace

variable (R)

private theorem chain {k : Val a → Val b → L} (h : Net L a b k m) : R.Chain a b k m := by
  induction h with
  | empty => exact .inl ⟨_, .empty, by simp⟩
  | table a b k hk =>
    obtain ⟨v, hv, hb⟩ := Net.dense (.pair a R.wire) (.pair b R.wire) (R.lifted k)
    refine .inr ⟨v, hv, ?_⟩
    have ht : v ≤ 8 * R.cost := calc
      v ≤ 8 * 2 ^ (3 + (wd R.wire + wd R.wire)) := hb.trans (by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_right (by decide)
        simp only [wd]
        omega)
      _ = 8 * R.cost := by rw [pow_add]; rfl
    omega
  | par _ _ h i => exact h.par i
  | comp _ _ h i => exact ((h.par i).post (.swap _ _)).trace
  | trace _ h => exact h.trace
  | pre _ hf h => exact h.pre hf
  | post _ hf h => exact h.post hf

private theorem descend {k : Val a → Val b → F}
    (h : Net L a b (fun x y => algebraMap F L (k x y)) m) :
    ∃ v, Net F a b k v ∧ v ≤ 9 * R.cost * m := by
  rcases R.chain h with ⟨g, hg, he⟩ | ⟨v, hv, hb⟩
  · have : k = g := funext fun x => funext fun y =>
      (algebraMap F L).injective (congrFun (congrFun he x) y)
    exact ⟨0, this.symm ▸ hg, Nat.zero_le _⟩
  · obtain ⟨p, hp, hp'⟩ := Net.dense R.wire R.wire
      (fun x y => if x = R.root ∧ y = R.root then (1 : F) else 0)
    refine ⟨v + p, ?_, (Nat.add_le_add_left hp' v).trans hb⟩
    have g := ((hv.par hp).post (swapTail b R.wire R.wire)).trace.trace
    simpa only [lifted, ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, R.scalar] using g

private theorem cost_le : R.cost ≤ 32 * Module.finrank F L ^ 2 := by
  unfold cost
  rw [pow_add]
  calc
    _ ≤ 8 * ((2 * Module.finrank F L) * (2 * Module.finrank F L)) :=
      Nat.mul_le_mul_left 8 (Nat.mul_le_mul R.width R.width)
    _ = _ := by ring

end Representation

/-- A trivalent network of ground-field values descends without changing any
exterior positions. The bound counts vertices and also holds when both sides
count the common exterior arity. -/
theorem Net.descend [Module.Finite F L] {k : Val a → Val b → F}
    (h : Net L a b (fun x y => algebraMap F L (k x y)) m) :
    ∃ v, Net F a b k v ∧ v ≤ 288 * Module.finrank F L ^ 2 * m := by
  obtain ⟨R⟩ := exists_representation F L
  obtain ⟨v, hv, hb⟩ := R.descend h
  refine ⟨v, hv, hb.trans ?_⟩
  calc
    _ ≤ 9 * (32 * Module.finrank F L ^ 2) * m :=
      Nat.mul_le_mul_right m (Nat.mul_le_mul_left 9 R.cost_le)
    _ = _ := by ring

end OAI.LinearAlgebra.MatrixExponent
end
