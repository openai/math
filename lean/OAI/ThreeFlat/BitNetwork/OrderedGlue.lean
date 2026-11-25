import OAI.ThreeFlat.BitNetwork
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace OAI
/-! # Joining addressed networks in memory order

Allocate the shared bits first, then the private bits of each component in
component order. Copy the component table records in the same order. The
library table referenced by a record is unchanged by resolving its pointers.
-/

namespace ThreeFlat.BitNetwork.Ordered

open scoped BigOperators

variable {F : Type*} {m p h : ℕ} {arity : Fin m → ℕ}
variable (N : (i : Fin m) → BitNetwork F (arity i))
variable (wire : (i : Fin m) → Fin (arity i) → BitSource h p)

abbrev Row := (i : Fin m) × Fin (N i).cells
abbrev Private := (i : Fin m) × Fin (N i).internal

/-- Public intermediate bits use the initial segment. Every local private bit
has offset `h + sum of private widths of the preceding components`. -/
def privateEquiv : Fin h ⊕ Private N ≃ Fin (h + ∑ i, (N i).internal) :=
  (Equiv.sumCongr (Equiv.refl _) finSigmaFinEquiv).trans finSumFinEquiv

def resolve (i : Fin m) : BitSource (N i).internal (arity i) → BitSource (h + ∑ j, (N j).internal) p
  | .constant b => .constant b
  | .hidden j => .hidden (privateEquiv N (.inr ⟨i,j⟩))
  | .pin j => match wire i j with
    | .constant b => .constant b
    | .hidden k => .hidden (privateEquiv N (.inl k))
    | .pin k => .pin k

/-- Concatenate resolved trivalent records in their original memory order. -/
def glue : BitNetwork F p where
  internal := h + ∑ i, (N i).internal
  cells := ∑ i, (N i).cells
  source a k := let c : Row N := finSigmaFinEquiv.symm a
                resolve N wire c.1 ((N c.1).source c.2 k)
  table a := let c : Row N := finSigmaFinEquiv.symm a
             (N c.1).table c.2

@[simp] theorem table_at (c : Row N) :
    (glue N wire).table (finSigmaFinEquiv c) = (N c.1).table c.2 := by
  let f (a : Row N) := (N a.1).table a.2
  exact congrArg f (finSigmaFinEquiv.symm_apply_apply c)

@[simp] theorem source_at (c : Row N) (k : Fin 3) :
    (glue N wire).source (finSigmaFinEquiv c) k = resolve N wire c.1 ((N c.1).source c.2 k) := by
  let f (a : Row N) := resolve N wire a.1 ((N a.1).source a.2 k)
  exact congrArg f (finSigmaFinEquiv.symm_apply_apply c)

/-- Natural address of a record, for emitting it directly into a flat buffer. -/
theorem row_offset (c : Row N) : (finSigmaFinEquiv c).val =
    (∑ j : Fin c.1.val, (N (Fin.castLE c.1.isLt.le j)).cells) + c.2.val :=
  finSigmaFinEquiv_apply c

/-- Natural address of a private bit when a child address is resolved. -/
theorem private_offset (c : Private N) : (privateEquiv (h := h) N (.inr c)).val =
    h + ((∑ j : Fin c.1.val, (N (Fin.castLE c.1.isLt.le j)).internal) + c.2.val) := by
  change h + (finSigmaFinEquiv c).val = _
  rw [finSigmaFinEquiv_apply]

private def pack (a : Fin h → Bool) (b : ∀ i, Fin (N i).internal → Bool)
    (k : Fin (h + ∑ i, (N i).internal)) : Bool :=
  match (privateEquiv (h := h) N).symm k with
  | .inl j => a j
  | .inr c => b c.1 c.2

private def witnessEquiv :
    ((Fin h → Bool) × ((i : Fin m) → Fin (N i).internal → Bool)) ≃
      (Fin (h + ∑ i, (N i).internal) → Bool) where
  toFun z := pack N z.1 z.2
  invFun f := ⟨fun j => f (privateEquiv N (.inl j)),
    fun i j => f (privateEquiv N (.inr ⟨i,j⟩))⟩
  left_inv x := by ext <;> simp [pack]
  right_inv f := by
    funext k
    obtain ⟨y, rfl⟩ := (privateEquiv (h := h) N).surjective k
    cases y <;> simp [pack]

private theorem read_resolve (pin : Fin p → Bool) (a : Fin h → Bool)
    (b : ∀ i, Fin (N i).internal → Bool) (i) (s : BitSource (N i).internal (arity i)) :
    (resolve N wire i s).read (pack N a b) pin =
    s.read (b i) (fun j => (wire i j).read a pin) := by
  cases s with
  | constant _ => rfl
  | hidden _ => simp [resolve, BitSource.read, pack]
  | pin j =>
    simp only [resolve, BitSource.read]
    cases wire i j <;> simp [pack]

private theorem glue_weight [CommMonoid F] (pin : Fin p → Bool) (a : Fin h → Bool)
    (b : ∀ i, Fin (N i).internal → Bool) :
    (glue N wire).weight pin (pack N a b) =
      ∏ i, (N i).weight (fun j => (wire i j).read a pin) (b i) := by
  unfold weight
  rw [← Fintype.prod_sigma' (fun i j => (N i).factor (fun t => (wire i t).read a pin) (b i) j)]
  symm
  apply Fintype.prod_equiv finSigmaFinEquiv
  intro c
  simp only [factor, source_at, table_at]
  apply congrArg ((N c.1).table c.2)
  funext j
  exact (read_resolve N wire pin a b c.1 ((N c.1).source c.2 j)).symm

/-- Multiplying local contractions and summing the shared bits gives the
partition function of the one flat, densely addressed descriptor. -/
theorem glue_eval [CommSemiring F] (pin : Fin p → Bool) :
    (glue N wire).eval pin = ∑ a : Fin h → Bool,
      ∏ i, (N i).eval (fun j => (wire i j).read a pin) := by
  classical
  simp only [eval, Fintype.prod_sum]
  rw [← Fintype.sum_prod_type']
  symm
  apply Fintype.sum_equiv (witnessEquiv (h := h) N)
  intro z
  exact (glue_weight N wire pin z.1 z.2).symm

end ThreeFlat.BitNetwork.Ordered

end OAI
