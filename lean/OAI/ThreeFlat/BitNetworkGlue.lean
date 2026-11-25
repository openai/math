import OAI.ThreeFlat.BitNetwork
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Logic.Equiv.Prod

namespace OAI
/-! # Assembling weighted bit networks

Each component pin is wired to a global input bit, an extra shared summation bit,
or a constant. The component's internal indices remain private to that component.
-/

namespace ThreeFlat.BitNetwork

open scoped BigOperators
noncomputable section

variable {F I : Type*} [Fintype I] {arity : I → ℕ} {p h : ℕ}
variable (N : (i : I) → BitNetwork F (arity i))
variable (wire : (i : I) → Fin (arity i) → BitSource h p)

private abbrev Cell := (i : I) × Fin (N i).cells
private abbrev Hidden (h : ℕ) := Fin h ⊕ ((i : I) × Fin (N i).internal)

private def liftSource (i : I) (s : BitSource (N i).internal (arity i)) :
    BitSource (Fintype.card (Hidden N h)) p :=
  match s with
  | .constant b => .constant b
  | .hidden j => .hidden (Fintype.equivFin _ (Sum.inr ⟨i,j⟩))
  | .pin j => match wire i j with
    | .constant b => .constant b
    | .pin k => .pin k
    | .hidden k => .hidden (Fintype.equivFin _ (Sum.inl k))

/-- Simultaneous wiring of a finite family of networks. -/
def glue : BitNetwork F p where
  internal := Fintype.card (Hidden N h)
  cells := Fintype.card (Cell N)
  source a k := let c := (Fintype.equivFin (Cell N)).symm a
                liftSource N wire c.1 ((N c.1).source c.2 k)
  table a := let c := (Fintype.equivFin (Cell N)).symm a
             (N c.1).table c.2

@[simp] theorem glue_cells : (glue N wire).cells = ∑ i, (N i).cells := by
  simp [glue, Cell]

@[simp] theorem glue_internal : (glue N wire).internal = h + ∑ i, (N i).internal := by
  simp [glue, Hidden]

private def hiddenBits (a : Fin h → Bool) (b : ∀ i, Fin (N i).internal → Bool)
    (k : Fin (Fintype.card (Hidden N h))) : Bool :=
  match (Fintype.equivFin (Hidden N h)).symm k with
  | .inl j => a j
  | .inr t => b t.1 t.2

private def hiddenEquiv :
    ((Fin h → Bool) × ((i : I) → Fin (N i).internal → Bool)) ≃
      (Fin (Fintype.card (Hidden N h)) → Bool) where
  toFun z := hiddenBits N z.1 z.2
  invFun f := ⟨fun j => f (Fintype.equivFin _ (.inl j)),
    fun i j => f (Fintype.equivFin _ (.inr ⟨i,j⟩))⟩
  left_inv x := by
    ext <;> simp [hiddenBits]
  right_inv f := by
    funext k
    obtain ⟨y, rfl⟩ := (Fintype.equivFin (Hidden N h)).surjective k
    cases y <;> simp [hiddenBits]

private theorem read_liftSource (pin : Fin p → Bool) (a : Fin h → Bool)
    (b : ∀ i, Fin (N i).internal → Bool) (i) (s : BitSource (N i).internal (arity i)) :
    (liftSource N wire i s).read (hiddenBits N a b) pin =
    s.read (b i) (fun j => (wire i j).read a pin) := by
  cases s with
  | constant _ => rfl
  | hidden _ => simp [liftSource, BitSource.read, hiddenBits]
  | pin j =>
    simp only [liftSource, BitSource.read]
    cases wire i j <;> simp [hiddenBits]

variable [CommSemiring F]

private theorem glue_weight (pin : Fin p → Bool) (a : Fin h → Bool)
    (b : ∀ i, Fin (N i).internal → Bool) :
    (glue N wire).weight pin (hiddenBits N a b) =
      ∏ i, (N i).weight (fun j => (wire i j).read a pin) (b i) := by
  classical
  unfold weight
  rw [← Fintype.prod_sigma' (fun i j => (N i).factor (fun t => (wire i t).read a pin) (b i) j)]
  symm
  apply Fintype.prod_equiv (Fintype.equivFin (Cell N))
  intro c
  let f (d : Cell N) := (N d.1).factor (fun t => (wire d.1 t).read a pin) (b d.1) d.2
  simpa only [f, factor, glue, read_liftSource] using
    (congrArg f ((Fintype.equivFin (Cell N)).symm_apply_apply c)).symm

/-- The contraction sums global intermediate bits once and multiplies the
evaluated component tables. -/
theorem glue_eval (pin : Fin p → Bool) :
    (glue N wire).eval pin = ∑ a : Fin h → Bool,
      ∏ i, (N i).eval (fun j => (wire i j).read a pin) := by
  classical
  simp only [eval, Fintype.prod_sum]
  rw [← Fintype.sum_prod_type']
  symm
  apply Fintype.sum_equiv (hiddenEquiv (h := h) N)
  intro z
  exact (glue_weight N wire pin z.1 z.2).symm

end
end ThreeFlat.BitNetwork

end OAI
