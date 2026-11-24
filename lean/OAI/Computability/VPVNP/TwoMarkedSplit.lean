import OAI.Computability.VPVNP.TwoMarkedTransport
import OAI.Computability.VPVNP.ExteriorLevels

/-!
# Tensor nodes in the endpoint-coupling split

Appendix A.3 splits the first marked index while retaining the second.
The exterior column and row become background indices at the fixed endpoints,
so that a child is again a two-marked table with both marks free to move.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

open scoped Classical
open ExteriorLevels Lemmata.FockCircuits

universe u v

/-- A coefficient table with two movable indices and a finite background
basis at each party. The background may grow at successive splits. -/
structure TwoMarkedNode (k : Type u) (J : Type v) (I K : Type) where
  /-- Finite background basis at each party, separate from the two movable indices of the node. -/
  Basis : J → Type
  finiteBasis : ∀ j, Fintype (Basis j)
  /-- Tensor coefficients indexed by a background basis assignment and the two independently
  marked indices. -/
  coeff : ((j : J) → Basis j) → I → K → k

attribute [instance] TwoMarkedNode.finiteBasis

namespace TwoMarkedNode

variable {k : Type u} {J : Type v} {I K : Type} [Fintype I] [Fintype K]

/-- Place the two indices without moving any background index. -/
noncomputable def place (W : TwoMarkedNode k J I K) (a b : J) : Tensor k J :=
  twoMarked W.Basis I K W.coeff a b

/-- The root table is the identity on a pair of marked indices. -/
noncomputable def wire [Zero k] [One k] (q : ℕ) : TwoMarkedNode k J (Fin q) (Fin q) where
  Basis _ := Unit
  finiteBasis _ := inferInstance
  coeff _ i j := @ite k (i = j) (Classical.propDecidable _) 1 0

/-- Contract the old first index against the last argument of the operator.
Its column lives at `a₀`, its row at `a₁`, and the new first index can be
placed anywhere. -/
noncomputable def child [CommSemiring k] (W : TwoMarkedNode k J I K) (a₀ a₁ : J)
    {H : Type} [Fintype H] (operator : H → H → I → I → k) : TwoMarkedNode k J I K where
  Basis j := W.Basis j × (j = a₀ → H) × (j = a₁ → H)
  finiteBasis _ := inferInstance
  coeff x i l := ∑ j, W.coeff (fun p => (x p).1) j l *
    operator ((x a₁).2.2 rfl) ((x a₀).2.1 rfl) i j

/-- `true` chooses contraction after creation. The intermediate level is
one higher on that branch and one lower on the `false` branch. -/
noncomputable def exteriorOperator [CommRing k] {q : ℕ} (b : ℕ) (branch : Bool)
    (β α : Level q b) (i j : Fin q) : k :=
  if branch then
    ∑ γ : Level q (b+1), entry k (Fock.contract k j) β γ * entry k (Fock.create k i) γ α
  else
    ∑ γ : Level q (b-1), entry k (Fock.create k i) β γ * entry k (Fock.contract k j) γ α

/-- One exterior split in the binary tree of Appendix A.3. -/
noncomputable def exteriorChild [CommRing k] {q : ℕ} (W : TwoMarkedNode k J (Fin q) K)
    (a₀ a₁ : J) (b : ℕ) (branch : Bool) : TwoMarkedNode k J (Fin q) K :=
  W.child a₀ a₁ (exteriorOperator b branch)

variable [Fintype J] [Field k]

theorem value_wire (F : SpectralPoint k J) (q : ℕ) (a b : J) :
    F.value ((wire q).place a b) = F.value (WireTensor.wire a b (Fin q)) :=
  F.value_eq_of_mutual (twoMarked_wire_mutual (k := k) (Fin q) a b)

/-- At each placement the sum of the two child arrays represents the parent
times the identity wire on the exterior level. -/
theorem value_exterior_split {q : ℕ} (F : SpectralPoint k J) (W : TwoMarkedNode k J (Fin q) K)
    (a₀ a₁ x y : J) (b : ℕ) :
    F.value (W.place x y) * F.value (WireTensor.wire a₀ a₁ (Level q b)) ≤
      F.value ((W.exteriorChild a₀ a₁ b true).place x y) +
      F.value ((W.exteriorChild a₀ a₁ b false).place x y) := by
  let P := (W.exteriorChild a₀ a₁ b true).place x y
  let M := (W.exteriorChild a₀ a₁ b false).place x y
  let Z := Tensor.mk P.Basis P.finiteBasis (fun z => P.coeff z + M.coeff z)
  let U := tensorProduct (W.place x y) (WireTensor.wire a₀ a₁ (Level q b))
  let e (j : J) : Z.Basis j ≃ U.Basis j :=
    { toFun z := ((z.1.1, z.2), z.1.2)
      invFun z := ((z.1.1, z.2), z.1.2)
      left_inv _ := rfl
      right_inv _ := rfl }
  have h : Restricts U Z ∧ Restricts Z U := by
    apply restricts_of_reindex e
    intro z
    let α := (z a₀).1.2.1 rfl
    let β := (z a₁).1.2.2 rfl
    let i := (z x).2.1 rfl
    let t (j : Fin q) := W.coeff (fun p => (z p).1.1) j ((z y).2.2 rfl)
    change (∑ j, t j * exteriorOperator b true β α i j) +
      (∑ j, t j * exteriorOperator b false β α i j) =
      t i * (@ite k (α = β) (Classical.propDecidable _) 1 0)
    simp only [exteriorOperator, ↓reduceIte, Bool.false_eq_true]
    rw [matrix_car_apply]
    by_cases h : α = β <;> simp [h, eq_comm]
  rw [← F.value_tensorProduct, F.value_eq_of_mutual h]
  exact F.value_add_le (B := P.Basis) P.coeff M.coeff

end TwoMarkedNode
end WireTensor

end VPVNP
end Computability
end OAI
