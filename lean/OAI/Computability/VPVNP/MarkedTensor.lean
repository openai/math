import OAI.Computability.VPVNP.WireSpectrum

/-!
# Local operations on marked tensor indices

In Appendix A, the same coefficient table can place its marked indices at
different parties. Each party retains its background basis while receiving one
factor for each marked role assigned to it. These local operations describe
the arrays in the two orders of the exterior-algebra splitting identity.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

universe u v w r

variable {k : Type u} {J : Type v} {R : Type r}

/-- A table on the background bases and additional marked indices. -/
abbrev MarkedArray (k : Type*) (B : J → Type*) (I : R → Type*) :=
  ((j : J) → B j) → ((r : R) → I r) → k

/-- Place all marked indices while retaining the original background basis at
 each party. This applies when multiple roles have the same party. -/
noncomputable def placedWith [Fintype R] (B : J → Type*) [∀ j, Fintype (B j)]
    (I : R → Type*) [∀ r, Fintype (I r)] (place : R → J) (T : MarkedArray k B I) : Tensor k J where
  Basis j := B j × ((r : R) → j = place r → I r)
  finiteBasis _ := by classical exact inferInstance
  coeff x := T (fun j ↦ (x j).1) (fun r ↦ (x (place r)).2 r rfl)

/-- One marked index, keeping the background bases unchanged. -/
noncomputable def marked (B : J → Type*) [∀ j, Fintype (B j)]
    (I : Type*) [Fintype I] (a : J) (T : ((j : J) → B j) → I → k) : Tensor k J where
  Basis j := B j × (j = a → I)
  finiteBasis _ := by classical exact inferInstance
  coeff x := T (fun j ↦ (x j).1) ((x a).2 rfl)

/-- A complete assignment of local indices to a placed tensor is equivalently
an assignment of the background indices and one index per role. -/
def placedWithEquiv (B : J → Type*) (I : R → Type*) (place : R → J) :
    (((j : J) → B j) × ((r : R) → I r)) ≃ ((j : J) → B j × ((r : R) → j = place r → I r)) where
  toFun xy j := (xy.1 j, fun r _ ↦ xy.2 r)
  invFun x := (fun j ↦ (x j).1, fun r ↦ (x (place r)).2 r rfl)
  left_inv _ := rfl
  right_inv x := by
    funext j
    refine Prod.ext ?_ ?_
    · rfl
    funext r h
    subst j
    rfl

/-- Move one extra factor into party `a`'s local basis, carrying it there as a function on the
equality witness. -/
def markedEquiv (B : J → Type*) (I : Type*) (a : J) :
    (((j : J) → B j) × I) ≃ ((j : J) → B j × (j = a → I)) where
  toFun xy j := (xy.1 j, fun _ ↦ xy.2)
  invFun x := (fun j ↦ (x j).1, (x a).2 rfl)
  left_inv _ := rfl
  right_inv x := by
    funext j
    refine Prod.ext ?_ ?_
    · rfl
    funext h
    subst j
    rfl

/-- Regroup role-indexed factors by their assigned parties, with one factor for each role
placed at a given party. -/
def placedEquiv (I : R → Type*) (place : R → J) :
    ((r : R) → I r) ≃ ((j : J) → (r : R) → j = place r → I r) where
  toFun x _ r _ := x r
  invFun x r := x (place r) r rfl
  left_inv _ := rfl
  right_inv x := by
    funext j r h
    subst j
    rfl

/-- Identity matrix on the background and new marked indices, and a local
pairing between the old marked index of the tensor and that of an operator. -/
theorem contract_marked_operator [Fintype J] [Fintype R] [CommSemiring k]
    (B : J → Type*) [∀ j, Fintype (B j)] (I : R → Type w) [∀ r, Fintype (I r)]
    (K : Type w) [Fintype K] (a : J) (place : R → J)
    (T : ((j : J) → B j) → K → k) (A : ((r : R) → I r) → K → k) :
    Restricts (tensorProduct (marked B K a T)
      (placedTensor (fun e ↦ e.elim a place) (cutBasis I K) (fun z ↦ A (fun r ↦ z (some r)) (z none))))
      (placedWith B I place (fun b y ↦ ∑ i, T b i * A y i)) := by
  classical
  let L (j : J) (out : B j × ((r : R) → j = place r → I r))
      (p : (B j × (j = a → K)) × ((e : Option R) → j = e.elim a place → cutBasis I K e)) : k :=
    if out.1 = p.1.1 ∧ (∀ r (h : j = place r), out.2 r h = p.2 (some r) h) ∧
      (∀ h : j = a, p.1.2 h = p.2 none h) then 1 else 0
  refine ⟨L, ?_⟩
  funext out
  let e₁ := markedEquiv B K a
  let e₂ := placedEquiv (cutBasis I K) (fun e ↦ e.elim a place)
  let e₃ : (K × ((r : R) → I r)) ≃ ((e : Option R) → cutBasis I K e) :=
    { toFun := fun xy e ↦ match e with | none => xy.1 | some r => xy.2 r
      invFun := fun x ↦ (x none, fun r ↦ x (some r))
      left_inv := fun _ ↦ rfl
      right_inv := fun x ↦ by funext e; cases e <;> rfl }
  let Y := tensorProduct (marked B K a T)
    (placedTensor (fun e ↦ e.elim a place) (cutBasis I K)
      (fun z ↦ A (fun r ↦ z (some r)) (z none)))
  let ei : ((((j : J) → B j) × K) × (K × ((r : R) → I r))) ≃ ((j : J) → Y.Basis j) :=
    (e₁.prodCongr (e₃.trans e₂)).trans (Equiv.arrowProdEquivProdArrow J _ _).symm
  let f (x : (j : J) → Y.Basis j) := (∏ j, L j (out j) (x j)) * Y.coeff x
  calc
    _ = ∑ x : (j : J) → Y.Basis j, f x := rfl
    _ = ∑ xy, f (ei xy) := (ei.sum_comp f).symm
    _ = _ := ?_
  let bg := fun j ↦ (out j).1
  let vals := fun r ↦ (out (place r)).2 r rfl
  have hh (b : (j : J) → B j) (k₁ k₂ : K) (y : (r : R) → I r) :
      f (ei ((b,k₁),(k₂,y))) =
        (if bg = b ∧ vals = y ∧ k₁ = k₂ then 1 else 0) * (T b k₁ * A y k₂) := by
    dsimp only [f, Y, tensorProduct, marked, placedTensor, L, ei, e₁, e₂, e₃, Equiv.trans_apply, Equiv.prodCongr_apply,
      Equiv.arrowProdEquivProdArrow, Equiv.symm, Equiv.coe_fn_mk, markedEquiv, placedEquiv]
    rw [Fintype.prod_boole]
    congr 2
    apply propext
    change (∀ j, (out j).1 = b j ∧ (∀ r (h : j = place r), (out j).2 r h = y r) ∧
      (∀ _h : j = a, k₁ = k₂)) ↔ _
    constructor
    · intro h
      exact ⟨funext (fun j ↦ (h j).1), funext (fun r ↦ (h (place r)).2.1 r rfl), (h a).2.2 rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩ j
      refine ⟨rfl, ?_, fun _ ↦ rfl⟩
      intro r h
      subst j
      rfl
  simp_rw [Fintype.sum_prod_type]
  simp_rw [hh]
  simp [ite_mul, ite_and, bg, vals, placedWith]

end WireTensor

end VPVNP
end Computability
end OAI
