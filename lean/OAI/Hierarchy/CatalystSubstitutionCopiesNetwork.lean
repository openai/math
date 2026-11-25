import OAI.Hierarchy.CorrectionBatch

namespace OAI
/-! # Physical independent copies of a pointwise approximation

Each row has its own data and its own catalyst endpoints. Regrouping the
endpoints by direction preserves their sites and the full exposed size.
-/

noncomputable section
namespace Hierarchy.CatalystSubstitution
open ThreeFlat Routing Catalyst CorrectionFrame
open scoped BigOperators Classical

variable {F : Type*} [Field F] {k p : ℕ}

private def rowWire {d : ℕ} {P : Type} (i : Fin d) (v : P) : (Fin d × P) ⊕ Empty := .inl (i,v)

private def rowBank (d : ℕ) (X : Approximation F k p) :
    BitNetwork F (Fintype.card (Fin d × Port p X.width)) :=
  TypedWiring.glue (port:=fun _ : Fin d => Port p X.width) (fun _ => X.network) rowWire

/-- No hidden bits or tables connect different copies. -/
abbrev copies (d : ℕ) (X : Approximation F k p) : Approximation F k (d*p) :=
  ⟨copiesWidth d X.width,(CorrectionBatch.package X.width (rowBank d X)).network⟩

theorem copies_coeff (d : ℕ) (X : Approximation F k p)
    (x : Port (d*p) (copiesWidth d X.width) → Bool) :
    (copies d X).coeff x = ∏ i : Fin d, X.coeff (fun j => x (copiesPortEquiv d X.width (i,j))) := by
  refine (CorrectionBatch.coeff_package X.width (rowBank d X) x).trans ?_
  rw [rowBank, TypedWiring.glue_value, Fintype.sum_unique]; rfl

omit [Field F] in
theorem copies_size (d : ℕ) (X : Approximation F k p) : (copies d X).size = d*X.size := by
  refine (CorrectionBatch.size_package X.width (rowBank d X)).trans ?_
  simp only [rowBank, TypedWiring.glue_cells, TypedWiring.glue_internal, Fintype.card_empty,
    zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Approximation.size, Nat.mul_add, Nat.cast_id]

/-- Catalyst-only part of the batch numbering, retaining both signs. -/
def copiesWirePorts (d : ℕ) (b : Fin k → ℕ) :
    (Fin d × (Wire b × Bool)) ≃ (Wire (copiesWidth d b) × Bool) where
  toFun
    | (i,⟨j,t⟩,s) => (⟨j,finProdFinEquiv (i,t)⟩,s)
  invFun
    | (⟨j,t⟩,s) =>
      let a : Fin d × Fin (b j) := finProdFinEquiv.symm t
      (a.1,⟨j,a.2⟩,s)
  left_inv := by
    rintro ⟨i,⟨j,t⟩,s⟩
    simp
  right_inv := by
    rintro ⟨⟨j,t⟩,s⟩
    exact congrArg (fun n => ((⟨j,n⟩ : Wire (copiesWidth d b)),s))
      ((finProdFinEquiv (m:=d) (n:=b j)).apply_symm_apply t)

theorem copiesWirePorts_location {d : ℕ} (b : Fin k → ℕ) (i : Fin d × (Wire b × Bool)) :
    location (p:=d*p) (b:=copiesWidth d b) (.inr (copiesWirePorts d b i)) =
      location (p:=p) (b:=b) (.inr i.2) := by
  rcases i with ⟨i,⟨j,t⟩,s⟩
  rfl

private theorem row_read {d : ℕ} (b : Fin k → ℕ) (a : Fin (d*p) → Bool)
    (x : Wire (copiesWidth d b) × Bool → Bool) (i : Fin d) :
    (fun j => Sum.elim a x (copiesPortEquiv d b (i,j))) =
      Sum.elim (fun t => a (finProdFinEquiv (i,t))) (fun w => x (copiesWirePorts d b (i,w))) := by
  funext j
  rcases j with t | ⟨⟨j,t⟩,s⟩ <;> rfl

/-- With all data pinned, the batch error is the difference between its two
independent products on the same packed catalyst legs. -/
theorem copies_pinned (d : ℕ) (X : Approximation F k p) (f : (Fin p → Bool) → F)
    (a : Fin (d*p) → Bool) (x : Wire (copiesWidth d X.width) × Bool → Bool) :
    ((copies d X).pinnedError (dataProduct d f) a).coeff x =
      (∏ i : Fin d, X.coeff (Sum.elim (fun t => a (finProdFinEquiv (i,t)))
        (fun w => x (copiesWirePorts d X.width (i,w))))) -
      ∏ i : Fin d, ideal X.width f (Sum.elim (fun t => a (finProdFinEquiv (i,t)))
        (fun w => x (copiesWirePorts d X.width (i,w)))) := by
  change (copies d X).coeff (Sum.elim a x) - ideal (copiesWidth d X.width)
    (dataProduct d f) (Sum.elim a x) = _
  refine (congrArg₂ (· - ·) (copies_coeff d X (Sum.elim a x))
    (CorrectionBatch.ideal_power X.width f (Sum.elim a x))).trans ?_
  simp only [row_read]

theorem copies_pinned_rows (d : ℕ) (X : Approximation F k p) (f : (Fin p → Bool) → F)
    (a : Fin (d*p) → Bool) (x : Fin d × (Wire X.width × Bool) → Bool) :
    ((copies d X).pinnedError (dataProduct d f) a).coeff (x ∘ (copiesWirePorts d X.width).symm) =
      (∏ i : Fin d, X.coeff (Sum.elim (fun t => a (finProdFinEquiv (i,t))) (fun w => x (i,w)))) -
      ∏ i : Fin d, ideal X.width f (Sum.elim (fun t => a (finProdFinEquiv (i,t))) (fun w => x (i,w))) := by
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    copies_pinned d X f a (x ∘ (copiesWirePorts d X.width).symm)

end Hierarchy.CatalystSubstitution

end
end OAI
