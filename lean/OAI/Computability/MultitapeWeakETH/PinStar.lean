import OAI.Computability.MultitapeWeakETH.Pins
import OAI.Computability.VPVNP.WireSpectrum

/-! # Implementing the pin stream source as a star of equality wires -/

namespace OAI.Computability.MultitapeWeakETH

open VPVNP.WireTensor Finset
open scoped BigOperators Classical

variable {K J : Type} [Field K] [Fintype J]

/-- A common root sends a possibly different pin index down each spoke.
The maps at every party depend only on its incoming pin and its own tensor
index. The root is allowed to carry an ordinary tensor factor as well. -/
theorem pin_star_restriction (T : Tensor K J) (root : J) (Pin B : J → Type)
    [∀ j, Fintype (Pin j)] [∀ j, Fintype (B j)]
    (weight : ((j : J) → Pin j) → K) (maps : ∀ j, Pin j → B j → T.Basis j → K) :
    Restricts (tensorProduct T (wireNetwork (fun _ : J => root) id Pin))
      (⟨B,inferInstance,fun x => ∑ p, weight p * applyLocal (fun j => maps j (p j)) T.coeff x⟩ :
        Tensor K J) := by
  classical
  let a (_ : J) := root
  let b : J → J := id
  let star := wireNetwork (k := K) a b Pin
  let select (j : J) (x : B j) (s : T.Basis j) (wire : star.Basis j) :=
    (if h : j = root then weight (fun i => wire.1 i h) else 1) * maps j (wire.2 j rfl) x s
  refine ⟨fun j x sw => select j x sw.1 sw.2,?_⟩
  funext x
  let term (s : ∀ j, T.Basis j) (w : ∀ j, star.Basis j) :=
    ((∏ j, select j (x j) (s j) (w j))*star.coeff w)*T.coeff s
  change (∑ sw : (j : J) → T.Basis j × star.Basis j,
    (∏ j, select j (x j) (sw j).1 (sw j).2) *
      (T.coeff (fun j => (sw j).1)*star.coeff (fun j => (sw j).2))) = _
  calc
    _ = ∑ sw : ((j : J) → T.Basis j) × ((j : J) → star.Basis j), term sw.1 sw.2 := by
      apply Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow J T.Basis star.Basis)
      intro sw
      dsimp only [term,Equiv.arrowProdEquivProdArrow,Equiv.coe_fn_mk]
      ring
    _ = ∑ s, (∑ p : (j : J) → Pin j, weight p * ∏ j, maps j (p j) (x j) (s j)) * T.coeff s := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro s _
      simp only [term,← sum_mul]
      congr 1
      change applyLocal (fun j z w => select j z (s j) w) star.coeff x = _
      rw [applyLocal_wireNetwork a b Pin]
      apply sum_congr rfl
      intro p _
      simp only [select,edgeAssignment,prod_mul_distrib]
      congr 1
      rw [prod_eq_single root] <;> simp_all
    _ = _ := by
      change _ = ∑ p, weight p*(∑ s, (∏ j, maps j (p j) (x j) (s j))*T.coeff s)
      simp only [sum_mul,mul_sum,mul_assoc]
      exact sum_comm

end OAI.Computability.MultitapeWeakETH
