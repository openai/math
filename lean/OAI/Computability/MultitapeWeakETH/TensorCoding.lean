import OAI.Computability.MultitapeWeakETH.PinStar

/-! # Local tensor maps for endpoint coding over repeated uses -/

namespace OAI.Computability.MultitapeWeakETH

open VPVNP.WireTensor Finset
open scoped BigOperators Classical

variable {K J R : Type} [Field K] [Fintype J] [Fintype R]

/-- Applying a product of local maps to independent copies of a tensor
has the product of the one-copy coefficients, after regrouping by party. -/
theorem apply_copies (T : Tensor K J) {B : J → Type} (m : R → ∀ j, B j → T.Basis j → K)
    (x : (j : J) → R → B j) :
    applyLocal (fun j (c : R → B j) (s : R → T.Basis j) => ∏ r, m r j (c r) (s r))
      (tensorFamilyProduct (fun _ : R => T)).coeff x =
        ∏ r, applyLocal (m r) T.coeff (fun j => x j r) := by
  classical
  change (∑ s : (j : J) → R → T.Basis j,
    (∏ j, ∏ r, m r j (x j r) (s j r))*(∏ r, T.coeff (fun j => s j r))) =
      ∏ r, ∑ u, (∏ j, m r j (x j r) (u j))*T.coeff u
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (Equiv.piComm (fun j (_ : R) => T.Basis j))
  intro s
  rw [prod_comm,← prod_mul_distrib]
  rfl

/-- Pushing a pinned singleton through independent maps of the local basis
indices simply moves its support. It does not require injective color maps. -/
theorem pushforward_singleton {B C : J → Type} [∀ j, Fintype (B j)]
    (f : ∀ j, B j → C j) (s : ∀ j, B j) (c : K) :
    applyLocal (fun j b a => if f j a = b then (1:K) else 0)
      (fun x => if x = s then c else 0) =
      fun y => if (fun j => f j (s j)) = y then c else 0 := by
  classical
  funext y
  simp only [applyLocal,mul_ite,mul_zero,sum_ite_eq',mem_univ,ite_true]
  simp only [Fintype.prod_boole,← funext_iff,ite_mul,one_mul,zero_mul]

omit [Fintype J] in
/-- The root sums the diagonal assignments for independent equality wires.
This coefficient identity also applies when both endpoints lie at one party. -/
theorem sum_wire_basis {E : Type} [Fintype E] (a b : E → J) (B : E → Type)
    [∀ e, Fintype (B e)] (y : (j : J) → (wireNetwork (k := K) a b B).Basis j) :
    (∑ s : (e : E) → B e, if edgeAssignment a b s = y then (1:K) else 0) =
      (wireNetwork a b B).coeff y := by
  classical
  let s (e : E) := (y (a e)).1 e rfl
  have unique (v : (e : E) → B e) (h : edgeAssignment a b v = y) : v = s := by
    funext e
    exact congrArg (fun u => (u (a e)).1 e rfl) h
  have diag : (edgeAssignment a b s = y) ↔ ∀ e, (y (a e)).1 e rfl = (y (b e)).2 e rfl := by
    constructor
    · intro eq e
      exact congrArg (fun u => (u (b e)).2 e rfl) eq
    · intro h
      funext j
      apply Prod.ext
      · funext e hje
        subst j; rfl
      · funext e hje
        subst j; exact h e
  rw [sum_eq_single s]
  · simp only [wireNetwork,Fintype.prod_boole,diag]
  · intro v _ ne
    rw [ite_eq_right (fun eq => ne (unique v eq))]
  · simp

end OAI.Computability.MultitapeWeakETH
