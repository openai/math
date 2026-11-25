import OAI.Computability.VPVNP.CircuitComposition
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

namespace OAI
/-! # Straight-line programs for a binary-tree contraction

The entries in both child tables are existing gate references. Each triple of edge labels
contributes two multiplications and one addition to the new table.
-/

namespace Hierarchy.BinaryTree

open Computability.VPVNP
open scoped BigOperators
open private read_reindex run_append_left run_append_right
  from OAI.Computability.VPVNP.CircuitComposition
noncomputable section

variable {F σ I J : Type*} [CommRing F] {n m q : ℕ}

private abbrev value (p : Program F σ n) (r : Ref F σ n) :=
  (Circuit.mk p r).polynomial

/-- Place both child programs in one program, keeping each of their named outputs. -/
theorem joinTables (p : Program F σ n) (q : Program F σ m)
    (left : I → Ref F σ n) (right : J → Ref F σ m) :
    ∃ (l : I → Ref F σ (n + m)) (r : J → Ref F σ (n + m)),
      (∀ i, (Circuit.mk (p.append q) (l i)).polynomial = (Circuit.mk p (left i)).polynomial) ∧
      (∀ j, (Circuit.mk (p.append q) (r j)).polynomial = (Circuit.mk q (right j)).polynomial) := by
  refine ⟨fun i => (left i).reindex (Fin.castAdd m),
    fun j => (right j).reindex (Fin.natAdd n), ?_, ?_⟩
  · intro i
    simp only [Circuit.polynomial, Circuit.eval, read_reindex, run_append_left]
  · intro j
    simp only [Circuit.polynomial, Circuit.eval, read_reindex, run_append_right]

private theorem gate (p : Program F σ n) (op : BinOp) (a b : Ref F σ n) :
    ∃ (p' : Program F σ (n+1)) (lift : Ref F σ n → Ref F σ (n+1)) (out : Ref F σ (n+1)),
      (∀ i, value p' (lift i) = value p i) ∧
      value p' out = op.apply (value p a) (value p b) := by
  refine ⟨p.snoc op a b, fun i => i.reindex Fin.castSucc, .gate (Fin.last n), ?_, ?_⟩
  · intro i
    cases i with
    | const => rfl
    | var => rfl
    | gate j =>
      simp [value, Circuit.polynomial, Circuit.eval, Ref.reindex, Ref.read, Program.run]
  · simp [value, Circuit.polynomial, Circuit.eval, Ref.read, Program.run]

private theorem triple (p : Program F σ n) (x : σ) (l r acc : Ref F σ n) :
    ∃ (p' : Program F σ (n+3)) (lift : Ref F σ n → Ref F σ (n+3)) (out : Ref F σ (n+3)),
      (∀ i, value p' (lift i) = value p i) ∧
      value p' out = MvPolynomial.X x * value p l * value p r + value p acc := by
  obtain ⟨u,f,a,hu,ha⟩ := gate p .mul (.var x) l
  obtain ⟨v,g,b,hv,hb⟩ := gate u .mul a (f r)
  obtain ⟨z,k,c,hz,hc⟩ := gate v .add b (g (f acc))
  refine ⟨z, fun i => k (g (f i)), c, fun i => (hz _).trans ((hv _).trans (hu i)), ?_⟩
  change value u a = MvPolynomial.X x * value p l at ha
  change value v b = value u a * value u (f r) at hb
  change value z c = value v b + value v (g (f acc)) at hc
  rw [hc, hb, ha, hv, hu, hu]

private theorem messageTerms (p : Program F σ n) (l r : Fin q → Ref F σ n)
    (labels : Fin q → Fin q → σ) (terms : Finset (Fin q × Fin q)) :
    ∃ m ≤ n + 3 * terms.card,
      ∃ (z : Program F σ m) (lift : Ref F σ n → Ref F σ m) (acc : Ref F σ m),
      (∀ i, value z (lift i) = value p i) ∧ value z acc =
        ∑ ij ∈ terms, MvPolynomial.X (labels ij.1 ij.2) * value p (l ij.1) * value p (r ij.2) := by
  classical
  induction terms using Finset.induction_on with
  | empty =>
    refine ⟨n, by simp, p, id, .const 0, fun _ => rfl, ?_⟩
    change MvPolynomial.C (0 : F) = _
    simp
  | @insert a s ha ih =>
    obtain ⟨m, bound, z, f, acc, kept, sum⟩ := ih
    obtain ⟨z',g,last,kept',total⟩ := triple z (labels a.1 a.2) (f (l a.1)) (f (r a.2)) acc
    refine ⟨m+3, ?_, z', fun i => g (f i), last,
      fun i => (kept' _).trans (kept i), ?_⟩
    · rw [Finset.card_insert_of_notMem ha]
      omega
    · rw [Finset.sum_insert ha, total, kept, kept, sum]

private theorem messageRows (p : Program F σ n) (left right : Fin q → Ref F σ n)
    (labels : Fin q → Fin q → Fin q → σ) (colors : Finset (Fin q)) :
    ∃ m ≤ n + colors.card * (3 * q^2),
      ∃ (z : Program F σ m) (lift : Ref F σ n → Ref F σ m) (rows : Fin q → Ref F σ m),
      (∀ i, value z (lift i) = value p i) ∧
      ∀ a ∈ colors, value z (rows a) =
        ∑ i, ∑ j, MvPolynomial.X (labels a i j) * value p (left i) * value p (right j) := by
  classical
  induction colors using Finset.induction_on with
  | empty =>
    exact ⟨n, by simp, p, id, fun _ => .const 0, fun _ => rfl, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨m, bound, z, f, rows, kept, earlier⟩ := ih
    obtain ⟨k, charge, z', g, last, kept', total⟩ :=
      messageTerms z (fun i => f (left i)) (fun j => f (right j)) (labels a) Finset.univ
    refine ⟨k, ?_, z', fun i => g (f i), fun i => if i=a then last else g (rows i),
      fun i => (kept' _).trans (kept i), ?_⟩
    · simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at charge
      rw [Finset.card_insert_of_notMem ha, Nat.add_mul, one_mul, pow_two]
      rw [pow_two] at bound
      omega
    · intro i hi
      change value z' (if i=a then last else g (rows i)) = _
      by_cases eqn : i=a
      · subst i
        simpa [Fintype.sum_prod_type, kept] using total
      · rw [ite_eq_right eqn, kept']
        exact earlier _ ((Finset.mem_insert.mp hi).resolve_left eqn)

/-- Compute every entry of a parent table with at most three more gates per triple of labels,
independently of how many gates the two child tables already use. -/
theorem extendMessages (p : Program F σ n) (left right : Fin q → Ref F σ n)
    (labels : Fin q → Fin q → Fin q → σ) :
    ∃ m ≤ n + 3*q^3, ∃ (z : Program F σ m) (refs : Fin q → Ref F σ m),
      ∀ a, (Circuit.mk z (refs a)).polynomial =
        ∑ i, ∑ j, MvPolynomial.X (labels a i j) *
          (Circuit.mk p (left i)).polynomial * (Circuit.mk p (right j)).polynomial := by
  obtain ⟨m, bound, z, _, refs, _, reads⟩ := messageRows p left right labels Finset.univ
  refine ⟨m, ?_, z, refs, fun a => reads a (Finset.mem_univ a)⟩
  simpa only [Finset.card_univ, Fintype.card_fin, show q * (3*q^2) = 3*q^3 by ring] using bound


end
end Hierarchy.BinaryTree

end OAI
