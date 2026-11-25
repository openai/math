import OAI.Hierarchy.BinaryTreeTablePorts

namespace OAI
/-! # Messages for the binary-tree contraction

An incoming color chooses one of the outputs of a subtree. A fork sums over
the two colors sent to the children and reads its own table entry once per pair.
-/

namespace Hierarchy.BinaryTree
open MvPolynomial
open scoped BigOperators Classical
noncomputable section

inductive MessageTree (σ : Type) (q : ℕ) : ℕ → Type where
  | leaf (label : Fin q → σ) : MessageTree σ q 0
  | fork {h : ℕ} (label : Fin q → Fin q → Fin q → σ)
      (l r : MessageTree σ q h) : MessageTree σ q (h+1)

namespace MessageTree
variable {σ : Type} {q : ℕ}

def eval (F : Type*) [CommSemiring F] : {h : ℕ} → MessageTree σ q h → Fin q → MvPolynomial σ F
  | _, .leaf label, a => X (label a)
  | _, .fork label l r, a =>
    ∑ i, ∑ j, X (label a i j) * l.eval F i * r.eval F j

end MessageTree

private abbrev Tables (σ : Type) (q h : ℕ) :=
  (v : V h) → (Port h v → Fin q) → σ

private def childTables {σ : Type} {q h : ℕ} (T : Tables σ q (h+1)) (c : Bool) :
    Tables σ q h :=
  fun v z => T (child c v) (z ∘ childPort c v)

private def ofTables {σ : Type} {q : ℕ} :
    (h : ℕ) → Tables σ q h → MessageTree σ q h
  | 0, T => .leaf (fun a => T (root 0) (fun _ => a))
  | h+1, T => .fork (fun a i j => T (root (h+1)) (rootColors a i j))
      (ofTables h (childTables T false)) (ofTables h (childTables T true))

private def weight {σ : Type} {q h : ℕ} (F : Type*) [CommSemiring F] (T : Tables σ q h)
    (a : Fin q) (z : E h → Fin q) : MvPolynomial σ F :=
  ∏ v, X (T v (point z a v))

private theorem weight_glue {σ : Type} {q h : ℕ} (F : Type*) [CommSemiring F]
    (T : Tables σ q (h+1)) (a i j : Fin q) (l r : E h → Fin q) :
    weight F T a (glueColor i j l r) =
      X (T (root (h+1)) (rootColors a i j)) * weight F (childTables T false) i l *
        weight F (childTables T true) j r := by
  rw [weight, prod_vertex_split]
  simp only [weight, childTables, point_glue_root, point_glue_false, point_glue_true]

private theorem eval_ofTables {σ : Type} {q : ℕ} (F : Type*) [CommSemiring F] :
    ∀ (h : ℕ) (T : Tables σ q h) (a : Fin q),
      (ofTables h T).eval F a = ∑ z, weight F T a z := by
  intro h
  induction h with
  | zero =>
    intro T a
    let : Unique (E 0 → Fin q) := inferInstanceAs (Unique (Empty → Fin q))
    let : Unique (V 0) := inferInstanceAs (Unique Unit)
    rw [Fintype.sum_unique, weight, Fintype.prod_unique]
    change X (R := F) (T (root 0) (fun _ => a)) = X (T (root 0) (point _ a (root 0)))
    rw [point_leaf]
  | succ h ih =>
    intro T a
    rw [sum_color_split]
    simp only [ofTables, MessageTree.eval, weight_glue]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [ih, ih]
    rw [Finset.mul_sum (a := X (R := F) (T (root (h+1)) (rootColors a i j))), Finset.sum_mul]
    simp_rw [Finset.mul_sum]

/-- The ordinary contraction, with its independent variable at every local assignment,
is one output of a binary message computation. At the root its extra incoming color
is ignored. -/
theorem realizes_contraction (F : Type*) [CommSemiring F] (h q : ℕ) (hq : 0 < q) :
    ∃ t : MessageTree ((graph h).TableVar q) q h, ∃ i : Fin q,
      t.eval F i = (graph h).contraction F q := by
  let T : Tables ((graph h).TableVar q) q h :=
    fun v z => ⟨v, fun e => z (.inl e)⟩
  let i : Fin q := ⟨0, hq⟩
  exact ⟨ofTables h T, i, eval_ofTables F h T i⟩

end
end Hierarchy.BinaryTree

end OAI
