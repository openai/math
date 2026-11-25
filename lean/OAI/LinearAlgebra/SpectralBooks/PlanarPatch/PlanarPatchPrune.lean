import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchPruneAlgebra

/-! # Trivalent pruning of ordered patch tensor trees

Rooting at a distinguished boundary stub orders the children at each vertex.
A scalar subtree can be summed out. A unary table can be composed with the
adjacent table. The surviving branches retain their left-to-right boundary
labels, with one trivalent vertex for each binary branch.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

variable {V K : Type*} [CommSemiring K] {d : V → ℕ}

/-- A rooted ordered tensor tree with a free output wire of dimension `q`.
Each named stub exposes an input index of dimension `d v`. -/
inductive OrderedTensorTree (K : Type*) {V : Type*} (d : V → ℕ) : ℕ → Type _
  | scalar {q} (v : Fin q → K) : OrderedTensorTree K d q
  | stub {q} (v : V) (M : LinTable K q (d v)) : OrderedTensorTree K d q
  | unary {q i} (M : LinTable K q i) (left : OrderedTensorTree K d i) : OrderedTensorTree K d q
  | branch {q i j} (B : TriTable K q i j) (left : OrderedTensorTree K d i)
      (right : OrderedTensorTree K d j) : OrderedTensorTree K d q

/-- A stub has no internal table. Every table in the normalized representation has
three ports, including the output port at the root. -/
inductive TrivalentTree (K : Type*) {V : Type*} (d : V → ℕ) : ℕ → Type _
  | port (v : V) : TrivalentTree K d (d v)
  | branch {q i j} (B : TriTable K q i j) (left : TrivalentTree K d i)
      (right : TrivalentTree K d j) : TrivalentTree K d q

def boundaryValue (x : ∀ v, Fin (d v)) (v : V) (i : Fin (d v)) : K :=
  if i = x v then 1 else 0

namespace OrderedTensorTree

def labels : {q : ℕ} → OrderedTensorTree K d q → List V
  | _, .scalar _ => []
  | _, .stub v _ => [v]
  | _, .unary _ t => t.labels
  | _, .branch _ t u => t.labels ++ u.labels

def eval (x : ∀ v, Fin (d v)) : {q : ℕ} → OrderedTensorTree K d q → Fin q → K
  | _, .scalar v => v
  | _, .stub v M => linEval M (boundaryValue x v)
  | _, .unary M t => linEval M (t.eval x)
  | _, .branch B t u => triEval B (t.eval x) (u.eval x)

/-- A common dimension cap on all edge and stub indices. -/
def Bounded (m : ℕ) : {q : ℕ} → OrderedTensorTree K d q → Prop
  | q, .scalar _ => q ≤ m
  | q, .stub v _ => q ≤ m ∧ d v ≤ m
  | q, .unary _ t => q ≤ m ∧ t.Bounded m
  | q, .branch _ t u => q ≤ m ∧ t.Bounded m ∧ u.Bounded m

end OrderedTensorTree

namespace TrivalentTree

def labels : {q : ℕ} → TrivalentTree K d q → List V
  | _, .port v => [v]
  | _, .branch _ t u => t.labels ++ u.labels

def eval (x : ∀ v, Fin (d v)) : {q : ℕ} → TrivalentTree K d q → Fin q → K
  | _, .port v => boundaryValue x v
  | _, .branch B t u => triEval B (t.eval x) (u.eval x)

def vertices : {q : ℕ} → TrivalentTree K d q → ℕ
  | _, .port _ => 0
  | _, .branch _ t u => t.vertices + u.vertices + 1

def Bounded (m : ℕ) : {q : ℕ} → TrivalentTree K d q → Prop
  | _, .port v => d v ≤ m
  | q, .branch _ t u => q ≤ m ∧ t.Bounded m ∧ u.Bounded m

omit [CommSemiring K] in
theorem vertices_add_one_eq_length {q : ℕ} (t : TrivalentTree K d q) :
    t.vertices + 1 = t.labels.length := by
  induction t with
  | port v => rfl
  | branch B t u ht hu => simp only [vertices, labels, List.length_append]; omega

end TrivalentTree

/-- Intermediate normalization with one unapplied matrix at the root. -/
inductive Pruned (K : Type*) {V : Type*} (d : V → ℕ) (q : ℕ) : Type _
  | scalar (v : Fin q → K) : Pruned K d q
  | tree {i} (M : LinTable K q i) (t : TrivalentTree K d i) : Pruned K d q

namespace Pruned

def labels {q : ℕ} : Pruned K d q → List V
  | .scalar _ => []
  | .tree _ t => t.labels

def eval {q : ℕ} (x : ∀ v, Fin (d v)) : Pruned K d q → Fin q → K
  | .scalar v => v
  | .tree M t => linEval M (t.eval x)

def Bounded {q : ℕ} (m : ℕ) : Pruned K d q → Prop
  | .scalar _ => True
  | .tree _ t => t.Bounded m

def post {q i : ℕ} (M : LinTable K q i) : Pruned K d i → Pruned K d q
  | .scalar v => .scalar (linEval M v)
  | .tree A t => .tree (linComp M A) t

def fuse {q i j : ℕ} (B : TriTable K q i j) : Pruned K d i → Pruned K d j → Pruned K d q
  | .scalar v, .scalar w => .scalar (triEval B v w)
  | .scalar v, .tree A u => .tree (linComp (triLeftScalar B v) A) u
  | .tree A t, .scalar w => .tree (linComp (triRightScalar B w) A) t
  | .tree A t, .tree D u => .tree (linId q) (.branch (triPrecomp B A D) t u)

theorem labels_post {q i : ℕ} (M : LinTable K q i) (t : Pruned K d i) :
    (post M t).labels = t.labels := by cases t <;> rfl

theorem labels_fuse {q i j : ℕ} (B : TriTable K q i j) (t : Pruned K d i) (u : Pruned K d j) :
    (fuse B t u).labels = t.labels ++ u.labels := by
  cases t <;> cases u <;> simp [fuse, labels, TrivalentTree.labels]

theorem eval_post {q i : ℕ} (x : ∀ v, Fin (d v)) (M : LinTable K q i) (t : Pruned K d i) :
    (post M t).eval x = linEval M (t.eval x) := by
  cases t <;> simp [post, eval, linEval_comp]

theorem eval_fuse {q i j : ℕ} (x : ∀ v, Fin (d v)) (B : TriTable K q i j)
    (t : Pruned K d i) (u : Pruned K d j) :
    (fuse B t u).eval x = triEval B (t.eval x) (u.eval x) := by
  cases t <;> cases u <;> simp [fuse, eval, TrivalentTree.eval, linEval_comp,
    linEval_id, triEval_leftScalar, triEval_rightScalar, triEval_precomp]

theorem bounded_post {q i m : ℕ} (M : LinTable K q i) (t : Pruned K d i) :
    t.Bounded m → (post M t).Bounded m := by cases t <;> exact id

theorem bounded_fuse {q i j m : ℕ} (B : TriTable K q i j) (t : Pruned K d i) (u : Pruned K d j)
    (hq : q ≤ m) : t.Bounded m → u.Bounded m → (fuse B t u).Bounded m := by
  cases t <;> cases u <;> simp [fuse, Bounded, TrivalentTree.Bounded, hq]
  exact And.intro

end Pruned

namespace OrderedTensorTree

def prune : {q : ℕ} → OrderedTensorTree K d q → Pruned K d q
  | _, .scalar v => .scalar v
  | _, .stub v M => .tree M (.port v)
  | _, .unary M t => Pruned.post M (prune t)
  | _, .branch B t u => Pruned.fuse B (prune t) (prune u)

theorem labels_prune {q : ℕ} (t : OrderedTensorTree K d q) : (prune t).labels = t.labels := by
  induction t with
  | scalar | stub => rfl
  | unary _ _ ih => exact (Pruned.labels_post ..).trans ih
  | branch _ _ _ ih jh => exact (Pruned.labels_fuse ..).trans (congrArg₂ _ ih jh)

theorem eval_prune {q : ℕ} (t : OrderedTensorTree K d q) (x : ∀ v, Fin (d v)) :
    (prune t).eval x = t.eval x := by
  induction t with
  | scalar | stub => rfl
  | unary _ _ ih => exact (Pruned.eval_post ..).trans (congrArg _ ih)
  | branch _ _ _ ih jh => exact (Pruned.eval_fuse ..).trans (congrArg₂ _ ih jh)

theorem bounded_prune {q m : ℕ} (t : OrderedTensorTree K d q) (h : t.Bounded m) :
    (prune t).Bounded m := by
  induction t with
  | scalar => trivial
  | stub v M => exact h.2
  | unary M t ih => exact Pruned.bounded_post _ _ (ih h.2)
  | branch B t u ih jh => exact Pruned.bounded_fuse _ _ _ h.1 (ih h.2.1) (jh h.2.2)

omit [CommSemiring K] in
theorem root_bounded {q m : ℕ} (t : OrderedTensorTree K d q) (h : t.Bounded m) : q ≤ m := by
  cases t with
  | scalar => exact h
  | _ => exact h.1

/-- Contract every inactive subtree and suppress every unary vertex. Including the
distinguished output stub, the number of trivalent vertices is the number of
boundary stubs minus two. The same boundary assignment works before and after pruning. -/
theorem trivalent_pruning {q m : ℕ} (t : OrderedTensorTree K d q)
    (h : t.Bounded m) (hports : 2 ≤ t.labels.length) :
    ∃ u : TrivalentTree K d q, u.labels = t.labels ∧ u.Bounded m ∧
      u.vertices + 2 = t.labels.length + 1 ∧ ∀ x, u.eval x = t.eval x := by
  have hl := t.labels_prune
  have he := t.eval_prune
  have hb := t.bounded_prune h
  cases ht : prune t with
  | scalar v =>
    rw [ht] at hl
    change [] = t.labels at hl
    simp [← hl] at hports
  | tree M u =>
    rw [ht] at hl hb
    cases u with
    | port v =>
      change [v] = t.labels at hl
      simp [← hl] at hports
    | branch B l r =>
      let v := TrivalentTree.branch (triPostcomp M B) l r
      have hv : v.labels = t.labels := hl
      refine ⟨v, hv, ⟨t.root_bounded h, hb.2⟩, ?_, ?_⟩
      · have := v.vertices_add_one_eq_length
        rw [hv] at this
        omega
      · intro x
        specialize he x
        rw [ht] at he
        exact (triEval_postcomp M B _ _).trans he

end OrderedTensorTree
end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
