import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchGluing
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchTreeTables
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchPrune
import Mathlib.Data.List.Range

/-!
# Ordered tensor trees from a patch triangulation

Each vertex table is assigned to its outgoing side. The leaf on that side
exposes a physical port when the table has a free index. A triangle joins
its two child messages by matching the three pairs of corner states.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace PlanarPatch

variable {K V : Type*} [CommSemiring K] {d : V → ℕ}

/-- A corner table with its incident state and at most one physical boundary leg. -/
inductive CornerTable (K : Type*) {V : Type*} (d : V → ℕ) (A : Type*)
  | scalar (table : A → K)
  | stub (v : V) (table : A → Fin (d v) → K)

namespace CornerTable

def label {A : Type*} (U : CornerTable K d A) : Option V :=
  match U with
  | .scalar _ => none
  | .stub v _ => some v

def value {A : Type*} (U : CornerTable K d A) (x : ∀ v, Fin (d v)) : A → K :=
  match U with
  | .scalar f => f
  | .stub v f => fun a ↦ f a (x v)

/-- A boundary side contributes its polygon edge check and the table of its
left endpoint. -/
def sideTree {A B : Type*} [Fintype A] [Fintype B]
    (U : CornerTable K d A) (e : A → B → K) :
    OrderedTensorTree K d (Fintype.card (A × B)) :=
  match U with
  | .scalar f => .scalar (fun k ↦ let p := statePair A B k; e p.1 p.2 * f p.1)
  | .stub v f => .stub v (fun k c ↦ let p := statePair A B k; e p.1 p.2 * f p.1 c)

@[simp] theorem sideTree_labels {A B : Type*} [Fintype A] [Fintype B]
    (U : CornerTable K d A) (e : A → B → K) :
    (U.sideTree e).labels = U.label.toList := by cases U <;> rfl

@[simp] theorem sideTree_eval {A B : Type*} [Fintype A] [Fintype B]
    (U : CornerTable K d A) (e : A → B → K) (x : ∀ v, Fin (d v)) (k) :
    (U.sideTree e).eval x k = e (statePair A B k).1 (statePair A B k).2 *
      U.value x (statePair A B k).1 := by
  cases U with
  | scalar => rfl
  | stub v f => simp [sideTree, OrderedTensorTree.eval, value, linEval, boundaryValue, mul_ite]

theorem sideTree_bounded {A B : Type*} [Fintype A] [Fintype B]
    (U : CornerTable K d A) (e : A → B → K) {m : ℕ} (hq : Fintype.card (A × B) ≤ m)
    (hd : ∀ v, U.label = some v → d v ≤ m) : (U.sideTree e).Bounded m := by
  cases U with
  | scalar => exact hq
  | stub v f => exact ⟨hq, hd v rfl⟩

end CornerTable

namespace Triangulation

variable {l h : ℕ}

/-- The ordered tensor tree computes the triangulation's two-endpoint message. -/
def orderedTree {l h : ℕ} (T : Triangulation l h) (S : ℕ → Type*) [∀ i, Fintype (S i)]
    (U : ∀ i, CornerTable K d (S i)) (E : ∀ i j, S i → S j → K) :
    OrderedTensorTree K d (Fintype.card (S l × S h)) :=
  match T with
  | .side i => (U i).sideTree (E i (i+1))
  | .split (lo := i) (mid := m) (hi := j) _ _ L R =>
    .branch (pairingTable (S m) (E i j)) (L.orderedTree S U E) (R.orderedTree S U E)

theorem orderedTree_eval (T : Triangulation l h) (S : ℕ → Type*) [∀ i, Fintype (S i)]
    (U : ∀ i, CornerTable K d (S i)) (E : ∀ i j, S i → S j → K)
    (x : ∀ v, Fin (d v)) (k : Fin (Fintype.card (S l × S h))) :
    (T.orderedTree S U E).eval x k = T.eval S (fun i ↦ (U i).value x) E
      (statePair (S l) (S h) k).1 (statePair (S l) (S h) k).2 := by
  induction T with
  | side i => exact (U i).sideTree_eval _ _ _
  | split hl hr L R il ir =>
    simp only [orderedTree, OrderedTensorTree.eval]
    rw [funext il, funext ir]
    exact triEval_pairingTable _ _ _ k

/-- The leaves retain the cyclic order, starting after the distinguished root stub. -/
theorem orderedTree_labels (T : Triangulation l h) (S : ℕ → Type*) [∀ i, Fintype (S i)]
    (U : ∀ i, CornerTable K d (S i)) (E : ∀ i j, S i → S j → K) :
    (T.orderedTree S U E).labels =
      (List.range' l (h-l)).filterMap (fun i ↦ (U i).label) := by
  induction T with
  | side i =>
    simp only [orderedTree, CornerTable.sideTree_labels, Nat.add_sub_cancel_left, List.range'_succ,
      List.range'_zero, List.filterMap_cons, List.filterMap_nil]
    cases (U i).label <;> rfl
  | @split i m j hl hr L R il ir =>
    rw [orderedTree, OrderedTensorTree.labels, il, ir, ← List.filterMap_append]
    have hlist := @List.range'_append i (m-i) (j-m) 1
    rw [one_mul, show i+(m-i)=m by omega, show m-i+(j-m)=j-i by omega] at hlist
    rw [hlist]

/-- Only polygon-side pairs and the existing stub dimensions occur as channel dimensions. -/
theorem orderedTree_bounded (T : Triangulation l h) (S : ℕ → Type*) [∀ i, Fintype (S i)]
    (U : ∀ i, CornerTable K d (S i)) (E : ∀ i j, S i → S j → K) {m : ℕ}
    (hp : ∀ a b, (a,b) ∈ T.edges → Fintype.card (S a × S b) ≤ m)
    (hd : ∀ i v, l ≤ i → i < h → (U i).label = some v → d v ≤ m) :
    (T.orderedTree S U E).Bounded m := by
  induction T with
  | side i => exact (U i).sideTree_bounded _ (hp _ _ (root_mem _)) (fun v ↦ hd i v le_rfl (by omega))
  | split hl hr L R il ir =>
    refine ⟨hp _ _ (root_mem _), il ?_ ?_, ir ?_ ?_⟩
    · exact fun a b he ↦ hp a b (split_hasEdge.mpr (Or.inr (Or.inl he)))
    · exact fun i v h₁ h₂ ↦ hd i v h₁ (h₂.trans hr)
    · exact fun a b he ↦ hp a b (split_hasEdge.mpr (Or.inr (Or.inr he)))
    · exact fun i v h₁ h₂ ↦ hd i v (hl.le.trans h₁) h₂

end Triangulation
end PlanarPatch

end

end SpectralBooks
end LinearAlgebra
end OAI
