import OAI.Computability.VPVNP.PrimedCounterFold
import Mathlib.Data.List.OfFn

/-!
# Order and prefix capacity of the parser slots

The expanded loops run through all absolute cursor values consecutively.
Only node calls increase counts. The other calls preserve the histogram,
and the root initializer reinstates a stack representing at most `n` leaves.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Fold

open Chronology

variable {n m s w A S K T : ℕ}

private theorem row_order (u : Fin S) :
    (rowItems (m := m) (K := K) (T := T) u).map (fun i => (slot (A := A) i).val) =
      List.ofFn (fun j : Fin (Cursor.span m K) => A + (u.val * Cursor.span m K + j.val)) := by
  conv_rhs =>
    change List.ofFn (fun j : Fin (m + (1 + K)) => A + (u.val * Cursor.span m K + j.val))
    rw [List.ofFn_add, List.ofFn_add]
  simp [rowItems, slot, Cursor.index_site, List.ofFn_eq_map,
    Function.comp_def, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Reading the assembled inputs and then following the logical parser loops
gives exactly the increasing absolute cursor. -/
theorem items_order (A S m K T : ℕ) :
    (List.finRange A).map (fun i => Cursor.index A S m K T (.inl i)) ++
      (items S m K T).map slot = List.finRange (Cursor.calls A S m K T) := by
  apply (List.map_injective_iff.mpr Fin.val_injective)
  conv_rhs =>
    rw [← List.ofFn_eq_map]
    change List.ofFn (fun j : Fin (A + (S * Cursor.span m K + T)) => j.val)
    rw [List.ofFn_add, List.ofFn_add, List.ofFn_mul]
  simp only [items, List.map_append, List.map_map, List.map_flatMap, Function.comp_def,
    Cursor.index_input, slot, Cursor.index_compare]
  simp_rw [show ∀ u : Fin S,
    List.map (fun i => (Cursor.index A S m K T (.inr i)).val) (rowItems u) =
      List.ofFn (fun j : Fin (Cursor.span m K) => A + (u.val * Cursor.span m K + j.val)) from
    fun u => row_order u]
  simp [List.ofFn_eq_map, List.flatMap_def, Cursor.compareStart, Nat.add_assoc]

/-- Detect the parser-node slots, the only post-assembly calls that can increment production
counts. -/
def isNode : PostItem S m K T → Bool
  | .inl (_, .inr (.inr _)) => true
  | _ => false

@[simp] theorem rowItems_nodeCount (u : Fin S) :
    (rowItems (m := m) (K := K) (T := T) u).countP isNode = K := by
  simp [rowItems, List.countP_append, List.countP_map, Function.comp_def, isNode]

@[simp] theorem items_nodeCount (S m K T : ℕ) :
    (items S m K T).countP isNode = S*K := by
  simp [items, List.countP_append, List.countP_flatMap, List.countP_map, Function.comp_def, isNode]

private theorem call_bounds (d : Fin n) (root : Fin s) (x : Fin S → Fin m → Bool)
    (e : Label n m (Fin s) ≃ Fin T) (μ : Label n m (Fin s) →₀ ℕ) (raw : Tape A S m K T)
    (st out : VisitState n m s) (i : PostItem S m K T) (hm : leafMass st.pending ≤ n)
    (hc : call w d root x e μ raw st i = some out) :
    leafMass out.pending ≤ n ∧ ∀ a, out.counts a ≤ st.counts a + if isNode i then 1 else 0 := by
  rcases i with (⟨u, j | (j | j)⟩ | j)
  · simp only [call] at hc
    split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc
    subst out
    simpa only [isNode, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, le_refl, implies_true, and_true] using hm
  · simp only [call] at hc
    split at hc <;> simp only [Option.some.injEq, reduceCtorEq] at hc
    subst out
    exact ⟨d.isLt, fun _ => le_rfl⟩
  · have hh := visit_bounds _ _ _ _ hc
    exact ⟨hh.1.trans hm, hh.2.2⟩
  · simp only [call] at hc
    split at hc <;> simp_all [isNode]

/-- Bounds hold for every executed prefix, regardless of later rejection.
Each component increases by at most the number of node items. -/
theorem prefix_bounds (d : Fin n) (root : Fin s) (x : Fin S → Fin m → Bool)
    (e : Label n m (Fin s) ≃ Fin T) (μ : Label n m (Fin s) →₀ ℕ) (raw : Tape A S m K T)
    (st out : VisitState n m s) (p : List (PostItem S m K T)) (hm : leafMass st.pending ≤ n)
    (hc : p.foldlM (call w d root x e μ raw) st = some out) :
    leafMass out.pending ≤ n ∧ ∀ a, out.counts a ≤ st.counts a + p.countP isNode := by
  induction p generalizing st with
  | nil => simp at hc; subst out; simp [hm]
  | cons i p ih =>
    cases hi : call w d root x e μ raw st i with
    | none => simp [hi] at hc
    | some next =>
      obtain ⟨hm', hb⟩ := call_bounds d root x e μ raw st next i hm hi
      obtain ⟨hmo, ho⟩ := ih next hm' (by simpa [hi] using hc)
      refine ⟨hmo, fun a => ?_⟩
      specialize ho a
      specialize hb a
      rw [List.countP_cons]
      omega

/-- Immediately before a scheduled node, the next increment is bounded by
the number of node calls in the whole rectangle. -/
theorem next_increment_le (d : Fin n) (root : Fin s) (x : Fin S → Fin m → Bool)
    (e : Label n m (Fin s) ≃ Fin T) (μ : Label n m (Fin s) →₀ ℕ) (raw : Tape A S m K T)
    (out : VisitState n m s) (p q : List (PostItem S m K T)) (u : Fin S) (j : Fin K)
    (he : items S m K T = p ++ .inl (u, .inr (.inr j)) :: q)
    (hc : p.foldlM (call w d root x e μ raw) ⟨[],∅,0⟩ = some out) :
    leafMass out.pending ≤ n ∧ ∀ a, out.counts a + 1 ≤ S*K := by
  obtain ⟨hm, hh⟩ := prefix_bounds d root x e μ raw _ out p (by simp [leafMass]) hc
  refine ⟨hm, fun a => ?_⟩
  specialize hh a
  simp only [Finsupp.zero_apply, zero_add] at hh
  have he' := congrArg (List.countP isNode) he
  simp only [items_nodeCount, List.countP_append, List.countP_cons, isNode, ↓reduceIte] at he'
  omega

end PrimedCounter.Fold

end VPVNP
end Computability
end OAI
