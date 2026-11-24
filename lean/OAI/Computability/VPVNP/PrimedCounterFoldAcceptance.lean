import OAI.Computability.VPVNP.PrimedCounterFoldOrder

/-!
# Acceptance of the absolute-cursor parser loop

Clearing all mark addresses and initializing the root reconstructs the
per-site start state. The node calls then agree with `visits` for every
tape. The dense comparisons accept exactly when every nominated component
agrees with the accumulated histogram.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Fold

open Chronology
open scoped Classical

variable {n m s w A S K T : ℕ}

private def rowAdmin (raw : Tape A S m K T) (u : Fin S) : Prop :=
  (∀ j : Fin m, raw (slot (.inl (u, .inl j))) = []) ∧
    raw (slot (.inl (u, .inr (.inl 0)))) = []

private theorem clear_fold (d : Fin n) (root : Fin s) (x : Fin S → Fin m → Bool)
    (e : Label n m (Fin s) ≃ Fin T) (μ : Label n m (Fin s) →₀ ℕ) (raw : Tape A S m K T)
    (st : VisitState n m s) (u : Fin S) (js : List (Fin m)) :
    (js.map (fun j => Sum.inl (u, Sum.inl j))).foldlM (call w d root x e μ raw) st =
      if ∀ j ∈ js, raw (slot (.inl (u, .inl j))) = [] then
        some {st with marked := st.marked \ js.toFinset} else none := by
  induction js generalizing st with
  | nil => simp
  | cons j js ih =>
    by_cases hj : raw (slot (.inl (u, .inl j))) = []
    · have hh : (st.marked.erase j) \ js.toFinset = st.marked \ (j :: js).toFinset := by
        ext a
        simp [and_assoc, and_left_comm]
      simp only [List.map_cons, List.foldlM_cons, call, hj, ↓reduceIte, bind, Option.bind_some,
        ih, List.mem_cons, forall_eq_or_imp, true_and, hh]
    · simp [call, hj]

/-- Execute a row, including all of its administrative tape checks. -/
theorem row_fold (d : Fin n) (root : Fin s) (x : Fin S → Fin m → Bool)
    (e : Label n m (Fin s) ≃ Fin T) (μ : Label n m (Fin s) →₀ ℕ) (raw : Tape A S m K T)
    (st : VisitState n m s) (u : Fin S) (hK : K = 2*d.val+1) :
    (rowItems u).foldlM (call w d root x e μ raw) st =
      if rowAdmin raw u then
        visits w (x u) ⟨[(d,root)],∅,st.counts⟩ (List.ofFn (nodePart raw u)) else none := by
  let init : VisitState n m s := ⟨[(d,root)],∅,st.counts⟩
  have hn : nodePrefix w (x u) init (List.ofFn (nodePart raw u)) =
      visits w (x u) init (List.ofFn (nodePart raw u)) :=
    nodePrefix_visits _ _ _ (by simp [init, pendingNodes, hK])
  have hclear : st.marked \ Finset.univ = ∅ := by ext; simp
  rw [rowItems, List.foldlM_append, List.foldlM_append, clear_fold]
  by_cases hc : ∀ j : Fin m, raw (slot (.inl (u, .inl j))) = []
  · by_cases hr : raw (slot (.inl (u, .inr (.inl 0)))) = []
    · simp [hc, hr, hclear, rowAdmin, call, List.foldlM_map]
      simpa only [nodePrefix, List.ofFn_eq_map, List.foldlM_map, nodePart, slot, init] using hn
    · simp [hc, hr, rowAdmin, call]
  · simp [hc, rowAdmin]

private theorem rows_fold (d : Fin n) (root : Fin s) (x : Fin S → Fin m → Bool)
    (e : Label n m (Fin s) ≃ Fin T) (μ : Label n m (Fin s) →₀ ℕ) (raw : Tape A S m K T)
    (st : VisitState n m s) (rows : List (Fin S)) (hK : K = 2*d.val+1) :
    ((rows.flatMap rowItems).foldlM (call w d root x e μ raw) st).map VisitState.counts =
      if ∀ u ∈ rows, rowAdmin raw u then
        runSites w d root x (fun v => List.ofFn (nodePart raw v)) rows st.counts else none := by
  induction rows generalizing st with
  | nil => simp [runSites]
  | cons u rows ih =>
    rw [List.flatMap_cons, List.foldlM_append, row_fold d root x e μ raw st u hK]
    by_cases hu : rowAdmin raw u
    · cases hv : visits w (x u) ⟨[(d,root)],∅,st.counts⟩ (List.ofFn (nodePart raw u)) with
      | none =>
        by_cases ha : ∀ v ∈ rows, rowAdmin raw v <;>
          simp [hu, ha, hv, runSites]
      | some next => simp [hu, hv, runSites, ih]
    · simp [hu]

private theorem compare_fold (d : Fin n) (root : Fin s) (x : Fin S → Fin m → Bool)
    (e : Label n m (Fin s) ≃ Fin T) (μ : Label n m (Fin s) →₀ ℕ) (raw : Tape A S m K T)
    (st : VisitState n m s) (js : List (Fin T)) :
    (js.map Sum.inr).foldlM (call w d root x e μ raw) st =
      if ∀ j ∈ js, raw (slot (.inr j)) = [] ∧ st.counts (e.symm j) = μ (e.symm j)
      then some st else none := by
  induction js with
  | nil => simp
  | cons j js ih =>
    by_cases hj : raw (slot (.inr j)) = [] ∧ st.counts (e.symm j) = μ (e.symm j) <;>
      simp [call, hj, ih]

/-- The parser portion of the tape succeeds exactly when the administrative
slots are empty and the operational site histograms add to the nomination. -/
theorem accepts_iff (d : Fin n) (root : Fin s) (x : Fin S → Fin m → Bool)
    (e : Label n m (Fin s) ≃ Fin T) (μ : Label n m (Fin s) →₀ ℕ) (raw : Tape A S m K T)
    (st : VisitState n m s) (hK : K = 2*d.val+1) :
    ((items S m K T).foldlM (call w d root x e μ raw) st).isSome ↔
      AdminEmpty raw ∧ runSites w d root x (fun u => List.ofFn (nodePart raw u))
        (List.finRange S) st.counts = some μ := by
  have ha : AdminEmpty raw ↔ (∀ u, rowAdmin raw u) ∧ ∀ j, raw (slot (.inr j)) = [] := by
    constructor
    · intro h
      exact ⟨fun u => ⟨h.1 u, h.2.1 u 0⟩, h.2.2⟩
    · rintro ⟨h,h'⟩
      exact ⟨fun u => (h u).1, fun u j => (Subsingleton.elim j 0) ▸ (h u).2, h'⟩
  have hr := rows_fold (w := w) d root x e μ raw st (List.finRange S) hK
  simp only [List.mem_finRange, forall_const] at hr
  rw [items, List.foldlM_append, ha]
  cases h : ((List.finRange S).flatMap rowItems).foldlM (call w d root x e μ raw) st with
  | none =>
    by_cases hm : ∀ u, rowAdmin raw u
    · have hs : runSites w d root x (fun u => List.ofFn (nodePart raw u))
          (List.finRange S) st.counts = none := by simpa [h,hm] using hr.symm
      simp [hs]
    · simp [hm]
  | some out =>
    have hm : ∀ u, rowAdmin raw u := by by_contra he; simp [h,he] at hr
    have hs : runSites w d root x (fun u => List.ofFn (nodePart raw u))
        (List.finRange S) st.counts = some out.counts := by simpa [h,hm] using hr.symm
    have hh : (∀ j, out.counts (e.symm j) = μ (e.symm j)) ↔ out.counts = μ := by
      constructor
      · intro he
        ext a
        simpa using he (e a)
      · rintro rfl
        simp
    simp [compare_fold, hm, hs, forall_and, hh]

end PrimedCounter.Fold

end VPVNP
end Computability
end OAI
