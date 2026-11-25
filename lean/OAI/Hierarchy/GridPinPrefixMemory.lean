import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range

namespace OAI
/-! # Prefix words left by the factor and bucket scans

A selected row publishes the old cursor for its owner, then advances the
cursor by the row length. Taking the memory value in an additive monoid
allows the statement to apply directly to native words.
-/

namespace Hierarchy.GridPinPrefixMemory

variable {Row Lane A : Type*} [AddMonoid A]
    (owner : Row → Lane) (size : Row → A) (cur : Lane → ℕ) (dst : Row → ℕ)

def store (mem : ℕ → A) (r : Row) : ℕ → A :=
  Function.update (Function.update mem (dst r) (mem (cur (owner r))))
    (cur (owner r)) (mem (cur (owner r)) + size r)

def run (mem : ℕ → A) (rows : List Row) : ℕ → A :=
  rows.foldl (store owner size cur dst) mem

theorem unchanged (mem : ℕ → A) (rows : List Row) (a : ℕ)
    (away : ∀ r ∈ rows, a ≠ dst r ∧ a ≠ cur (owner r)) :
    run owner size cur dst mem rows a = mem a := by
  induction rows generalizing mem with
  | nil => rfl
  | cons r rs ih =>
    have hr := away r List.mem_cons_self
    change run _ _ _ _ (store owner size cur dst mem r) rs a=_
    rw [ih _ (fun s hs => away s (List.mem_cons_of_mem _ hs))]
    simp [store,Function.update_of_ne,hr.1,hr.2]

variable [DecidableEq Lane]

/-- Each owner's cursor adds exactly the lengths of the selected earlier rows belonging to it. -/
theorem cursor_after (mem : ℕ → A) (rows : List Row) (lane : Lane)
    (unique : Function.Injective cur) (sep : ∀ t r, cur t ≠ dst r) :
    run owner size cur dst mem rows (cur lane) =
      mem (cur lane) + ((rows.filter (fun r => decide (owner r = lane))).map size).sum := by
  induction rows generalizing mem with
  | nil => simp [run]
  | cons r rs ih =>
    change run _ _ _ _ (store owner size cur dst mem r) rs (cur lane) = _
    rw [ih]
    by_cases yes : owner r=lane
    · simp [store,yes,add_assoc]
    · have ne := fun e : cur lane=cur (owner r) => yes (unique e).symm
      have same : store owner size cur dst mem r (cur lane) = mem (cur lane) := by
        unfold store
        rw [Function.update_of_ne ne, Function.update_of_ne (sep lane r)]
      rw [same]
      simp [yes]

/-- The destination of a row records the cursor before the row is charged. -/
theorem record_after (mem : ℕ → A) (pre : List Row) (r : Row) (post : List Row)
    (unique : Function.Injective cur) (sep : ∀ t i, cur t ≠ dst i)
    (later : ∀ s ∈ post, dst r ≠ dst s) :
    run owner size cur dst mem (pre ++ r :: post) (dst r) =
      mem (cur (owner r)) + ((pre.filter (fun s => decide (owner s=owner r))).map size).sum := by
  let m := run owner size cur dst mem pre
  change (pre ++ r :: post).foldl _ mem (dst r) = _
  rw [List.foldl_append]
  change run _ _ _ _ (store owner size cur dst m r) post (dst r) = _
  rw [unchanged _ _ _ _ _ _ _ (fun s hs => ⟨later s hs, (sep (owner s) r).symm⟩)]
  rw [store,Function.update_of_ne ((sep (owner r) r).symm),Function.update_self]
  exact cursor_after owner size cur dst mem pre (owner r) unique sep

/-- The caller's list of factors for one tick, or buckets for one factor, can
be split at the selected occurrence without exposing the other owners' rows. -/
theorem record_after_owner_split (mem : ℕ → A) (rows : List Row) (r : Row) (before after : List Row)
    (distinct : rows.Nodup) (unique : Function.Injective cur) (ids : Function.Injective dst)
    (sep : ∀ t i, cur t ≠ dst i)
    (index : rows.filter (fun s => decide (owner s=owner r))=before++r::after) :
    run owner size cur dst mem rows (dst r) = mem (cur (owner r)) + (before.map size).sum := by
  let same := fun s => decide (owner s=owner r)
  have hit : r ∈ rows.filter same := by
    dsimp only [same]
    rw [index]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨pre,post,parts⟩ := List.mem_iff_append.mp (List.mem_filter.mp hit).1
  subst rows
  have hrpre : r ∉ pre := by
    intro h
    exact (List.disjoint_left.mp (List.disjoint_of_nodup_append distinct)) h List.mem_cons_self
  have hrpost : r ∉ post := (List.nodup_append.mp distinct).2.1.notMem
  have filtered : pre.filter same ++ r::post.filter same = before++r::after := by
    simpa [List.filter_append,same] using index
  have eqn := (List.append_cons_inj_of_notMem
    (fun h => hrpre (List.mem_filter.mp h).1) (fun h => hrpost (List.mem_filter.mp h).1)).mp filtered
  rw [record_after owner size cur dst mem pre r post unique sep
    (fun s hs eq => hrpost ((ids eq).symm ▸ hs))]
  exact congrArg (fun l : List Row => (mem (cur (owner r)))+(l.map size).sum) eqn.1

omit [DecidableEq Lane] in
/-- Relate the arithmetic-loop ordinal to the stream of rows it actually selected. -/
theorem iter_selected (mem : ℕ → ℕ → A) (select : ℕ → Option Row) (n : ℕ)
    (step : ∀ i<n, mem (i+1)=(select i).elim (mem i) (store owner size cur dst (mem i))) :
    mem n=run owner size cur dst (mem 0) ((List.range n).filterMap select) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have old := ih (fun i hi => step i (Nat.lt_succ_of_lt hi))
    rw [step n (Nat.lt_succ_self n),List.range_succ,List.filterMap_append]
    cases h : select n <;> simp [run,old,List.foldl_append,h]


end Hierarchy.GridPinPrefixMemory

end OAI
