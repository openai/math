import Mathlib.Data.Nat.Log
import OAI.Computability.NearSquareRoot.BoxShape
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Flatten

/-!
# The balanced tree for the tape CRT permutation

The indices of the axes are listed fastest first. Each interval splits after half its
axes, rounded down. Blocks of length zero are permitted so all levels are defined even
when the axis count is not a power of two. A block of length at most one requires no CRT
rotation, since its left child is empty.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTree

variable {α : Type*}

def left (xs : List α) := xs.take (xs.length / 2)
def right (xs : List α) := xs.drop (xs.length / 2)
def children (xs : List α) := [left xs, right xs]

def level : ℕ → List α → List (List α)
  | 0, xs => [xs]
  | t + 1, xs => (level t xs).flatMap children

/-- A balanced binary split sends a list of length at most twice the
capacity to two child lists of length at most the capacity. -/
theorem length_le_of_mem_children {xs ys : List α} {m : ℕ}
    (h : xs.length ≤ 2 * m) (hy : ys ∈ children xs) : ys.length ≤ m := by
  simp only [children, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · simp only [left, List.length_take]
    omega
  · simp only [right, List.length_drop]
    omega

/-- Every node at depth t has length at most m when the input has
length at most m times two to the t. This includes empty child lists. -/
theorem length_le_of_mem_level {xs ys : List α} {t m : ℕ}
    (h : xs.length ≤ m * 2 ^ t) (hy : ys ∈ level t xs) : ys.length ≤ m := by
  induction t generalizing m ys with
  | zero =>
    simp only [level, List.mem_singleton] at hy
    simpa [hy] using h
  | succ t ih =>
    obtain ⟨p, hp, hy⟩ := List.mem_flatMap.mp hy
    apply length_le_of_mem_children (ys := ys) _ hy
    apply ih _ hp
    simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- At the ceiling base-two logarithm of the input length, every
remaining part is empty or a singleton. -/
theorem length_le_one_of_mem_clog_level {xs ys : List α}
    (hy : ys ∈ level (Nat.clog 2 xs.length) xs) : ys.length ≤ 1 :=
  length_le_of_mem_level (m := 1)
    (by simpa using Nat.le_pow_clog (by decide : 1 < 2) xs.length) hy

@[simp] theorem append_halves (xs : List α) : left xs ++ right xs = xs :=
  List.take_append_drop ..

/-- The same partition described recursively down from the root. -/
theorem level_succ_eq (t : ℕ) (xs : List α) :
    level (t + 1) xs = level t (left xs) ++ level t (right xs) := by
  induction t with
  | zero => simp [level, children]
  | succ t ih =>
    simpa only [level, List.flatMap_append] using congrArg (List.flatMap children) ih

/-- Concatenating disjoint intervals in the order of a level recovers the entire input. -/
@[simp] theorem flatten_level (t : ℕ) (xs : List α) : (level t xs).flatten = xs := by
  induction t generalizing xs with
  | zero => simp [level]
  | succ t ih => rw [level_succ_eq, List.flatten_append, ih, ih, append_halves]

theorem pairwise_disjoint_level (t : ℕ) {xs : List α} (hx : xs.Nodup) :
    (level t xs).Pairwise List.Disjoint :=
  (List.nodup_flatten.mp (by simpa using hx : (level t xs).flatten.Nodup)).2

/-- All left children supply the control coordinates for the rotations at a depth. -/
def controls (t : ℕ) (xs : List α) : List α := (level t xs).flatMap left

theorem controls_sublist (t : ℕ) (xs : List α) : (controls t xs).Sublist xs := by
  simpa only [List.flatMap_id, flatten_level, controls] using
    (List.Sublist.flatMap_right (level t xs) (g := id) (f := left)
      (fun l _ => List.take_sublist _ l))

theorem twice_controls_length_le (t : ℕ) (xs : List α) :
    2 * (controls t xs).length ≤ xs.length := by
  suffices h : ∀ nodes : List (List α), 2 * (nodes.flatMap left).length ≤ nodes.flatten.length by
    simpa only [controls, flatten_level] using h (level t xs)
  intro nodes
  induction nodes with
  | nil => simp
  | cons l ls ih =>
    simp only [List.flatMap_cons, List.flatten_cons, List.length_append,
      left, List.length_take] at *
    omega

/-- The possible short final axis adds at most one full width to the doubled
control footprint. -/
theorem controlWidth {k l : ℕ} {box : List (ℕ × ℕ)}
    (hb : BoxShape.Valid k l box) (t : ℕ) :
    2 * ((controls t box).map Prod.fst).sum ≤ k + l :=
  hb.controlWidth (controls_sublist ..) (twice_controls_length_le ..)

theorem controlFraction {k l : ℕ} {box : List (ℕ × ℕ)}
    (hb : BoxShape.Valid k l box) (t : ℕ) (hl : 2*l ≤ k) :
    4 * ((controls t box).map Prod.fst).sum ≤ 3*k :=
  hb.controlFraction (controls_sublist ..) (twice_controls_length_le ..) hl

theorem infix_of_mem_level {xs node : List α} {t : ℕ} (h : node ∈ level t xs) :
    node.IsInfix xs := by
  induction t generalizing node with
  | zero =>
    simp only [level, List.mem_singleton] at h
    subst node
    exact List.infix_refl _
  | succ t ih =>
    obtain ⟨p, hp, h⟩ := List.mem_flatMap.mp h
    simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact (List.take_prefix _ p).isInfix.trans (ih hp)
    · exact (List.drop_suffix _ p).isInfix.trans (ih hp)

/-- A slice of consecutive addresses is the full consecutive range between its endpoints. -/
theorem exists_range'_of_infix {base d : ℕ} {part : List ℕ}
    (h : part.IsInfix (List.range' base d)) :
    ∃ off : ℕ, off + part.length ≤ d ∧ part = List.range' (base + off) part.length := by
  obtain ⟨pre, post, h⟩ := h
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_range'] at hlen
  refine ⟨pre.length, by omega, ?_⟩
  have he := congrArg (fun l : List ℕ => (l.drop pre.length).take part.length) h
  simpa only [List.append_assoc, List.drop_left, List.take_left, List.drop_range',
    Nat.mul_one, List.take_range'_of_length_ge (show d - pre.length ≥ part.length by omega)] using he

theorem finRange_map_val (d : ℕ) : (List.finRange d).map Fin.val = List.range d := by
  apply List.ext_getElem <;> simp

/-- At every depth the addresses in a coprime-axis tree node form one contiguous interval. -/
theorem finRange_node_addresses {d t : ℕ} {node : List (Fin d)}
    (h : node ∈ level t (List.finRange d)) :
    ∃ start : ℕ, start + node.length ≤ d ∧ node.map Fin.val = List.range' start node.length := by
  have hh := List.IsInfix.map Fin.val (infix_of_mem_level h)
  rw [finRange_map_val, List.range_eq_range'] at hh
  simpa using exists_range'_of_infix hh

theorem level_map {β : Type*} (f : α → β) (t : ℕ) (xs : List α) :
    level t (xs.map f) = (level t xs).map (List.map f) := by
  induction t generalizing xs with
  | zero => simp [level]
  | succ t ih =>
    rw [level_succ_eq, level_succ_eq, List.map_append, ← ih, ← ih]
    simp [left, right]

theorem controls_map {β : Type*} (f : α → β) (t : ℕ) (xs : List α) :
    controls t (xs.map f) = (controls t xs).map f := by
  simp [controls, level_map, List.map_flatMap, List.flatMap_map, left]

/-- All target blocks operate on pairwise disjoint axes, and every control axis
is outside their union. -/
theorem controls_disjoint_targets (t : ℕ) {xs : List α} (hx : xs.Nodup) :
    (controls t xs).Disjoint ((level t xs).flatMap right) ∧
      ((level t xs).map right).Pairwise List.Disjoint := by
  have partition (nodes : List (List α)) :
      (nodes.flatMap left ++ nodes.flatMap right).Perm nodes.flatten := by
    induction nodes with
    | nil => simp
    | cons l ls ih =>
      simp only [List.flatMap_cons, List.flatten_cons, List.append_assoc]
      have hs := (List.perm_append_comm_assoc (ls.flatMap left) (right l)
        (ls.flatMap right)).append_left (left l)
      apply hs.trans
      rw [← List.append_assoc, append_halves]
      exact ih.append_left l
  obtain ⟨_, hright, hdisj⟩ := List.nodup_append'.mp
    ((partition (level t xs)).nodup_iff.mpr (by simpa using hx))
  refine ⟨hdisj, List.nodup_flatten.mp ?_ |>.2⟩
  simpa only [← List.flatMap_def] using hright

end CRTTree

end NearSquareRoot
end Computability
end OAI
