import OAI.Computability.VPVNP.PrimedCounterTraces

/-!
# Scratch capacity during the preorder traversal

The pending frames partition the still unread leaves. Their total leaf count
cannot increase, even if the path is later rejected for repeated positions.
Replacing a pending internal frame by its children decreases the number of
nodes still to visit by exactly one. These bounds apply after every prefix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter

open ParseGrammar
variable {n m : ℕ} {H : Type*}

/-- Unvisited leaves represented by the pending subtree roots. -/
def leafMass (stack : List (Frame n H)) := (stack.map fun f => f.1.val + 1).sum

/-- Nodes remaining in those subtrees, including their pending roots. -/
def pendingNodes (stack : List (Frame n H)) := (stack.map fun f => 2*f.1.val + 1).sum

private theorem length_le_mass (stack : List (Frame n H)) : stack.length ≤ leafMass stack := by
  induction stack with
  | nil => rfl
  | cons f stack ih =>
    change stack.length + 1 ≤ f.1.val + 1 + leafMass stack
    omega

theorem step_bounds (x : Fin m → Bool) (f : Frame n H) (t : Token m H)
    (a : Label n m H) (children stack : List (Frame n H)) (hs : step x f t = some (a, children)) :
    leafMass (children ++ stack) ≤ leafMass (f :: stack) ∧
    pendingNodes (children ++ stack) + 1 = pendingNodes (f :: stack) := by
  obtain ⟨⟨k, hk⟩, h⟩ := f
  cases k with
  | zero =>
    cases t with
    | binary => simp [step] at hs
    | terminal j =>
      simp [step] at hs
      obtain ⟨rfl, rfl⟩ := hs
      simp [leafMass, pendingNodes, Nat.add_comm]
  | succ k =>
    cases t with
    | terminal => simp [step] at hs
    | binary b i j =>
      by_cases hb : b < k+1
      · simp [step, hb] at hs
        obtain ⟨rfl, rfl⟩ := hs
        simp [leafMass, pendingNodes, leftDegree, rightDegree]
        omega
      · simp [step, hb] at hs

/-- Executing a prefix may leave pending subtrees for the next visit. -/
def advance (x : Fin m → Bool) : List (Frame n H) → List (Token m H) → Option (List (Frame n H))
  | stack, [] => some stack
  | [], _ :: _ => none
  | f :: stack, t :: ts => do
    let (_, children) ← step x f t
    advance x (children ++ stack) ts

/-- Prefix accounting includes malformed paths until their first failed step. -/
theorem advance_bounds (x : Fin m → Bool) (stack : List (Frame n H)) (ts : List (Token m H))
    (out : List (Frame n H)) (hs : advance x stack ts = some out) :
    leafMass out ≤ leafMass stack ∧ ts.length + pendingNodes out = pendingNodes stack := by
  induction ts generalizing stack with
  | nil => simp [advance] at hs; subst out; simp
  | cons t ts ih =>
    cases stack with
    | nil => simp [advance] at hs
    | cons f stack =>
      cases h : step x f t with
      | none => simp [advance, h] at hs
      | some v =>
        obtain ⟨a, children⟩ := v
        simp [advance, h] at hs
        obtain ⟨h₁, h₂⟩ := ih _ hs
        obtain ⟨b₁, b₂⟩ := step_bounds x f t a children stack h
        exact ⟨h₁.trans b₁, by simp only [List.length_cons]; omega⟩

/-- A stack plane of one word per possible leaf suffices at every prefix.
In particular no rejected path accesses an additional frame. -/
theorem root_bounds (x : Fin m → Bool) (d : Fin n) (h : H) (ts : List (Token m H))
    (out : List (Frame n H)) (hr : advance x [(d,h)] ts = some out) :
    out.length ≤ d.val + 1 ∧ ts.length ≤ 2*d.val + 1 := by
  obtain ⟨h₁, h₂⟩ := advance_bounds x [(d,h)] ts out hr
  simp only [leafMass, pendingNodes, List.map_singleton, List.sum_singleton] at h₁ h₂
  exact ⟨(length_le_mass out).trans h₁, h₂ ▸ Nat.le_add_right ..⟩

/-- Test and set the mark of each selected leaf. A fresh parse begins with
all marks cleared. -/
def testMarks : Finset (Fin m) → List (Token m H) → Option (Finset (Fin m))
  | marked, [] => some marked
  | marked, .terminal j :: more => if j ∈ marked then none else testMarks (insert j marked) more
  | marked, .binary .. :: more => testMarks marked more

theorem testMarks_eq_some_iff (marked : Finset (Fin m)) (ts : List (Token m H))
    (out : Finset (Fin m)) : testMarks marked ts = some out ↔
    (positions ts).Nodup ∧ (∀ j ∈ positions ts, j ∉ marked) ∧ out = marked ∪ (positions ts).toFinset := by
  induction ts generalizing marked with
  | nil => simp [testMarks, positions, eq_comm]
  | cons t ts ih =>
    cases t with
    | binary => simpa [testMarks, positions] using ih marked
    | terminal j =>
      by_cases hj : j ∈ marked
      · simp [testMarks, positions, hj]
      · simp only [testMarks, hj, ↓reduceIte, ih, positions, List.filterMap_cons, List.nodup_cons,
          List.mem_cons, List.toFinset_cons, Finset.mem_insert, not_or, forall_and, or_imp]
        simp only [Finset.insert_union, Finset.union_insert]
        aesop

/-- The linear test-and-set loop implements the decoder's position check. -/
theorem freshMarks_iff (ts : List (Token m H)) : (testMarks ∅ ts).isSome ↔ (positions ts).Nodup := by
  rw [Option.isSome_iff_exists]
  simp [testMarks_eq_some_iff]

end PrimedCounter

end VPVNP
end Computability
end OAI
