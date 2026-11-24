import OAI.Computability.VPVNP.PrimedCounterPreorder

/-!
# Stack execution of the primed parser

At each visit the machine pops the pending frame, produces one histogram label,
and pushes zero or two frames. The left child is visited first. The executable
scan below agrees with recursive tree decoding for every continuation stack.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter

open ParseGrammar

variable {n m : ℕ} {H : Type*}

/-- One pending grammar node represented by its bounded degree index and nonterminal state. -/
abbrev Frame (n : ℕ) (H : Type*) := Fin n × H
/-- A production histogram key for either a terminal position and bit or a binary split with
its parent and child states. -/
abbrev Label (n m : ℕ) (H : Type*) := GrammarLabel (Fin m × Bool) H n

/-- Pop one frame. The emitted label identifies the counter to increment, and
the replacement frames are prepended to the remaining stack. -/
def step (x : Fin m → Bool) : Frame n H → Token m H → Option (Label n m H × List (Frame n H))
  | (⟨0, _⟩, h), .terminal j => some (.inl (h, j, x j), [])
  | (⟨k + 1, hk⟩, h), .binary b i j =>
    if hb : b < k + 1 then
      let d : Fin n := ⟨k + 1, hk⟩
      let split : Fin d.val := ⟨b, hb⟩
      some (.inr ⟨d, h, split, i, j⟩, [(leftDegree d split, i), (rightDegree d split, j)])
    else none
  | _, _ => none

/-- Execute the flat stream of node choices. Completion requires exhausting
both the input stream and the pending stack at the same visit. -/
def scan (x : Fin m → Bool) : List (Frame n H) → List (Token m H) → Option (List (Label n m H))
  | [], [] => some []
  | [], _ :: _ | _ :: _, [] => none
  | f :: stack, t :: ts => do
    let (a, children) ← step x f t
    let rest ← scan x (children ++ stack) ts
    return a :: rest

/-- The production labels of a tree in visit order. -/
def labels (d : Fin n) (h : H) (p : OrderedParse (Fin m × Bool) H d.val) : List (Label n m H) :=
  match d, p with
  | ⟨0, _⟩, .leaf v => [.inl (h, v)]
  | ⟨k + 1, hk⟩, .node b i j l r =>
    let deg : Fin n := ⟨k + 1, hk⟩
    .inr ⟨deg, h, b, i, j⟩ :: (labels (leftDegree deg b) i l ++ labels (rightDegree deg b) j r)
termination_by d.val
decreasing_by all_goals first | exact leftDegree_lt _ _ | exact rightDegree_lt _ _

/-- The integer counter vector formed by adding one for each visit. -/
noncomputable def tally (as : List (Label n m H)) : Label n m H →₀ ℕ :=
  (as.map (fun a => Finsupp.single a 1)).sum

@[simp] theorem tally_append (as bs : List (Label n m H)) : tally (as ++ bs) = tally as + tally bs := by
  simp [tally]

theorem tally_labels (d : Fin n) (h : H) (p : OrderedParse (Fin m × Bool) H d.val) :
    tally (labels d h p) = histogram d h p := by
  induction d using (measure (fun d : Fin n => d.val)).wf.induction generalizing h with
  | h d ih =>
    obtain ⟨k, hk⟩ := d
    cases k with
    | zero =>
      cases p
      simp [labels, histogram, tally]
    | succ k =>
      cases p with
      | node b i j l r =>
        let d : Fin n := ⟨k + 1, hk⟩
        rw [labels, histogram]
        change Finsupp.single (.inr ⟨d, h, b, i, j⟩) 1 +
          tally (labels (leftDegree d b) i l ++ labels (rightDegree d b) j r) = _
        rw [tally_append, ih _ (leftDegree_lt d b) i l, ih _ (rightDegree_lt d b) j r]
        exact (add_assoc ..).symm

/-- Unrolling one root in a continuation stack consumes exactly one encoded
tree. This also handles malformed or truncated inputs and unused trailing choices. -/
theorem scan_cons (x : Fin m → Bool) (d : Fin n) (h : H) (stack : List (Frame n H))
    (ts : List (Token m H)) :
    scan x ((d, h) :: stack) ts =
      ((readTree x d.val ts).bind fun (p, tail) =>
        (scan x stack tail).map (fun rest => labels d h p ++ rest)) := by
  induction d using (measure (fun d : Fin n => d.val)).wf.induction generalizing h stack ts with
  | h d ih =>
    obtain ⟨k, hk⟩ := d
    cases ts with
    | nil => cases k <;> simp [scan, readTree]
    | cons t more =>
      cases k with
      | zero =>
        cases t with
        | binary => simp [scan, step, readTree]
        | terminal j =>
          cases hh : scan x stack more <;> simp [scan, step, readTree, labels, hh]
      | succ k =>
        cases t with
        | terminal => simp [scan, step, readTree]
        | binary b i j =>
          by_cases hb : b < k + 1
          · let d : Fin n := ⟨k + 1, hk⟩
            let b' : Fin d.val := ⟨b, hb⟩
            have hl := ih (leftDegree d b') (leftDegree_lt d b') i
              ((rightDegree d b', j) :: stack) more
            have hr := ih (rightDegree d b') (rightDegree_lt d b') j stack
            cases hh₁ : readTree x b more with
            | none =>
              simp [leftDegree, hh₁, d, b'] at hl
              simp [scan, step, readTree, hb, hh₁, hl, leftDegree]
            | some v =>
              obtain ⟨l, rest⟩ := v
              cases hh₂ : readTree x (k - b) rest with
              | none =>
                specialize hr rest
                simp [rightDegree, d, b', hh₂] at hr
                simp [leftDegree, d, b', hh₁, hr, rightDegree] at hl
                simp [scan, step, readTree, hb, hh₁, hh₂, hl, leftDegree, rightDegree]
              | some v =>
                obtain ⟨r, tail⟩ := v
                specialize hr rest
                simp [rightDegree, d, b', hh₂] at hr
                simp [leftDegree, d, b', hh₁, hr, rightDegree] at hl
                cases ht : scan x stack tail <;>
                  simp_all [scan, step, readTree, labels, leftDegree, rightDegree, List.append_assoc]
          · simp [scan, step, readTree, hb]

/-- An empty continuation stack cannot accept trailing choices. -/
theorem scan_nil (x : Fin m → Bool) (ts : List (Token m H)) :
    scan (n := n) x [] ts = if ts = [] then some [] else none := by cases ts <;> rfl

/-- Complete traversal from the prescribed root emits exactly the labels of
the unique parse recovered from this list of choices. -/
theorem scan_root (x : Fin m → Bool) (d : Fin n) (h : H) (ts : List (Token m H)) :
    scan x [(d,h)] ts = ((readTree x d.val ts).bind fun (p, tail) =>
      if tail.isEmpty then some (labels d h p) else none) := by
  rw [scan_cons]
  cases hr : readTree x d.val ts with
  | none => rfl
  | some v =>
    obtain ⟨p, tail⟩ := v
    cases tail <;> simp [scan]

/-- Linear mark checks and the stack traversal have the same acceptance
predicate as the recursive reader; every accepted tree supplies its histogram. -/
theorem scan_marked (x : Fin m → Bool) (d : Fin n) (h : H) (ts : List (Token m H)) :
    (if (positions ts).Nodup then (scan x [(d,h)] ts).map tally else none) =
      (checkedTree x d.val ts).map (histogram d h) := by
  rw [scan_root]
  cases hr : readTree x d.val ts with
  | none => simp [checkedTree, hr]
  | some v =>
    obtain ⟨p, tail⟩ := v
    cases tail <;> by_cases hn : (positions ts).Nodup <;> simp [checkedTree, hr, hn, tally_labels]

end PrimedCounter

end VPVNP
end Computability
end OAI
