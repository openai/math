import OAI.Computability.BorderVNP.ShortenAdaptiveTree
import OAI.Computability.BorderVNP.ShortenStageBounds

/-!
# Restricting the physical batch to its actual input leaves

An upper bound on the cost of the chosen K^b leaves bounds every
history above those leaves. Other admissible starting packs at the
same cover level may have arbitrarily larger cost.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Adaptive

open Packing

universe u

/-- A predicate on every original input in a finite leaf tuple. -/
def allLeaves {k : ℕ} {A : Type u} (test : A → Prop) : (n : ℕ) → Leaves k A n → Prop
  | 0, a => test a
  | n+1, a => ∀ i, allLeaves test n (a i)

namespace System

variable {k b : ℕ} {A : ℕ → Type u} (S : System k b A)

/-- A history passes the input bound precisely when each of its original
leaf states passes. -/
def fromInputs (test : A 0 → Prop) : (n : ℕ) → (S.layer n).Name → Prop
  | 0, a => test a
  | n+1, z => ∀ i, fromInputs test n (z.1 i)

/-- Every attained histogram history over a given leaf tuple has exactly
that tuple's admissible leaves. -/
theorem fromInputs_histories (test : A 0 → Prop) (n : ℕ) (hn : n ≤ b) (a : Leaves k (A 0) n)
    (ha : allLeaves test n a) (q : (S.histories n hn a).Index) :
    S.fromInputs test n ((S.histories n hn a).term q) := by
  induction n with
  | zero => exact ha
  | succ n ih => exact fun i => ih (by omega) (a i) (ha i) (q.1 i)

/-- The actual K-ary batch restricted to nodes satisfying the chosen initial predicate. -/
def batchFrom (W X : ∀ n, A n → ℝ) (test : A 0 → Prop) : Batch k where
  Packs := fun n => {a : (S.layer n).Name // S.fromInputs test n a}
  child := fun z i => ⟨z.val.1 i,z.property i⟩
  length := fun {n} p => W n ((S.layer n).state p.val)
  concentration := fun {n} p => X n ((S.layer n).state p.val)

/-- Passing to the chosen input leaves preserves both stage bounds. -/
theorem stageBounds_batchFrom (W X : ∀ n, A n → ℝ) (test : A 0 → Prop)
    {hk : 0 < k} {r V : ℝ} {C : Fin b → ℝ}
    (rows : (S.batch W X).StageBounds hk r V C) :
    (S.batchFrom W X test).StageBounds hk r V C := fun i z => rows i z.val

end System
end Shortening.Adaptive

end BorderVNP
end Computability
end OAI
