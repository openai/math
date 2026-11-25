import OAI.Computability.BorderVNP.PackedHistoryCapacity
import OAI.Computability.BorderVNP.PackedHistoryEpoch

/-! # Forgetting auxiliary state in a physical histogram tree

A projection retains the actual local branch index at each child tuple. Its
recursive action on a history applies those branch equivalences at each node.
Thus profiles leading to the same physical pack retain their separate indices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Shortening.Adaptive Packing

variable {k b : ℕ} {X A : ℕ → Type*}

/-- A map of adaptive states with exact correspondence of the local branches
and the physical state saved at each branch. -/
structure Projection (R : System k b X) (S : System k b A) where
  /-- Physical state carried by the decorated state. -/
  physical : ∀ n, X n → A n
  /-- Local branch correspondence before saving. -/
  branch : ∀ n (hn : n < b) (c : Fin k → X n),
    (R.choose n hn c).Index ≃ (S.choose n hn (physical n ∘ c)).Index
  /-- Forgetting the decoration commutes with this actual successor. -/
  successor : ∀ n hn c q, physical (n+1) ((R.choose n hn c).term q) =
    (S.choose n hn (physical n ∘ c)).term (branch n hn c q)

namespace Projection

variable {R : System k b X} {S : System k b A} (p : Projection R S)

/-- Forget auxiliary data on the bottom inputs of the same tree. -/
def leaves : (n : ℕ) → Leaves k (X 0) n → Leaves k (A 0) n
  | 0, a => p.physical 0 a
  | n+1, a => fun i => leaves n (a i)

/-- Correspondence of two history enumerations and the resulting physical states. -/
structure History (n : ℕ) (hn : n ≤ b) (x : Leaves k (X 0) n) (a : Leaves k (A 0) n) where
  /-- Map of branch histories. -/
  index : (R.histories n hn x).Index ≃ (S.histories n hn a).Index
  /-- Projected stored state on each particular history. -/
  root : ∀ q, p.physical n (state n hn x q) = state n hn a (index q)

private def castBranch (S : System k b A) {n : ℕ} (hn : n < b) {a a' : Fin k → A n}
    (h : a = a') : (S.choose n hn a).Index ≃ (S.choose n hn a').Index := h ▸ Equiv.refl _

private theorem castBranch_term (S : System k b A) {n : ℕ} (hn : n < b) {a a' : Fin k → A n}
    (h : a = a') (q : (S.choose n hn a).Index) :
    (S.choose n hn a).term q = (S.choose n hn a').term (castBranch S hn h q) := by
  subst a'; rfl

/-- Canonical recursive map. Every child history is mapped separately, then
the specified local correspondence acts on its chosen root histogram. -/
def histories : (n : ℕ) → (hn : n ≤ b) → (x : Leaves k (X 0) n) → p.History n hn x (p.leaves n x)
  | 0, _, _ => ⟨Equiv.refl _, fun _ => rfl⟩
  | n+1, hn, x => by
    have lower : n ≤ b := by omega
    have stage : n < b := by omega
    let child (i : Fin k) := histories n lower (x i)
    let children := Equiv.piCongrRight fun i => (child i).index
    let input (c : ∀ i, (R.histories n lower (x i)).Index) :=
      fun i => state (S := R) n lower (x i) (c i)
    let target (c : ∀ i, (S.histories n lower (p.leaves n (x i))).Index) :=
      fun i => state (S := S) n lower (p.leaves n (x i)) (c i)
    have agree (c) : p.physical n ∘ input c = target (children c) := funext fun i => (child i).root (c i)
    let fiber (c) := (p.branch n stage (input c)).trans (castBranch S stage (agree c))
    refine ⟨Equiv.sigmaCongr (β₁ := fun c => (R.choose n stage (input c)).Index)
      (β₂ := fun c => (S.choose n stage (target c)).Index) children fiber,?_⟩
    rintro ⟨c,q⟩
    exact (p.successor n stage (input c) q).trans (castBranch_term S stage (agree c) _)

/-- Projection acts on the genuine row-major flat leaves without reordering. -/
theorem leaves_flat (n : ℕ) (x : Fin (k^n) → X 0) :
    p.leaves n (leavesEquiv k _ n x) = leavesEquiv k _ n (p.physical 0 ∘ x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact funext fun i => ih (fun j => x (copyIndex k n (i,j)))

/-- Map all branch choices at the given decorated flat inputs to the actual
physical histories on their specified projections. -/
def flat (x : Fin (k^b) → X 0) (a : Fin (k^b) → A 0) (start : ∀ i, p.physical 0 (x i) = a i) :
    p.History b le_rfl (leavesEquiv k _ b x) (leavesEquiv k _ b a) := by
  have he := (p.leaves_flat b x).trans (congrArg (leavesEquiv k _ b) (funext start))
  exact he ▸ p.histories b le_rfl (leavesEquiv k _ b x)

/-- The bounded machine forgets only its capacity proof. Its local profile
correspondence is literally the identity at every child tuple. -/
def capacity (S : System k b A) (good : ∀ n, A n → Prop) (closed : Capacity.Closed S good) :
    Projection (Capacity.restrict S good closed) S where
  physical _ := Subtype.val
  branch _ _ _ := Equiv.refl _
  successor _ _ _ _ := rfl

end Projection
end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
