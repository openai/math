import OAI.Computability.BorderVNP.PackedProfiles
import OAI.Computability.BorderVNP.ShortenRecurrence

/-!
# The actual adaptive K-ary history tree inside one shortening epoch

Each node stores its K distinct predecessor histories and its new joint
profile. For an arbitrary tuple of initial packs the histories are finite.
The associated numerical batch is indexed by these same nodes and keeps
the exact predecessor projections used in the tensor expansion.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Adaptive

open Crossing Packing Finset
open scoped Classical

universe u

/-- The ordered original leaves of a single depth-n node. -/
def Leaves (k : ℕ) (A : Type u) : ℕ → Type u
  | 0 => A
  | n+1 => Fin k → Leaves k A n

/-- Public free ports after n stages, with each child's indices kept distinct. -/
def Port (k : ℕ) (P : Type) : ℕ → Type
  | 0 => P
  | n+1 => Fin k × Port k P n

/-- The bit width of a free port is inherited from its original leaf. -/
def width {P : Type} (bits : P → ℕ) (k : ℕ) : (n : ℕ) → Port k P n → ℕ
  | 0 => bits
  | n+1 => fun p => width bits k n p.2

/-- The independent tensor product of the given K^n input packs. -/
def parallelLeaves {D k : ℕ} {P : Type} {bits : P → ℕ} {R A : Type*}
    (leaf : A → Pack D P bits R) : (n : ℕ) → Leaves k A n → Pack D (Port k P n) (width bits k n) R
  | 0, x => leaf x
  | n+1, x => parallelPacks (fun i => parallelLeaves leaf n (x i))

/-- One bounded-height family of adaptive profile choices on the actual
child states. No stage is requested beyond the final round. -/
structure System (k b : ℕ) (A : ℕ → Type u) where
  /-- Profile enumeration and output state of a step after its inputs are known. -/
  choose : ∀ n, n < b → (Fin k → A n) → ProfileSum (A (n+1))

/-- A node history names a physical state at its stage. The set of all
possible starting states may be infinite; each fixed input tuple has
only finitely many attainable histories. -/
structure Layer (A : Type u) where
  /-- History and its initial leaf names. -/
  Name : Type u
  /-- The chosen output state. -/
  state : Name → A

namespace System

variable {k b : ℕ} {A : ℕ → Type u} (S : System k b A)

/-- Nodes store predecessor names and the attained profile of their actual child states. -/
def layer : (j : ℕ) → Layer (A j)
  | 0 => ⟨A 0,id⟩
  | n+1 =>
    let old := layer n
    { Name := Σ c : Fin k → old.Name, Σ h : PLift (n < b), (S.choose n h.down (fun i => old.state (c i))).Index
      state := fun z => (S.choose n z.2.1.down (fun i => old.state (z.1 i))).term z.2.2 }

/-- The true predecessor projections and measured state quantities give
the numerical Batch for the finite-stage recurrence. -/
def batch (W X : ∀ n, A n → ℝ) : Batch k where
  Packs := fun n => (S.layer n).Name
  child := fun p => p.1
  length := fun {n} p => W n ((S.layer n).state p)
  concentration := fun {n} p => X n ((S.layer n).state p)

/-- Lift a fixed parent profile into the global node history above the
specified child histories, retaining all those histories. -/
def nextNames (j : ℕ) (hj : j < b) (c : Fin k → (S.layer j).Name) : ProfileSum (S.layer (j+1)).Name :=
  let p := S.choose j hj (fun i => (S.layer j).state (c i))
  ⟨p.Index,p.finite,fun q => ⟨c,⟨⟨hj⟩,q⟩⟩⟩

/-- All attainable histories above an arbitrary fixed tuple of original
leaf states. Distinct profile choices retain separate summands. -/
def histories : (n : ℕ) → n ≤ b → Leaves k (A 0) n → ProfileSum (S.layer n).Name
  | 0, _, a => ⟨PUnit,inferInstance,fun _ => a⟩
  | n+1, hn, a => combineProfiles (fun i => histories n (by omega) (a i)) (S.nextNames n (by omega))

variable {D : ℕ} {P : Type} {bits : P → ℕ} {R : Type*} [CommSemiring R]
variable (pack : ∀ n, A n → Pack D (Port k P n) (width bits k n) R)

/-- A pointwise tensor identity on the concrete K child packs for each
attained next-stage profile. -/
def Exact : Prop :=
  ∀ j (hj : j < b) (c : Fin k → A j) (x : Ports (width bits k (j+1))),
    (parallelPacks (fun i => pack j (c i))).tensor x =
      ∑ q, (pack (j+1) ((S.choose j hj c).term q)).tensor x

set_option maxHeartbeats 1200000 in
/-- For every arbitrary input leaf tuple, the sum on the actual dependent
profile histories gives its full independent tensor product. -/
theorem tensor_histories (exact : S.Exact pack) (n : ℕ) (hn : n ≤ b) (a : Leaves k (A 0) n)
    (x : Ports (width bits k n)) :
    (parallelLeaves (pack 0) n a).tensor x =
      ∑ q, (pack n ((S.layer n).state ((S.histories n hn a).term q))).tensor x := by
  induction n with
  | zero =>
    exact (Fintype.sum_unique (fun _ : PUnit => (pack 0 a).tensor x)).symm
  | succ n ih =>
    let H := fun i : Fin k => S.histories n (by omega) (a i)
    let z := fun (i : Fin k) (t : (H i).Index) => (S.layer n).state ((H i).term t)
    refine (Network.parallel_value (fun i => (parallelLeaves (pack 0) n (a i)).layout)
      (fun i => (parallelLeaves (pack 0) n (a i)).table) x).trans ?_
    trans ∏ i : Fin k, ∑ h : (H i).Index, (pack n (z i h)).tensor (fun p => x (i,p))
    · exact prod_congr rfl fun i _ => ih (by omega) (a i) (fun p => x (i,p))
    rw [Fintype.prod_sum]
    change _ = ∑ y : Σ c : ∀ i, (H i).Index, (S.choose n (by omega) (fun i => z i (c i))).Index,
      (pack (n+1) ((S.choose n (by omega) (fun i => z i (y.1 i))).term y.2)).tensor x
    rw [Fintype.sum_sigma]
    apply sum_congr rfl
    intro c _
    exact (Network.parallel_value (fun i => (pack n (z i (c i))).layout)
      (fun i => (pack n (z i (c i))).table) x).symm.trans (exact n (by omega) (fun i => z i (c i)) x)

end System
end Shortening.Adaptive

end BorderVNP
end Computability
end OAI
