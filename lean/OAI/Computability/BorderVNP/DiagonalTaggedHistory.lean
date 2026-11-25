import OAI.Computability.BorderVNP.DiagonalTaggedHistoryStorage

/-!
# Replaying a fixed physical adaptive history on independently conditioned leaves

The public system selects a joint profile from the child layouts. The private
leaf assignments and the power-word data change the table at each node only.
All sums below use the very same dependent histogram indices as the physical
program, including branches whose interpreted contribution happens to vanish.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.Replay

open Crossing Shortening Adaptive Packing PlacedStep
open scoped BigOperators Classical

universe u

variable {k steps exp D m : ℕ} [NeZero D] {I P Team Param Gadget E : Type}
    [Fintype I] [Fintype Team] [Fintype Param] [Field E]
    {bits : P → ℕ} {A : ℕ → Type u} {B : Fin steps → Type} [∀ i, Fintype (B i)]
    {depth : ℕ → ℕ} {e : PaidIdentity E D m}
    {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) E I (depth n)}

/-- The batch type of a node consists of the child index followed by its
previous batch type. Its enumeration matches the real parallel composition. -/
@[instance_reducible] def batchFinite (k : ℕ) (T : Type) [Fintype T] : (n : ℕ) → Fintype (Port k T n)
  | 0 => inferInstanceAs (Fintype T)
  | n+1 =>
    letI : Fintype (Port k T n) := batchFinite k T n
    inferInstanceAs (Fintype (Fin k × Port k T n))

/-- Row-major enumeration of the original batches after these packing stages. -/
local instance {n : ℕ} : Fintype (Port k Team n) := batchFinite k Team n

/-- Give each physical leaf its own fine private table, even when its public
layout and scalar field state coincide with those of another leaf. -/
def Inputs (leaf : A 0 → Network D P bits) (Team Param Gadget : Type)
    [Fintype Team] [Fintype Param] (exp : ℕ) :
    (n : ℕ) → Leaves k (A 0) n → Type
  | 0, a => Tracked Team Param Gadget exp (leaf a)
  | n+1, a => (i : Fin k) → Inputs leaf Team Param Gadget exp n (a i)

/-- Product of all conditioned original leaf tensors. -/
noncomputable def inputValue (leaf : A 0 → Network D P bits) (values : Gadget → E) :
    (n : ℕ) → (a : Leaves k (A 0) n) → Inputs leaf Team Param Gadget exp n a →
      Ports (width bits k n) → MvPolynomial Param E
  | 0, _, t, x => (t.valued values).tensor x
  | n+1, a, t, x => ∏ i, inputValue leaf values n (a i) (t i) (fun p => x (i,p))

variable (F : Adaptive.Program (B := B) e view) (save : ProgramStorage F) (pos : e.Entry → Gadget)

/-- Public state at the end of the given attained profile history. -/
noncomputable def state (n : ℕ) (hn : n ≤ steps) (a : Leaves k (A 0) n)
    (q : (F.system.histories n hn a).Index) : A n :=
  (F.system.layer n).state ((F.system.histories n hn a).term q)

set_option maxHeartbeats 1500000 in
/-- The tagged tables on the actual stored layout at the end of that history. -/
noncomputable def replay :
    (n : ℕ) → (hn : n ≤ steps) → (a : Leaves k (A 0) n) →
      Inputs (fun a => (view 0 a).pack.layout) Team Param Gadget exp n a →
      (q : (F.system.histories n hn a).Index) →
      Tracked (Port k Team n) Param Gadget exp (view n (state F n hn a q)).pack.layout
  | 0, _, _, t, _ => t
  | n+1, hn, a, t, q => by
    let hj : n < steps := Nat.lt_of_succ_le hn
    let i : Fin steps := ⟨n,hj⟩
    let c := fun j : Fin k => state F n hj.le (a j) (q.1 j)
    let input := fun j : Fin k => replay n hj.le (a j) (t j) (q.1 j)
    exact (save i c q.2).tracked (Tracked.output e pos (F.step i c) input q.2)

set_option maxHeartbeats 1800000 in
/-- The original product is the sum over the very same attained public
histories. Private fine assignments on different leaves remain distinct. -/
theorem sum_replay (values : Gadget → E) (lookup : ∀ i, values (pos i) = e.entry i)
    (n : ℕ) (hn : n ≤ steps) (a : Leaves k (A 0) n)
    (t : Inputs (fun a => (view 0 a).pack.layout) Team Param Gadget exp n a)
    (x : Ports (width bits k n)) :
    inputValue (fun a => (view 0 a).pack.layout) values n a t x =
      ∑ q, ((replay F save pos n hn a t q).valued values).tensor x := by
  induction n with
  | zero =>
    exact (Fintype.sum_unique (fun _ : PUnit => (t.valued values).tensor x)).symm
  | succ n ih =>
    let hj : n < steps := Nat.lt_of_succ_le hn
    let i : Fin steps := ⟨n,hj⟩
    let H := fun j : Fin k => F.system.histories n hj.le (a j)
    let childState := fun j (q : (H j).Index) => state F n hj.le (a j) q
    let childTag := fun j (q : (H j).Index) => replay F save pos n hj.le (a j) (t j) q
    change (∏ j, inputValue _ values n (a j) (t j) (fun p => x (j,p))) = _
    trans ∏ j : Fin k, ∑ h : (H j).Index, ((childTag j h).valued values).tensor (fun p => x (j,p))
    · apply Finset.prod_congr rfl
      intro j _
      exact ih hj.le (a j) (t j) (fun p => x (j,p))
    rw [Fintype.prod_sum]
    change _ = ∑ y : Σ c : ∀ j, (H j).Index, (F.step i (fun j => childState j (c j))).Index e,
      ((replay F save pos (n+1) hn a t y).valued values).tensor x
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro c _
    let child := fun j : Fin k => childState j (c j)
    let tags := fun j : Fin k => childTag j (c j)
    refine (Tracked.sum_output e pos (F.step i child) tags values lookup x).trans ?_
    apply Finset.sum_congr _ (fun q _ => (Storage.tracked_tensor (save i child q)
      (Tracked.output e pos (F.step i child) tags q) values x).symm)
    exact congrArg (@Fintype.elems ((F.step i child).Index e)) (Subsingleton.elim _ _)

end Diagonal.CellEntries.Replay

end BorderVNP
end Computability
end OAI
