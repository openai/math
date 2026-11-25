import OAI.Computability.BorderVNP.DiagonalTaggedHistory

/-! # Tagged replay of a prescribed public history

A tagged transition uses the profile index already chosen by the public
system. Its sum may be evaluated over a different field from the one that
was used to choose the layout. In particular, dense ordering of the incoming
cables can be incorporated into the transition itself.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.Replay

open Crossing Shortening Adaptive Packing
open scoped BigOperators Classical

universe u

variable {k steps exp D : ℕ} {P Team Param Gadget E : Type}
    [Fintype Team] [Fintype Param] [Field E] {bits : P → ℕ}
    {A : ℕ → Type u} (S : System k steps A)
    (net : ∀ n, A n → Network D (Port k P n) (width bits k n))

/-- Enumerate the ordered batch of original team positions at this stage. -/
local instance publicReplayPortFinite {n : ℕ} : Fintype (Port k Team n) := batchFinite k Team n

/-- A transition on conditioned entries and power words over the chosen
public system. The result is stored on its actual successor layout. -/
def PublicTransition (Team Param Gadget : Type) [Fintype Team] [Fintype Param] (exp : ℕ) :=
  ∀ (n : ℕ) (hn : n < steps) (c : Fin k → A n),
    (∀ i, Tracked (Port k Team n) Param Gadget exp (net n (c i))) →
    (q : (S.choose n hn c).Index) →
      Tracked (Port k Team (n+1)) Param Gadget exp (net (n+1) ((S.choose n hn c).term q))

variable (move : PublicTransition S net Team Param Gadget exp)

/-- Tag the stored output using the original dependent sequence of public
profiles. Each leaf can have independently chosen private entries. -/
noncomputable def publicReplay :
    (n : ℕ) → (hn : n ≤ steps) → (a : Leaves k (A 0) n) →
      Inputs (net 0) Team Param Gadget exp n a →
      (q : (S.histories n hn a).Index) →
        Tracked (Port k Team n) Param Gadget exp (net n ((S.layer n).state ((S.histories n hn a).term q)))
  | 0, _, _, t, _ => t
  | n+1, hn, a, t, q =>
    let hj : n < steps := Nat.lt_of_succ_le hn
    let c := fun i : Fin k => (S.layer n).state ((S.histories n hj.le (a i)).term (q.1 i))
    move n hj c (fun i => publicReplay n hj.le (a i) (t i) (q.1 i)) q.2

/-- Exactness of the physical local transition after the scalar tables
have been interpreted in the chosen coefficient field. -/
def PublicTransition.Exact (values : Gadget → E) : Prop :=
  ∀ (n : ℕ) (hn : n < steps) (c : Fin k → A n)
    (tags : ∀ i, Tracked (Port k Team n) Param Gadget exp (net n (c i)))
    (x : Ports (width bits k (n+1))),
    (∏ i, ((tags i).valued values).tensor (fun p => x (i,p))) =
      ∑ q : (S.choose n hn c).Index, ((move n hn c tags q).valued values).tensor x

set_option maxHeartbeats 1800000 in
/-- The sum on the fixed public histories is the complete product of the
interpreted leaf tensors. All histories, including zero-weight terms, occur. -/
theorem sum_publicReplay (values : Gadget → E)
    (hmove : PublicTransition.Exact S net move values) (n : ℕ) (hn : n ≤ steps)
    (a : Leaves k (A 0) n) (t : Inputs (net 0) Team Param Gadget exp n a)
    (x : Ports (width bits k n)) :
    inputValue (net 0) values n a t x =
      ∑ q, ((publicReplay S net move n hn a t q).valued values).tensor x := by
  induction n with
  | zero => exact (Fintype.sum_unique (fun _ : PUnit => (t.valued values).tensor x)).symm
  | succ n ih =>
    let hj := Nat.lt_of_succ_le hn
    let H := fun j : Fin k => S.histories n hj.le (a j)
    let st := fun j (q : (H j).Index) => (S.layer n).state ((H j).term q)
    let tag := fun j (q : (H j).Index) => publicReplay S net move n hj.le (a j) (t j) q
    change (∏ j, inputValue _ values n (a j) (t j) (fun p => x (j,p))) = _
    trans ∏ j : Fin k, ∑ q : (H j).Index, ((tag j q).valued values).tensor (fun p => x (j,p))
    · apply Finset.prod_congr rfl
      intro j _
      exact ih hj.le (a j) (t j) (fun p => x (j,p))
    rw [Fintype.prod_sum]
    change _ = ∑ q : Σ c : ∀ j, (H j).Index, (S.choose n hj (fun j => st j (c j))).Index,
      ((publicReplay S net move (n+1) hn a t q).valued values).tensor x
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro c _
    exact hmove n hj (fun j => st j (c j)) (fun j => tag j (c j)) x

end Diagonal.CellEntries.Replay

end BorderVNP
end Computability
end OAI
