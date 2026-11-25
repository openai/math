import OAI.Computability.BorderVNP.DiagonalTaggedHistory
import OAI.Computability.BorderVNP.DiagonalEpochTransport
import OAI.Computability.BorderVNP.ShortenEpochRoundHistory

/-! # Flattening a replay on the physically installed terminal pack -/

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

/-- Finiteness of the physical leaf port set at every tree height. -/
local instance flatReplayBatchFinite {n : ℕ} : Fintype (Port k Team n) := batchFinite k Team n

/-- Reorder each flat leaf's independently chosen private table into the
ordered physical tree of the geometry. -/
def flatInputs (leaf : A 0 → Network D P bits) :
    (n : ℕ) → (a : Fin (k^n) → A 0) → (∀ j, Tracked Team Param Gadget exp (leaf (a j))) →
      Inputs leaf Team Param Gadget exp n (leavesEquiv k (A 0) n a)
  | 0, _, t => t 0
  | n+1, a, t => fun i => flatInputs leaf n (fun j => a (copyIndex k n (i,j)))
      (fun j => t (copyIndex k n (i,j)))

omit [NeZero D] in
/-- The flat leaf values are precisely the independent input product. -/
theorem flat_input_value (leaf : A 0 → Network D P bits) (values : Gadget → E)
    (n : ℕ) (a : Fin (k^n) → A 0) (t : ∀ j, Tracked Team Param Gadget exp (leaf (a j)))
    (x : Ports (fun q : Fin (k^n) × P => bits q.2)) :
    inputValue leaf values n (leavesEquiv k (A 0) n a) (flatInputs leaf n a t) (nestedPorts bits k n x) =
      ∏ i, ((t i).valued values).tensor (fun p => x (i,p)) := by
  induction n with
  | zero => exact (Fintype.prod_unique (fun i : Fin 1 => ((t i).valued values).tensor (fun p => x (i,p)))).symm
  | succ n ih =>
    let f := fun i : Fin (k^(n+1)) => ((t i).valued values).tensor (fun p => x (i,p))
    have he := (copyIndex k n).prod_comp f
    rw [Fintype.prod_prod_type] at he
    refine Eq.trans ?_ he
    exact Finset.prod_congr rfl fun i _ => ih (fun j => a (copyIndex k n (i,j)))
      (fun j => t (copyIndex k n (i,j))) (fun p => x (copyIndex k n (i,p.1),p.2))

variable (F : Adaptive.Program (B := B) e view) (save : ProgramStorage F) (pos : e.Entry → Gadget)

/-- Replay the last step before its storage renumbering. This is the pack on
which the terminal geometric width and incidence estimates are stated. -/
noncomputable def executedTag :
    (n : ℕ) → (hn : n ≤ steps) → (a : Leaves k (A 0) n) →
      Inputs (fun a => (view 0 a).pack.layout) Team Param Gadget exp n a →
      (q : (F.system.histories n hn a).Index) →
      Tracked (Port k Team n) Param Gadget exp (F.executed n ((F.system.histories n hn a).term q)).pack.layout
  | 0, _, _, t, _ => t
  | n+1, hn, a, t, q => by
    let hj := Nat.lt_of_succ_le hn
    let i : Fin steps := ⟨n,hj⟩
    let c := fun j : Fin k => state F n hj.le (a j) (q.1 j)
    exact Tracked.output e pos (F.step i c)
      (fun j => replay F save pos n hj.le (a j) (t j) (q.1 j)) q.2

/-- All earlier stages may use the physical storage adapter, and the last
stage can be read on its true unrenumbered terminal layout. -/
theorem executed_tensor (n : ℕ) (hn : n ≤ steps) (a : Leaves k (A 0) n)
    (t : Inputs (fun a => (view 0 a).pack.layout) Team Param Gadget exp n a)
    (q : (F.system.histories n hn a).Index) (values : Gadget → E) (x : Ports (width bits k n)) :
    ((replay F save pos n hn a t q).valued values).tensor x =
      ((executedTag F save pos n hn a t q).valued values).tensor x := by
  cases n with
  | zero => rfl
  | succ n =>
    let hj := Nat.lt_of_succ_le hn
    let i : Fin steps := ⟨n,hj⟩
    let c := fun j : Fin k => state F n hj.le (a j) (q.1 j)
    exact Storage.tracked_tensor (save i c q.2) _ values x

/-- The tagged terminal summand on the true final site pack, with row-major
batch labels and the identical public wires as the geometric bound. -/
noncomputable def terminal (a : Fin (k^steps) → A 0)
    (t : ∀ j, Tracked Team Param Gadget exp (view 0 (a j)).pack.layout) (q : F.Hist a) :
    Tracked (Fin (k^steps) × Team) Param Gadget exp (flattenPack steps (F.terminal a q).pack).layout := by
  let s := executedTag F save pos steps le_rfl (leavesEquiv k (A 0) steps a)
    (flatInputs _ steps a t) q
  exact ⟨s.flat.tags,s.flat.words.relabel (portEquiv k Team steps).symm⟩

/-- The full one-epoch parameter-ring expansion, with its real histogram
indices, true terminal layouts and all original batch labels. -/
theorem terminal_sum (values : Gadget → E) (lookup : ∀ i, values (pos i) = e.entry i)
    (a : Fin (k^steps) → A 0) (t : ∀ j, Tracked Team Param Gadget exp (view 0 (a j)).pack.layout)
    (x : Ports (fun q : Fin (k^steps) × P => bits q.2)) :
    (∏ i, ((t i).valued values).tensor (fun p => x (i,p))) =
      ∑ q : F.Hist a, ((terminal F save pos a t q).valued values).tensor x := by
  let leaf := fun a => (view 0 a).pack.layout
  let tree := leavesEquiv k (A 0) steps a
  let t' := flatInputs leaf steps a t
  refine (flat_input_value leaf values steps a t x).symm.trans ?_
  refine (sum_replay F save pos values lookup steps le_rfl tree t' (nestedPorts bits k steps x)).trans ?_
  apply Finset.sum_congr rfl
  intro q _
  exact executed_tensor F save pos steps le_rfl tree t' q values (nestedPorts bits k steps x)

end Diagonal.CellEntries.Replay

end BorderVNP
end Computability
end OAI
