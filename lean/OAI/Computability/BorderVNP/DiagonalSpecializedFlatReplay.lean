import OAI.Computability.BorderVNP.DiagonalFlatReplay
import OAI.Computability.BorderVNP.DiagonalSpecializedHistory

/-! # Flat, field-specialized output on the chosen public histories

The last physical move is read on its unrenumbered output. Prior nodes may
store their edges in any prescribed order. The flat output ports and every
original power-word position use the same copy permutation as the reference
epoch. For public systems which include dense ordering in the transition
itself, the stored flat terminal is also available directly.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.Replay
open Crossing Shortening Adaptive Packing PlacedStep
open scoped BigOperators Classical

universe u

variable {k steps exp D : ℕ} {P Team Param Gadget E : Type}
  [Fintype Team] [Fintype Param] [Field E] {bits : P → ℕ} {A : ℕ → Type u}

/-- Finiteness of the flat replay input ports, independent of the scalar field. -/
local instance specializedFlatBatchFinite {n : ℕ} : Fintype (Port k Team n) := batchFinite k Team n

/-- Flatten the ports of a network independently of any scalar table. -/
abbrev flatLayout (n : ℕ) (M : Network D (Port k P n) (width bits k n)) :=
  (flattenPack n (⟨M, fun _ _ _ => ()⟩ : Pack D _ _ Unit)).layout

variable (S : System k steps A) (net : ∀ n, A n → Network D (Port k P n) (width bits k n))
  (move : PublicTransition S net Team Param Gadget exp)

/-- Flatten a prescribed public system's actual stored terminal layout, preserving
the exact row-major leaf label on every unary power word. -/
noncomputable def publicFlat (n : ℕ) (hn : n ≤ steps) (a : Fin (k ^ n) → A 0)
    (t : ∀ j, Tracked Team Param Gadget exp (net 0 (a j)))
    (q : (S.histories n hn (leavesEquiv k _ n a)).Index) :
    Tracked (Fin (k ^ n) × Team) Param Gadget exp
      (flatLayout n (net n ((S.layer n).state ((S.histories n hn (leavesEquiv k _ n a)).term q)))) := by
  let s := publicReplay S net move n hn _ (flatInputs _ n a t) q
  exact ⟨s.flat.tags, s.flat.words.relabel (portEquiv k Team n).symm⟩

/-- The physical stored flat terminals of any exact public transition give the
full input product, even when the public choices and scalar evaluation live
over different fields. -/
theorem publicFlat_sum (values : Gadget → E) (exactMove : PublicTransition.Exact S net move values)
    (n : ℕ) (hn : n ≤ steps) (a : Fin (k ^ n) → A 0)
    (t : ∀ j, Tracked Team Param Gadget exp (net 0 (a j)))
    (x : Ports (fun q : Fin (k ^ n) × P => bits q.2)) :
    (∏ i, ((t i).valued values).tensor (fun p => x (i,p))) =
      ∑ q, ((publicFlat S net move n hn a t q).valued values).tensor x := by
  exact (flat_input_value (net 0) values n a t x).symm.trans
    (sum_publicReplay S net move values exactMove n hn _ (flatInputs _ n a t) (nestedPorts bits k n x))

variable {m : ℕ} [NeZero D] {I K : Type} [Fintype I] [Field K]
  {B : Fin steps → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ} {e : PaidIdentity K D m}
  {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
  (F : Adaptive.Program (B := B) e view) (save : ProgramStorage F) (y : e.Entry → E)
  (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
    MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget)

/-- Specialized private entries just before the storage permutation of the last
round, on the reference program's true geometric output layout. -/
noncomputable def specializedExecuted :
    (n : ℕ) → (hn : n ≤ steps) → (a : Leaves k (A 0) n) →
      Inputs (fun a => (view 0 a).pack.layout) Team Param Gadget exp n a →
      (q : (F.system.histories n hn a).Index) →
      Tracked (Port k Team n) Param Gadget exp (F.executed n ((F.system.histories n hn a).term q)).pack.layout
  | 0, _, _, t, _ => t
  | n+1, hn, a, t, q => by
    let hj := Nat.lt_of_succ_le hn
    let i : Fin steps := ⟨n,hj⟩
    let c := fun j : Fin k => state F n hj.le (a j) (q.1 j)
    exact Tracked.specializedOutput e y hy pos (F.step i c)
      (fun j => specializedReplay F save y hy pos n hj.le (a j) (t j) (q.1 j)) q.2

/-- The actually saved state and the actually executed final move have the same
conditioned tensor at every fixed profile, despite any cable renumbering. -/
theorem specializedExecuted_tensor (n : ℕ) (hn : n ≤ steps) (a : Leaves k (A 0) n)
    (t : Inputs (fun a => (view 0 a).pack.layout) Team Param Gadget exp n a)
    (q : (F.system.histories n hn a).Index) (values : Gadget → E) (x : Ports (width bits k n)) :
    ((specializedReplay F save y hy pos n hn a t q).valued values).tensor x =
      ((specializedExecuted F save y hy pos n hn a t q).valued values).tensor x := by
  cases n with
  | zero => rfl
  | succ n =>
    let hj := Nat.lt_of_succ_le hn
    let i : Fin steps := ⟨n,hj⟩
    let c := fun j : Fin k => state F n hj.le (a j) (q.1 j)
    exact Storage.tracked_tensor (save i c q.2) _ values x

/-- The specialized tagged terminal summand on the chosen physical histogram,
flattened with exactly the public epoch's row-major external port order. -/
noncomputable def specializedTerminal (a : Fin (k ^ steps) → A 0)
    (t : ∀ j, Tracked Team Param Gadget exp (view 0 (a j)).pack.layout) (q : F.Hist a) :
    Tracked (Fin (k ^ steps) × Team) Param Gadget exp (flattenPack steps (F.terminal a q).pack).layout := by
  let s := specializedExecuted F save y hy pos steps le_rfl (leavesEquiv k _ steps a) (flatInputs _ steps a t) q
  exact ⟨s.flat.tags, s.flat.words.relabel (portEquiv k Team steps).symm⟩

/-- Summing the specialized flat tensors over exactly the reference-field
histories preserves the entire formal polynomial on each external input. -/
theorem specializedTerminal_sum (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (a : Fin (k ^ steps) → A 0) (t : ∀ j, Tracked Team Param Gadget exp (view 0 (a j)).pack.layout)
    (x : Ports (fun q : Fin (k ^ steps) × P => bits q.2)) :
    (∏ i, ((t i).valued values).tensor (fun p => x (i,p))) =
      ∑ q : F.Hist a, ((specializedTerminal F save y hy pos a t q).valued values).tensor x := by
  let leaf := fun a => (view 0 a).pack.layout
  let tree := leavesEquiv k _ steps a
  let t' := flatInputs leaf steps a t
  refine (flat_input_value leaf values steps a t x).symm.trans ?_
  refine (sum_specializedReplay F save y hy pos values lookup steps le_rfl tree t' (nestedPorts bits k steps x)).trans ?_
  apply Finset.sum_congr rfl
  intro q _
  exact specializedExecuted_tensor F save y hy pos steps le_rfl tree t' q values (nestedPorts bits k steps x)

end Diagonal.CellEntries.Replay

end BorderVNP
end Computability
end OAI
