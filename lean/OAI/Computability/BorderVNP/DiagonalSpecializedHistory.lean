import OAI.Computability.BorderVNP.DiagonalPublicReplay
import OAI.Computability.BorderVNP.DiagonalSpecializedStep

/-! # Exact finite-field expansion over fixed reference-field histories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.Replay

open Crossing Shortening Adaptive Packing PlacedStep
open scoped BigOperators Classical

set_option maxHeartbeats 2000000

universe u

variable {k steps exp D m : ℕ} [NeZero D] {I P Team Param Gadget K E : Type}
    [Fintype I] [Fintype Team] [Fintype Param] [Field K] [Field E]
    {bits : P → ℕ} {A : ℕ → Type u} {B : Fin steps → Type} [∀ i, Fintype (B i)]
    {depth : ℕ → ℕ} {e : PaidIdentity K D m}
    {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}

/-- Enumerate the ordered batch of original team positions at this stage. -/
local instance specializedReplayPortFinite {n : ℕ} : Fintype (Port k Team n) := batchFinite k Team n

variable (F : Adaptive.Program (B := B) e view) (save : ProgramStorage F) (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget)

/-- Reuse the actual successor storage bijection from the reference program
after applying its joint profile with the specialized crossing tables. -/
noncomputable def specializedMove :
    PublicTransition F.system (fun n a => (view n a).pack.layout) Team Param Gadget exp :=
  fun n hn c tags q =>
    (save ⟨n,hn⟩ c q).tracked (Tracked.specializedOutput e y hy pos (F.step ⟨n,hn⟩ c) tags q)

/-- All local sums are exact on the very same saved layouts and histograms. -/
theorem specializedMove_exact (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i) :
    PublicTransition.Exact F.system (fun n a => (view n a).pack.layout)
      (specializedMove (Team := Team) (Param := Param) (exp := exp) F save y hy pos) values := by
  intro n hn c tags x
  let i : Fin steps := ⟨n,hn⟩
  refine (Tracked.sum_specializedOutput e y hy pos (F.step i c) tags values lookup x).trans ?_
  apply Finset.sum_congr _ (fun q _ => (Storage.tracked_tensor (save i c q)
    (Tracked.specializedOutput e y hy pos (F.step i c) tags q) values x).symm)
  exact congrArg (@Fintype.elems ((F.step i c).Index e)) (Subsingleton.elim _ _)

/-- The tagged table for a complete history selected over the reference field. -/
noncomputable def specializedReplay (n : ℕ) (hn : n ≤ steps) (a : Leaves k (A 0) n)
    (t : Inputs (fun a => (view 0 a).pack.layout) Team Param Gadget exp n a)
    (q : (F.system.histories n hn a).Index) :
    Tracked (Port k Team n) Param Gadget exp (view n (state F n hn a q)).pack.layout :=
  publicReplay F.system _ (specializedMove F save y hy pos) n hn a t q

/-- Specialization may be chosen after the public program. The reference-field
geometric estimates and the finite-field tensor identity have identical
indices and preserve every private assignment and original power word. -/
theorem sum_specializedReplay (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (n : ℕ) (hn : n ≤ steps) (a : Leaves k (A 0) n)
    (t : Inputs (fun a => (view 0 a).pack.layout) Team Param Gadget exp n a)
    (x : Ports (width bits k n)) :
    inputValue (fun a => (view 0 a).pack.layout) values n a t x =
      ∑ q, ((specializedReplay F save y hy pos n hn a t q).valued values).tensor x :=
  sum_publicReplay F.system _ _ values (specializedMove_exact F save y hy pos values lookup) n hn a t x

end Diagonal.CellEntries.Replay

end BorderVNP
end Computability
end OAI
