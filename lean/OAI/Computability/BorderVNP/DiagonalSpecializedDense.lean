import OAI.Computability.BorderVNP.DiagonalPublicReplay
import OAI.Computability.BorderVNP.DiagonalSpecializedDenseStep
import OAI.Computability.BorderVNP.PackedHistoryDenseProgram

/-! # Specializing a full history on the true sorted physical layouts -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.DenseReplay

open Crossing Shortening Adaptive Packing PackedHistoryCircuit.Normalized
open scoped BigOperators Classical

set_option maxHeartbeats 2000000

variable {D m k exp : ℕ} [NeZero D] {I P : Type} [Fintype I]
    {bits : P → ℕ} {Team Param Gadget K E : Type} [Fintype Team] [Fintype Param]
    [Field K] [Field E]


variable {steps : ℕ} {A : ℕ → Type*} {Bin : Fin steps → Type} [∀ i, Fintype (Bin i)]
    {depth : ℕ → ℕ} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    {e : PaidIdentity K D m} (F : PackedHistoryCircuit.Normalized.Program (B := Bin) e view)

/-- Enumerate the ordered batch of original team positions at this stage. -/
local instance denseReplayPortFinite {n : ℕ} : Fintype (Port k Team n) := Replay.batchFinite k Team n

/-- Site, cable, external port and assignment bijections of the actual output save. -/
def Saved :=
  ∀ (i : Fin steps) (c : Fin k → A i.val) (q : (F.stage i c).Index e),
    Storage ((F.stage i c).result e q).pack.layout (view (i.val+1) (F.advance i c q)).pack.layout

variable (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget)
    (save : Saved F)

/-- Apply the allocator in its sorted input order and store its actual output. -/
noncomputable def move :
    Replay.PublicTransition F.system (fun n a => (view n a).pack.layout) Team Param Gadget exp :=
  fun n hn c tags q => (save ⟨n,hn⟩ c q).tracked (stageOutput (F.stage ⟨n,hn⟩ c) tags e y hy pos q)

/-- The public sorted program and the independently specialized scalar tables
compute the same expansion on the same public histogram indices. -/
theorem move_exact (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i) :
    Replay.PublicTransition.Exact F.system (fun n a => (view n a).pack.layout)
      (move (Team := Team) (Param := Param) (exp := exp) F y hy pos save) values := by
  intro n hn c tags x
  let i : Fin steps := ⟨n,hn⟩
  refine (stage_sum (F.stage i c) tags e y hy pos values lookup x).trans ?_
  apply Finset.sum_congr _ (fun q _ => (Storage.tracked_tensor (save i c q)
    (stageOutput (F.stage i c) tags e y hy pos q) values x).symm)
  exact congrArg (@Fintype.elems ((F.stage i c).Index e)) (Subsingleton.elim _ _)

end Diagonal.CellEntries.DenseReplay

end BorderVNP
end Computability
end OAI
