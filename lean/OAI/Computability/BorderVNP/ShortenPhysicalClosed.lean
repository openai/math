import OAI.Computability.BorderVNP.ShortenPhysicalTree

/-!
# Direct physical storage of every prepared histogram

When a finite pattern is preserved by every measured output, the placed
pack itself is the successor state. Its full layout and every local table
are retained definitionally. This supplies the direct program used when
replaying the public interval choices on arbitrary coefficient tables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Adaptive.Program

open Crossing

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I]
    {bits : P → ℕ} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}

/-- Subtype state of actual placed packs whose relative and resource
invariants have been established at this stage. -/
abbrev Prepared (good : ∀ n, PlacedPack D (Port k P n) (width bits k n) K I (depth n) → Prop)
    (n : ℕ) := {p // good n p}

/-- Build the physical program from the closure of the chosen stage
preparations under actual histogram successors. There is no reindexing
in this constructor. -/
noncomputable def ofClosed (e : PaidIdentity K D m)
    (good : ∀ n, PlacedPack D (Port k P n) (width bits k n) K I (depth n) → Prop)
    (step : ∀ (i : Fin b) (c : Fin k → Prepared good i.val),
      PlacedStep m (B i) (depth (i.val+1)) (fun j => (c j).val))
    (closed : ∀ (i : Fin b) (c : Fin k → Prepared good i.val) (q : (step i c).Index e),
      good (i.val+1) ((step i c).result e q)) :
    Program (B := B) e (fun n (p : Prepared good n) => p.val) where
  step := step
  advance i c q := ⟨(step i c).result e q,closed i c q⟩
  tensor _ _ _ _ := rfl
  length _ _ _ := rfl
  concentration _ _ _ := rfl

end Shortening.Adaptive.Program

end BorderVNP
end Computability
end OAI
