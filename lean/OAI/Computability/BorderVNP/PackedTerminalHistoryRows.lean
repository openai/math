import OAI.Computability.BorderVNP.PackedHistoryNormalizedBoundary
import OAI.Computability.BorderVNP.PackedHistoryNormalizedMachine
import OAI.Computability.BorderVNP.PackedTerminalPhysical

/-! # The route directory of the actual accepted outer history

The transcript checked by the public geometry circuit fixes the stored
terminal state. Its flattened network, sparse row embeddings and reduced
site origins are therefore read at those very wires.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicCapacity Shortening.PreparedBins
open BorderVNP.Epoch BorderVNP.Epoch.Round Packing VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {P : Type} [Fintype P] {bits : P → ℕ} {start T w : ℕ} {shape : ℕ → Shape} {budget : ℕ → ℕ}
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {iw : ℕ → ℕ → ℕ}
    {deep : S.floor+1+S.drop*T ≤ start}

local notation "Bgood" => Boundary.Good (S:=S) (start:=start) (shape:=shape) (w:=w) (bits:=bits) budget
local notation "G" => Guess S start iw
variable (M : Machine deep (Boundary.Good (S:=S) (start:=start) (shape:=shape) (w:=w) (bits:=bits) budget) V iw) (leaf : Admissible (Boundary.Good (S:=S) (start:=start) (shape:=shape) (w:=w) (bits:=bits) budget) 0)
    {σ : Type} [Fintype σ] (bottom : Frame σ (Boundary.Pins S start shape w 0))
    (x : σ → Bool) (base : bottom.eval x = leaf.val.words)
local notation "leaves" => repeatLeaf (fan S) leaf T
local notation "tree" => repeatLeaf (fan S) bottom T

include base in
/-- The exact output and guard of the outer compiled circuit at an arbitrary
assigned profile. Its finite index is the true native dependent history. -/
theorem checked_words (g : Slot (fan S) G T → Bool) :
    (flag M.steps T le_rfl tree x g = true ↔ ∃ q, g = encode M.codec T le_rfl leaves q) ∧
    ∀ q, g = encode M.codec T le_rfl leaves q →
      output M.steps T le_rfl tree x g = (state (S:=M.system) T le_rfl leaves q).val.words := by
  have rep (n : ℕ) : LeafState (represents (good := Bgood)) x n (repeatLeaf (fan S) leaf n)
      (repeatLeaf (fan S) bottom n) := by
    induction n with
    | zero => exact base
    | succ n ih => exact fun _ => ih
  exact semantics M.codec (represents (good := Bgood)) M.steps M.correct T le_rfl leaves tree x (rep T) g

include base in
/-- Reading the flattened physical directory at the geometry-circuit output
for this native histogram, including true zero-width edges and empty rows. -/
theorem checked_routes (q : (M.system.histories T le_rfl leaves).Index) (g : Slot (fan S) G T → Bool)
    (selected : g = encode M.codec T le_rfl leaves q) :
    let s := (state (S:=M.system) T le_rfl leaves q).val
    flag M.steps T le_rfl tree x g = true ∧
      RouteRows.Ready (factorEnum D) (flattenPack T s.pack) s.route.flatten s.rows.flatten s.dummy
        (output M.steps T le_rfl tree x g) := by
  intro s
  have check := checked_words M leaf bottom x base g
  refine ⟨check.1.mpr ⟨q,selected⟩,?_⟩
  rw [check.2 q selected]
  exact (state (S:=M.system) T le_rfl leaves q).property.ready.flatten

end PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

end BorderVNP
end Computability
end OAI
