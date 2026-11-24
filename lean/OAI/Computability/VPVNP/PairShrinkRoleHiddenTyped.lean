import OAI.Computability.VPVNP.PairShrinkRoleHidden
import OAI.Computability.VPVNP.PairShrinkHiddenTypedDecode

/-!
# The hidden-stage reader on the actual owned half-wires

The native hidden directory keeps the same IDs and field lengths for every
assignment at a fixed vertex. Reading an arbitrary full tape prefix recovers
a unique assignment on its owned fields. Reading a specified assignment's
encoding returns those exact rows and preserves an arbitrary suffix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM Compression Compression.ShrinkMotif NetworkKernel CompressorRecords
open ShrinkHiddenSlots ShrinkHiddenGuess

variable {a g w endAddr : ℕ} (X : State a (packingLaneBits a g)) (layout : Bool)
  (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)
  (v : (X.Base × BitWord (Shrink.J a)) × BitWord g)

local notation "Hidden" => Placed (X.packingData.shrinkInternalOwner layout)
  (internalLabel widths layout) v
local notation "Rows" => ShrinkHiddenSlots.rows X layout widths v

private theorem hiddenLength_eq (a b : Hidden) : (stream (Rows a)).length =
    (stream (Rows b)).length := by
  simp only [stream, List.flatMap_def, ShrinkHiddenSlots.rows, List.map_ofFn,
    List.length_flatten, List.length_ofFn, Function.comp_def]

variable (arg : Args w) (mem : Memory w)
  (seed : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel widths layout) v)

/-- All accepted raw rows at a selected vertex determine one and only one
typed hidden assignment on the consumed prefix. -/
theorem hiddenReader_typed {node : Word w} {saved : DFS.Scratch w endAddr}
    {bs tail : List Bool} {out : Outcome w endAddr (List Row)}
    (hit : hiddenReader arg mem (Rows seed) node saved bs = some (out, tail)) :
    ∃! h : Hidden, out.value = Rows h ∧ bs = stream (Rows h) ++ tail := by
  unfold hiddenReader at hit
  split at hit
  · rename_i enough
    obtain ⟨h, decoded, part⟩ := decode_rows X layout widths v seed bs enough
    rw [decoded] at hit
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hit)
    refine ⟨h, ⟨rfl,part⟩, ?_⟩
    intro h' ok
    exact (rows_prefix_unique X layout widths v h' h _ _ (ok.2.symm.trans part)).1
  · contradiction

/-- Starting on a genuine hidden assignment and any continuation returns the
precise dense-ID rows of that assignment, together with their native stores. -/
theorem hiddenReader_encoded (h : Hidden) (node : Word w) (saved : DFS.Scratch w endAddr)
    (tail : List Bool) :
    ∃ out, hiddenReader arg mem (Rows seed) node saved (stream (Rows h) ++ tail) =
      some (out, tail) ∧
      out.value = Rows h := by
  let bs := stream (Rows h) ++ tail
  have enough : (stream (Rows seed)).length ≤ bs.length := by
    rw [hiddenLength_eq X layout widths v seed h]
    simp [bs]
  obtain ⟨z, decoded, part⟩ := decode_rows X layout widths v seed bs enough
  obtain ⟨hz, rest⟩ := rows_prefix_unique X layout widths v h z tail _ part
  subst z
  unfold hiddenReader
  rw [ite_eq_left enough, decoded, ← rest]
  exact ⟨_, rfl, rfl⟩

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
