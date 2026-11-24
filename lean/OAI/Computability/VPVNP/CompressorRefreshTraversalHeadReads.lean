import OAI.Computability.VPVNP.CompressorRefreshArgumentReads
import OAI.Computability.VPVNP.CompressorRefreshTraversalHeaders

/-!
# Header and singleton-row reads of the refresh role

The expressions that compute incidence and scratch heads read the published old and
new level headers. The child-node pointer uses exactly two cells of the preimage row.
All subsequent offset arithmetic on the level-plan operands introduces no probes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalHeaders

open BurstRAM PhaseRecipe Compression PairSimulation NewSlots
open scoped Fin.CommRing

variable {w : ℕ} (pub : Fin 5 → W w) (state : W w) (m : Memory w) (limit : ℕ)

/-- The child and parent argument addresses are readable, and the lane count, segment heads and
demand and term bases read only below the stated memory limit. -/
structure InputReads (I : OperandInputs.Input) : Prop where
  child : ArgumentAddress.Readable I.child limit pub state m
  parent : ArgumentAddress.Readable I.parent limit pub state m
  lanes : I.lanes.ReadsFrom (· < limit) pub state m
  offOut : I.offOut.ReadsFrom (· < limit) pub state m
  offIn : I.offIn.ReadsFrom (· < limit) pub state m
  widthOut : I.widthOut.ReadsFrom (· < limit) pub state m
  widthIn : I.widthIn.ReadsFrom (· < limit) pub state m
  demand : I.demandBase.ReadsFrom (· < limit) pub state m
  term : I.termBase.ReadsFrom (· < limit) pub state m

local notation "ok" => Expr.ReadsFrom (· < limit) pub state m

theorem input_reads (s : LevelRecipe.Shape) {oldHead newHead parent listHead child : ℕ}
    (stateWord : state.val = oldHead) (newWord : (pub 2).val = newHead)
    (parentWord : (pub 1).val = parent)
    (row : DFS.Row m parent listHead [word (bits := w) child])
    (oldBefore : oldHead + 60 < limit) (newBefore : newHead + 59 < limit)
    (parentBefore : parent < limit) (listBefore : listHead < limit) :
    InputReads pub state m limit (input s) := by
  have addBound (x : W w) (v : ℕ) : (x + (v : W w)).val ≤ x.val + v :=
    (Nat.mod_le ..).trans (Nat.add_le_add_left (Nat.mod_le ..) _)
  have old (j : ℕ) (hj : j ≤ 60) : ok (.header j) := by
    refine ⟨⟨trivial, trivial⟩, ?_⟩
    change (state + (j : W w)).val < limit
    apply (addBound ..).trans_lt; omega
  have curr (j : ℕ) (hj : j ≤ 59) : ok (current j) := by
    refine ⟨⟨trivial, trivial⟩, ?_⟩
    change (pub 2 + (j : W w)).val < limit
    apply (addBound ..).trans_lt; omega
  have childAt : ok traversal.child := by
    refine ⟨⟨trivial, parentWord ▸ parentBefore⟩, ?_⟩
    change (m (pub 1).val).val < limit
    rw [parentWord, row.2.2.1]
    exact (Nat.mod_le ..).trans_lt listBefore
  have ls : ok level.lanes := old 3 (by decide)
  have vs : ok level.vertices := old 0 (by decide)
  have st : ok level.start := old 60 le_rfl
  have seg : ok (LevelRecipe.segments s level) := ⟨⟨⟨vs, trivial⟩, ls⟩, trivial⟩
  have sc (j : Fin 8) : ok (LevelRecipe.scratch s level j) := by
    unfold LevelRecipe.scratch; split
    · trivial
    · exact ⟨st, trivial, seg⟩
  have dm : ok (LevelRecipe.demandStart s level) := ⟨st, trivial, seg⟩
  have tr : ok (LevelRecipe.termStart s level) := ⟨dm, ⟨vs, ls⟩, trivial⟩
  exact ⟨⟨old 17 (by decide), old 18 (by decide), childAt, trivial, old 58 (by decide), old 59
    (by decide)⟩,
    ⟨old 17 (by decide), old 18 (by decide), trivial, trivial, curr 58 (by decide), curr 59 le_rfl⟩,
    ls, sc 5, sc 6, sc 1, sc 7, dm, tr⟩

end CompressorRecords.PortRefresh.TraversalHeaders

end VPVNP
end Computability
end OAI
