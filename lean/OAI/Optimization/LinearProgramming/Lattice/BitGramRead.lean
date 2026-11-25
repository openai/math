import OAI.Optimization.LinearProgramming.Lattice.BitTables
import OAI.Optimization.LinearProgramming.Lattice.BitArithmetic

/-! Read the three neighboring Gram determinants and the pivot coefficient used by
the Lovász test and adjacent swap. All four reads use the framed input tables. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

def gramQuad (k : ℕ) (s : State) : GramQuad :=
  ((readAt 0 s.2.2 (k-1), readAt 0 s.2.2 k),
    (readAt 0 s.2.2 (k+1), entryAt s.2.1 k (k-1)))

noncomputable def gramQuadP : Procedure cursorCode gramQuadCode (fun x : Cursor => gramQuad x.1 x.2) := by
  let k := first Nat.bits stateCode
  let s := second Nat.bits stateCode
  let ds := gramsP.comp s
  let p := predIndexP k
  let a := getAtP 0 ds p
  let b := getAtP 0 ds k
  let c := getAtP 0 ds (succIndexP k)
  let v := tableEntryP (nuMatrixP.comp s) k p
  exact (a.pair b).pair (c.pair v)

theorem gramQuad_packState {n m : ℕ} (s : Hex.Internal.LLLState n m) (k : Fin n) (hk : 0 < k.val) :
    let prev := Hex.GramSchmidt.prevRow k hk
    gramQuad k.val (packState s) =
      ((s.d.get ⟨prev.val, by omega⟩, s.d.get ⟨k.val, by omega⟩),
        (s.d.get ⟨k.val+1, by omega⟩,(s.ν.getRow k).get prev)) := by
  dsimp [gramQuad, packState]
  rw [readAt_packVector 0 s.d ⟨k.val-1, by omega⟩,readAt_packVector 0 s.d ⟨k.val, by omega⟩,
    readAt_packVector 0 s.d ⟨k.val+1, by omega⟩,entryAt_packMatrix s.ν k ⟨k.val-1,by omega⟩]
  rfl

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
