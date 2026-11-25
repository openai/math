import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepGeometry
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepRow

/-! # Numerical geometry and switch tables of an actual directed Fourier pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord.PermDirectory

open IntegerMultiplication Code SynchronizedLayers SynchronizedLayers.ScheduleProgram BoxFin

theorem switchTable_entry {k L : ℕ} (h : BoxShape.Valid k L (CoprimeBox.box k))
    [∀ i, NeZero (modulus (CoprimeBox.box k) i)] (dir : Bool)
    (s : Fin (directedPlan (dir,tally k)).length)
    (hp : (directedPlan (dir,tally k))[s.val].2.1 = kindCode .permutation)
    (b : Fin ((CoprimeBox.box k).length/4)) :
    (directory (dir,tally k,tally s.val))[b.val]? =
      some (tally (physicalWidth (box := CoprimeBox.box k) b),switchTable dir s.val b) := by
  obtain ⟨_,_,_,entry,_⟩ := directory_represents h dir s b hp
  simp only [switchTable,entry,Option.getD_some]

end ShortFourier.BatchWord.PermDirectory

namespace Benes.PackedBatchHeader

open IntegerMultiplication Code Controlled ShortFourier.BatchWord SynchronizedLayers SynchronizedLayers.ScheduleProgram BoxFin

/-- The emitted full header exposes both the true dimensions and the compiled
query plan of the very same per-block tables read by the permutation sweep. -/
theorem placedHeader_row {k L : ℕ} (hb : BoxShape.Valid k L (CoprimeBox.box k))
    [∀ i, NeZero (modulus (CoprimeBox.box k) i)] (D : ℕ) (dir : Bool)
    (s : Fin (directedPlan (dir,tally k)).length)
    (hp : (directedPlan (dir,tally k))[s.val].2.1 = kindCode .permutation) (side : Bool) (j β : ℕ) :
    let w := BoxFin.physicalWidth (box := CoprimeBox.box k)
    let sel := FieldDirectory.selectBlock k β j w
    let b := (FieldDirectory.activeBlocks k β j w).length
    let G := guardWidth k
    let B := payloadBits D k
    placedHeader (tally D,((dir,tally k,tally s.val),(side,tally j),tally β)) =
      ((tally k,tally (k-(2*((b+1)*G)+B)),tally (G-1),tally b,tally B),
        prepare (seed w (PermDirectory.switchTable dir s.val) sel side j k G B)) := by
  dsimp only
  rw [geometry_eq hb D dir (tally s.val) side j β]
  exact congrArg (Prod.mk _) (fullHeader_eq hb D dir (tally s.val) side j β
    (PermDirectory.switchTable dir s.val) (PermDirectory.switchTable_entry hb dir s hp))

end Benes.PackedBatchHeader

end NearSquareRoot
end Computability
end OAI
