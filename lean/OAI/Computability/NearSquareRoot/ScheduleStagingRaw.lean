import OAI.Computability.NearSquareRoot.ScheduleStagingPhases
import OAI.Computability.NearSquareRoot.ScheduleChunkWhole

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingPhases

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open ChunkLoop ChunkTask

/-- A single fixed controller stages literal digit pairs and emits literal product bits. -/
theorem raw_controllers :
    ∃ (d : ChunkControl.Driver) (C : ℕ), ∀ (m : Operands → Word) (p : Input),
      (answer m p).length = 2*p.n →
      Calls d.load d.test d.prepare d.collect d.emit C m p ((answer m p).map Ltr.bit) := by
  obtain ⟨d,C,ctl⟩ := ChunkWhole.raw_driver
  exact ⟨⟨d.load,d.test,d.prepare.join (unparsePair.rename Nat.succ),
    (parseWord.rename Nat.succ).join d.collect,d.emit⟩,C+32,fun m p h => adapt (ctl m p h)⟩

end StagingPhases

end NearSquareRoot
end Computability
end OAI
