import OAI.ThreeFlat.Diagonal.NavigationArchiveFields
import OAI.ThreeFlat.Diagonal.ProgramDirectory

namespace OAI
/-! # Positive successor counts through the physical compressor program -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open NavigationDirectory PhysicalStage
variable {F : Type} [Field F]

/-- Native physical runs have a live successor row whenever the initial base is inhabited. -/
theorem successors_live {s : ℕ} (P : PhysicalStage.Program F s) (rem v : ℕ) (pos : 0<v) :
    ∀ op∈P.directory rem v,0<successors op := by
  induction P generalizing v with
  | done => simp [PhysicalStage.Program.directory]
  | shrink s t G small tail ih =>
    intro op hop
    rcases List.mem_cons.mp hop with rfl|h
    · change 0 < (v*2^(CompressorPacking.tagBits (2^s)))*2^(tail.charge+rem)
      positivity
    · exact ih _ (by positivity) op h
  | refresh s t h pad g γ tariff G hm hh sym rows zero conn degree tail ih =>
    intro op hop
    rcases List.mem_cons.mp hop with rfl|h
    · change 0 < (v*2^s)*2^(tail.charge+rem)
      positivity
    · exact ih _ (by positivity) op h

end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
