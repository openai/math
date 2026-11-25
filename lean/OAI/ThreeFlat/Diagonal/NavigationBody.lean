import OAI.ThreeFlat.Diagonal.NavigationCountedLoop
import OAI.ThreeFlat.Diagonal.NavigationScalar
import OAI.ThreeFlat.RAM.CountedProcedure
import OAI.ThreeFlat.Diagonal.NavigationPass
import OAI.ThreeFlat.Diagonal.PhysicalBlockSchedule
import OAI.ThreeFlat.RAM.CompressorIteration
import OAI.ThreeFlat.RAM.PackedStageArchive

namespace OAI
/-! # Single copy of all physical pass instructions, repeated by an external memory counter -/

namespace ThreeFlat.Diagonal.NavigationPass

open scoped Fin.CommRing

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.ContinuationLink PhysicalStage
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {W : ℕ}

/-- The finite native schedule follows exactly the order used by `PhysicalStage.Program.run`. -/
def compile (current : Word W) (K : ℕ) : {s : ℕ} → Program F s → Procedure W
  | _, .done _ => skip
  | _, .shrink s t T _ tail => (shrink current K s (2^t) T).seq (compile current K tail)
  | _, .refresh s _ h pad _ _ _ T _ _ sym rows loopless _ _ tail =>
    (refresh current K s h pad T sym rows loopless).seq (compile current K tail)

/-- This code has a fixed finite number of instructions independent of the repeated-block
count. The counter, directory, graphs and histogram are all physical external-memory data. -/
def repeated (current counter : Word W) (K : ℕ) (B : PhysicalStage.Block F) : Procedure W :=
  loop counter (compile current K (B.prefix (.done _)))

/-- A two-archive startup (static words, then all histogram words), two numerical pointer
seeds, and the counted block body. The caller provides only the eventual return location. -/
def forward (current counter : Word W) (K : ℕ) (B : PhysicalStage.Block F)
    (staticArchive histArchive : PackedStageArchive.Layout) (firstHeader blocks : ℕ) : Procedure W :=
  (PackedStageArchive.procedure staticArchive).seq
    ((PackedStageArchive.procedure histArchive).seq ((start current firstHeader).seq
      ((start counter blocks).seq (repeated current counter K B))))

end
end ThreeFlat.Diagonal.NavigationPass

end OAI
