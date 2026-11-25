import OAI.Hierarchy.HistorySelectedSeedWords
import OAI.ThreeFlat.RAM.HistoryCommandParameter
import OAI.ThreeFlat.RAM.HistoryReadyTape

namespace OAI
/-! # Native procedure of a reached receiver leaf -/

namespace Hierarchy.HistorySelectedSeed
open ThreeFlat RAM RAM.DescriptorExpr RAM.HistoryInitialSeed
open RAM.PhysicalProcedure RAM.HistoryReadyTape Computability.VPVNP.BurstRAM
open scoped Fin.CommRing
noncomputable section
variable {k W : ℕ}

def seedData (A : Layout) (pub : Fin k → Word W) : Fin (k+1) → Word W :=
  Fin.lastCases (A.ctrl : Word W) pub

def liftDecoder (dec : Term W k 4) : Term W (k+1) 4 :=
  HistoryCommandParameter.replace (fun i : Fin k => .parameter i.castSucc) dec

def procedure (A : Layout) (dec : Term W k 4) (pub : Fin k → Word W) : Procedure W :=
  (seed W A).seq (execute (words A (liftDecoder dec)) (Fin.last k) (seedData A pub))

end
end Hierarchy.HistorySelectedSeed

end OAI
